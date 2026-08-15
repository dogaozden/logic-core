//! The serve filter: the difficulty gate where the whole generator pipeline converges.
//!
//! `analyze_for_serving` runs a candidate theorem through cheese checks (T9), the
//! greedy prover (T7), and the bounded-optimal prover (T8), in a fixed evaluation
//! order, and either rejects it with a specific `ServeRejection` or accepts it with
//! a computed `score`. The order is a CONTRACT, not an implementation detail: T11's
//! shame suite asserts the exact rejection reason for known-bad theorems (Round 9's
//! grind, Round 10's vacuous disjunct, Round 11's disguised identity, Round 3's
//! excluded middle), so a theorem that could be rejected for more than one reason
//! must always report the FIRST reason in this order:
//!
//! 1. `TautologousDisjunct` / 2. `SubformulaDecoy` / 3. `DisguisedIdentity` — cheap
//!    cheese checks (T9), never even touching a prover.
//! 4. `NotGreedyProvable` / 5. `Hallway` — the greedy ("philosopher") prover (T7):
//!    no proof found, or a proof found with zero real choice points anywhere.
//! 6. `OptimalUnknown` — the bounded-optimal ("lawyer") prover (T8) either exhausted
//!    its node cap, ran out of depth budget, or found a proof it can't certify
//!    minimal. Tournament serving must never hand out a theorem whose difficulty
//!    wasn't actually measured.
//! 7. `TooShort` / 8. `InsufficientDivergence` / 9. `NoUnlock` — the theorem has a
//!    certified-minimal optimal proof, but it's too short outright, too close to
//!    what the greedy philosopher already found unassisted, or doesn't require any
//!    rule the philosopher wouldn't reach for on its own.
//!
//! Anything that survives all nine gates passes with `rejection: None` and a
//! computed `score`.
//!
//! ## Regime-classifier duty (ratified 2026-08-15, ruling #3 on this task)
//!
//! An `OptimalUnknown` rejection means "we can't certify this theorem's difficulty,"
//! not "no proof exists." When the optimal search DID find a proof but couldn't
//! certify it minimal (`Proved { minimal_proven: false, .. }`), that proof's length
//! still gets recorded in `best_found_lines` — never discarded. Tournament serving
//! rejects the theorem, but that uncertified length is the "par" a future proof-golf
//! feature would be built from. `optimal_lines` stays `None` in this case; it means
//! "certified minimal," which this length explicitly is not.
//!
//! ## Why the optimal-dependent reasons are a separate pure function
//!
//! Reasons 6-9 all depend on the outcome of `optimal_prove`, which is the expensive
//! stage (R10/R11-sized formulas take 6-32s at default config — see T8/T9's
//! reports). `analyze_for_serving` therefore short-circuits BEFORE ever calling it:
//! cheese and greedy both run first, with early returns, exactly like reasons 1-5
//! are cheap enough to exercise end-to-end with tiny real theorems in this file's
//! tests. Reasons 6-9, by contrast, are pulled into `decide_optimal_stage` — a pure
//! function of an already-computed `OptimalOutcome` plus the greedy facts the
//! earlier stages established. It never calls a prover itself, so its tests
//! hand-construct `OptimalOutcome::Exhausted`, `NotProvedWithinBounds`, and
//! `Proved { minimal_proven: false }` directly — giving full coverage of reasons
//! 6-9, including the regime-classifier duty above, without paying for (or
//! depending on the timing/tractability of) a real bounded search.

use std::collections::HashSet;

use serde::Serialize;

use crate::models::Theorem;

use super::cheese::cheese_check;
use super::prover::{greedy_prove, optimal_prove, OptimalConfig, OptimalOutcome};

#[derive(Serialize, Debug, PartialEq)]
pub enum ServeRejection {
    TautologousDisjunct,
    SubformulaDecoy,
    DisguisedIdentity { distance: usize },
    NotGreedyProvable,
    OptimalUnknown, // node cap / minimality unproven — never serve unmeasured theorems
    Hallway,        // greedy single-path (F1)
    TooShort { optimal: usize },
    InsufficientDivergence { greedy: usize, optimal: usize },
    NoUnlock,
}

#[derive(Serialize, Debug)]
pub struct ServeAnalysis {
    pub greedy_lines: Option<usize>,
    pub optimal_lines: Option<usize>, // set ONLY when certified minimal
    pub best_found_lines: Option<usize>, // best proof found even when uncertified — the future golf "par"
    pub optimal_certified: bool,
    pub divergence: Option<i64>,
    pub unlock_rules: Vec<String>,
    pub branch_points: usize,
    pub score: u64, // divergence × (1 + min(branch_points, 3)) — route-count proxy
    pub rejection: Option<ServeRejection>,
}

impl ServeAnalysis {
    /// Every field at its "nothing evaluated yet" default. Each pipeline stage
    /// below starts from this and fills in only what it actually computed before
    /// short-circuiting — a `TautologousDisjunct` rejection, for instance, never
    /// touches `greedy_lines` because the greedy prover never ran.
    fn empty() -> Self {
        ServeAnalysis {
            greedy_lines: None,
            optimal_lines: None,
            best_found_lines: None,
            optimal_certified: false,
            divergence: None,
            unlock_rules: Vec::new(),
            branch_points: 0,
            score: 0,
            rejection: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ServeConfig {
    pub min_divergence: i64,
    pub max_identity_distance: usize,
    pub min_optimal_lines: usize,
    pub greedy_max_lines: usize,
    pub optimal: OptimalConfig,
}

impl Default for ServeConfig {
    fn default() -> Self {
        ServeConfig {
            min_divergence: 3,
            max_identity_distance: 3,
            min_optimal_lines: 5,
            greedy_max_lines: 40,
            optimal: OptimalConfig::default(),
        }
    }
}

/// Run `theorem` through the nine-reason ordered pipeline documented at module
/// level, stopping at the first reason that rejects it. Never calls the expensive
/// `optimal_prove` unless the theorem already survived every cheaper gate.
pub fn analyze_for_serving(theorem: &Theorem, cfg: &ServeConfig) -> ServeAnalysis {
    let mut analysis = ServeAnalysis::empty();

    // 1-3: cheese (T9) — cheap, pre-prover rejections.
    let cheese = cheese_check(&theorem.premises, &theorem.conclusion, cfg.max_identity_distance);
    if cheese.tautologous_disjunct.is_some() {
        analysis.rejection = Some(ServeRejection::TautologousDisjunct);
        return analysis;
    }
    if cheese.subformula_decoy.is_some() {
        analysis.rejection = Some(ServeRejection::SubformulaDecoy);
        return analysis;
    }
    if let Some(distance) = cheese.identity_rewrite_distance {
        analysis.rejection = Some(ServeRejection::DisguisedIdentity { distance });
        return analysis;
    }

    // 4-5: the greedy ("philosopher") prover (T7).
    let greedy = greedy_prove(&theorem.premises, &theorem.conclusion, cfg.greedy_max_lines);
    analysis.branch_points = greedy.branch_points;
    let Some(greedy_proof) = greedy.proof else {
        analysis.rejection = Some(ServeRejection::NotGreedyProvable);
        return analysis;
    };
    analysis.greedy_lines = Some(greedy_proof.line_count);
    if greedy.single_path {
        analysis.rejection = Some(ServeRejection::Hallway);
        return analysis;
    }

    // 6-9: the bounded-optimal ("lawyer") prover (T8), decided by the pure
    // function below so it stays independently unit-testable.
    let greedy_rules = greedy_proof.rules_used();
    let optimal = optimal_prove(&theorem.premises, &theorem.conclusion, &cfg.optimal);
    decide_optimal_stage(analysis, greedy_proof.line_count, &greedy_rules, optimal, cfg)
}

/// Reasons 6-9 (`OptimalUnknown` / `TooShort` / `InsufficientDivergence` /
/// `NoUnlock`) plus the passing score — everything that depends on the optimal
/// search's result. See the module docs for why this is split out as a pure
/// function of an already-computed `OptimalOutcome`.
fn decide_optimal_stage(
    mut analysis: ServeAnalysis,
    greedy_lines: usize,
    greedy_rules: &HashSet<String>,
    optimal: OptimalOutcome,
    cfg: &ServeConfig,
) -> ServeAnalysis {
    let proof = match optimal {
        // 6: honest "unknown" — never serve a theorem whose difficulty wasn't
        // actually measured.
        OptimalOutcome::Exhausted | OptimalOutcome::NotProvedWithinBounds => {
            analysis.rejection = Some(ServeRejection::OptimalUnknown);
            return analysis;
        }
        // 6, regime-classifier duty: a real proof was found but can't be
        // certified minimal. Still rejected as OptimalUnknown, but the length
        // is real information — record it as the uncertified "par" rather than
        // discarding it. optimal_lines stays None: that field means certified.
        OptimalOutcome::Proved { proof, minimal_proven: false } => {
            analysis.best_found_lines = Some(proof.line_count);
            analysis.rejection = Some(ServeRejection::OptimalUnknown);
            return analysis;
        }
        OptimalOutcome::Proved { proof, minimal_proven: true } => proof,
    };

    let optimal_lines = proof.line_count;
    analysis.optimal_lines = Some(optimal_lines);
    analysis.best_found_lines = Some(optimal_lines);
    analysis.optimal_certified = true;
    let divergence = greedy_lines as i64 - optimal_lines as i64;
    analysis.divergence = Some(divergence);

    // 7: certified-minimal but trivially short outright.
    if optimal_lines < cfg.min_optimal_lines {
        analysis.rejection = Some(ServeRejection::TooShort { optimal: optimal_lines });
        return analysis;
    }

    // 8: not enough daylight between the philosopher's grind and the true minimum.
    if divergence < cfg.min_divergence {
        analysis.rejection = Some(ServeRejection::InsufficientDivergence {
            greedy: greedy_lines,
            optimal: optimal_lines,
        });
        return analysis;
    }

    // 9: does the optimal proof require something the greedy philosopher
    // wouldn't reach for on its own? Dist/Exp/CD are never in greedy's mechanical
    // repertoire; IP only counts if greedy didn't already have access to it too.
    let optimal_rules = proof.rules_used();
    const UNLOCK_RULES: [&str; 3] = ["Dist", "Exp", "CD"];
    let mut unlock_rules: Vec<String> =
        optimal_rules.iter().filter(|r| UNLOCK_RULES.contains(&r.as_str())).cloned().collect();
    if optimal_rules.contains("IP") && !greedy_rules.contains("IP") {
        unlock_rules.push("IP".to_string());
    }
    // rules_used() is a HashSet — sort for deterministic output.
    unlock_rules.sort();
    analysis.unlock_rules = unlock_rules;

    if analysis.unlock_rules.is_empty() {
        analysis.rejection = Some(ServeRejection::NoUnlock);
        return analysis;
    }

    // Pass: route-count proxy, capped multiplier on branch points.
    analysis.score = divergence as u64 * (1 + analysis.branch_points.min(3) as u64);
    analysis
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{Difficulty, Formula, Theorem};
    use crate::services::prover::{FoundProof, ProofStep};

    fn f(s: &str) -> Formula {
        Formula::parse(s).unwrap()
    }

    fn theorem(premises: &[&str], conclusion: &str) -> Theorem {
        Theorem::new(
            premises.iter().map(|p| f(p)).collect(),
            f(conclusion),
            Difficulty::Easy,
            None,
            None,
        )
    }

    fn serve(premises: &[&str], conclusion: &str) -> ServeAnalysis {
        analyze_for_serving(&theorem(premises, conclusion), &ServeConfig::default())
    }

    fn greedy_stage(lines: usize, branch_points: usize) -> ServeAnalysis {
        ServeAnalysis { greedy_lines: Some(lines), branch_points, ..ServeAnalysis::empty() }
    }

    fn mock_proof(line_count: usize, rules: &[&str]) -> FoundProof {
        FoundProof {
            line_count,
            steps: rules
                .iter()
                .map(|r| ProofStep { formula: Formula::Atom("X".to_string()), rule: r.to_string(), cited: vec![] })
                .collect(),
        }
    }

    // ── Config sanity ──────────────────────────────────────────────────────

    #[test]
    fn default_config_matches_spec() {
        let cfg = ServeConfig::default();
        assert_eq!(cfg.min_divergence, 3);
        assert_eq!(cfg.max_identity_distance, 3);
        assert_eq!(cfg.min_optimal_lines, 5);
        assert_eq!(cfg.greedy_max_lines, 40);
    }

    // ── Reasons 1-5, 7: end-to-end via analyze_for_serving on tiny real theorems ──

    #[test]
    fn reason1_tautologous_disjunct_short_circuits_before_greedy() {
        // Consequent "Z v (Q > Q)" flattens to [Z, Q>Q]; Q>Q is independently a
        // tautology, so this fires cheese reason 1 before greedy/optimal ever run.
        let result = serve(&[], "Z > (Z v (Q > Q))");
        assert_eq!(result.rejection, Some(ServeRejection::TautologousDisjunct));
        assert_eq!(result.greedy_lines, None, "greedy must never run once cheese rejects");
        assert_eq!(result.score, 0);
    }

    #[test]
    fn reason2_subformula_decoy_short_circuits_before_greedy() {
        // Proven cheese.rs shape (decoy_fires_on_add_shortcut_shape): left conjunct
        // "P" alone already entails the consequent via Add, independent of Q/Z.
        let result = serve(&[], "(P . Q) > (P v Q v Z)");
        assert_eq!(result.rejection, Some(ServeRejection::SubformulaDecoy));
        assert_eq!(result.greedy_lines, None);
    }

    #[test]
    fn reason3_disguised_identity_short_circuits_before_greedy() {
        // "P > ~~P": P rewrites to ~~P in exactly 1 DoubleNegation step.
        let result = serve(&[], "P > ~~P");
        assert_eq!(result.rejection, Some(ServeRejection::DisguisedIdentity { distance: 1 }));
        assert_eq!(result.greedy_lines, None);
    }

    #[test]
    fn reason4_not_greedy_provable() {
        // Q does not entail P; cheese is clean (verified: no tautologous disjunct,
        // no decoy, no implication shape at all for identity).
        let result = serve(&["Q"], "P");
        assert_eq!(result.rejection, Some(ServeRejection::NotGreedyProvable));
        assert_eq!(result.greedy_lines, None, "no proof means no line count to report");
    }

    #[test]
    fn reason5_hallway_when_greedy_has_zero_choice() {
        // Classic MP, one premise pair, exactly one legal move at every step.
        let result = serve(&["P", "P > Q"], "Q");
        assert_eq!(result.rejection, Some(ServeRejection::Hallway));
        assert_eq!(result.greedy_lines, Some(1), "the hallway proof itself is still reported");
        assert_eq!(result.branch_points, 0);
    }

    #[test]
    fn reason7_too_short_via_real_certified_optimal() {
        // Simp finds P in 1 line, both greedy and (certified) optimal — cheap
        // enough to run for real rather than mocking.
        let result = serve(&["P . Q"], "P");
        assert_eq!(result.rejection, Some(ServeRejection::TooShort { optimal: 1 }));
        assert_eq!(result.greedy_lines, Some(1));
        assert_eq!(result.optimal_lines, Some(1), "certified length is populated even though rejected");
        assert_eq!(result.best_found_lines, Some(1));
        assert!(result.optimal_certified);
        assert_eq!(result.divergence, Some(0), "divergence is populated even when TooShort, not it, is the reason");
        assert_eq!(result.score, 0);
    }

    // ── Reasons 6, 8, 9 + pass: decide_optimal_stage, mocked OptimalOutcome ──
    // Hard to hand-construct reliably as real theorems (T10 brief); tested here as
    // the pure decision over an already-computed OptimalOutcome instead, per the
    // module docs.

    #[test]
    fn optimal_exhausted_is_optimal_unknown_with_no_best_found() {
        let result = decide_optimal_stage(greedy_stage(11, 2), 11, &HashSet::new(), OptimalOutcome::Exhausted, &ServeConfig::default());
        assert_eq!(result.rejection, Some(ServeRejection::OptimalUnknown));
        assert_eq!(result.best_found_lines, None);
        assert_eq!(result.optimal_lines, None);
        assert!(!result.optimal_certified);
        assert_eq!(result.score, 0);
        assert_eq!(result.greedy_lines, Some(11), "greedy facts survive from the earlier stage");
    }

    #[test]
    fn optimal_not_proved_within_bounds_is_optimal_unknown() {
        let result = decide_optimal_stage(
            greedy_stage(9, 0),
            9,
            &HashSet::new(),
            OptimalOutcome::NotProvedWithinBounds,
            &ServeConfig::default(),
        );
        assert_eq!(result.rejection, Some(ServeRejection::OptimalUnknown));
        assert_eq!(result.best_found_lines, None);
        assert_eq!(result.optimal_lines, None);
        assert!(!result.optimal_certified);
    }

    #[test]
    fn optimal_uncertified_proof_is_optimal_unknown_but_keeps_best_found_par() {
        // Regime-classifier duty (2026-08-15 ratification #3): a Proved-but-
        // uncertified optimal result still rejects as OptimalUnknown (tournament
        // serving can't use an unmeasured length), but the uncertified best MUST
        // survive into best_found_lines -- the future proof-golf "par". optimal_lines
        // must stay None: that field means "certified minimal," which this isn't.
        let proof = mock_proof(7, &["MP", "MP", "HS"]);
        let result = decide_optimal_stage(
            greedy_stage(11, 2),
            11,
            &HashSet::new(),
            OptimalOutcome::Proved { proof, minimal_proven: false },
            &ServeConfig::default(),
        );
        assert_eq!(result.rejection, Some(ServeRejection::OptimalUnknown));
        assert_eq!(result.best_found_lines, Some(7));
        assert_eq!(result.optimal_lines, None, "uncertified length must never leak into optimal_lines");
        assert!(!result.optimal_certified);
        assert_eq!(result.score, 0);
    }

    #[test]
    fn certified_optimal_below_min_is_too_short() {
        let proof = mock_proof(3, &["MP", "MP", "MP"]);
        let result = decide_optimal_stage(
            greedy_stage(9, 1),
            9,
            &HashSet::new(),
            OptimalOutcome::Proved { proof, minimal_proven: true },
            &ServeConfig::default(), // min_optimal_lines = 5
        );
        assert_eq!(result.rejection, Some(ServeRejection::TooShort { optimal: 3 }));
        assert_eq!(result.optimal_lines, Some(3));
        assert_eq!(result.best_found_lines, Some(3));
        assert!(result.optimal_certified);
        assert_eq!(result.divergence, Some(6), "divergence is populated even though TooShort is the reason");
        assert_eq!(result.score, 0);
    }

    #[test]
    fn low_divergence_is_insufficient_divergence() {
        // optimal=5 clears min_optimal_lines(5), but divergence=6-5=1 < min_divergence(3).
        let proof = mock_proof(5, &["MP", "MP", "MP", "MP", "MP"]);
        let result = decide_optimal_stage(
            greedy_stage(6, 1),
            6,
            &HashSet::new(),
            OptimalOutcome::Proved { proof, minimal_proven: true },
            &ServeConfig::default(),
        );
        assert_eq!(result.rejection, Some(ServeRejection::InsufficientDivergence { greedy: 6, optimal: 5 }));
        assert_eq!(result.divergence, Some(1));
        assert_eq!(result.score, 0);
    }

    #[test]
    fn no_unlock_rules_and_ip_used_by_both_is_no_unlock() {
        // divergence = 10-5=5 >= 3, optimal clears min_optimal_lines, but the
        // proof's rules are all "plain" -- no Dist/Exp/CD -- and IP appears in
        // both proofs, so it doesn't count as an unlock either.
        let proof = mock_proof(5, &["MP", "HS", "IP"]);
        let mut greedy_rules = HashSet::new();
        greedy_rules.insert("IP".to_string());
        let result = decide_optimal_stage(
            greedy_stage(10, 2),
            10,
            &greedy_rules,
            OptimalOutcome::Proved { proof, minimal_proven: true },
            &ServeConfig::default(),
        );
        assert_eq!(result.rejection, Some(ServeRejection::NoUnlock));
        assert!(result.unlock_rules.is_empty());
        assert_eq!(result.score, 0);
    }

    #[test]
    fn dist_in_optimal_proof_unlocks_and_scores() {
        let proof = mock_proof(5, &["MP", "Dist", "HS"]);
        let result = decide_optimal_stage(
            greedy_stage(10, 2),
            10,
            &HashSet::new(),
            OptimalOutcome::Proved { proof, minimal_proven: true },
            &ServeConfig::default(),
        );
        assert_eq!(result.rejection, None);
        assert_eq!(result.unlock_rules, vec!["Dist".to_string()]);
        // score = divergence(5) * (1 + min(branch_points=2, 3)) = 5 * 3 = 15
        assert_eq!(result.score, 15);
    }

    #[test]
    fn cd_in_optimal_proof_unlocks() {
        let proof = mock_proof(6, &["CD"]);
        let result = decide_optimal_stage(
            greedy_stage(11, 0),
            11,
            &HashSet::new(),
            OptimalOutcome::Proved { proof, minimal_proven: true },
            &ServeConfig::default(),
        );
        assert_eq!(result.rejection, None);
        assert_eq!(result.unlock_rules, vec!["CD".to_string()]);
    }

    #[test]
    fn ip_used_only_by_optimal_unlocks() {
        let proof = mock_proof(5, &["MP", "IP"]);
        let result = decide_optimal_stage(
            greedy_stage(10, 0),
            10,
            &HashSet::new(), // greedy never used IP
            OptimalOutcome::Proved { proof, minimal_proven: true },
            &ServeConfig::default(),
        );
        assert_eq!(result.rejection, None);
        assert_eq!(result.unlock_rules, vec!["IP".to_string()]);
        // score = divergence(5) * (1 + min(0,3)) = 5 * 1 = 5
        assert_eq!(result.score, 5);
    }

    #[test]
    fn score_multiplier_caps_branch_points_at_three() {
        let proof = mock_proof(5, &["Exp"]);
        let result = decide_optimal_stage(
            greedy_stage(10, 7), // branch_points well above the cap
            10,
            &HashSet::new(),
            OptimalOutcome::Proved { proof, minimal_proven: true },
            &ServeConfig::default(),
        );
        assert_eq!(result.rejection, None);
        // score = divergence(5) * (1 + min(7,3)) = 5 * 4 = 20
        assert_eq!(result.score, 20);
    }

    #[test]
    fn multiple_unlock_rules_are_sorted_for_determinism() {
        // rules_used() is a HashSet -- iteration order isn't guaranteed, so
        // unlock_rules must be sorted or this assertion would be flaky.
        let proof = mock_proof(6, &["Dist", "CD", "MP"]);
        let result = decide_optimal_stage(
            greedy_stage(11, 1),
            11,
            &HashSet::new(),
            OptimalOutcome::Proved { proof, minimal_proven: true },
            &ServeConfig::default(),
        );
        assert_eq!(result.unlock_rules, vec!["CD".to_string(), "Dist".to_string()]);
    }
}
