//! Cheese predicates: cheap, pre-prover rejections for degenerate theorems.
//!
//! These are microsecond-class gates — pure truth-table and syntactic checks —
//! that catch specific ways a theorem that already passed `validate_theorem`
//! can still be cheap/uninteresting, before the expensive prover ever runs:
//! - **Tautologous disjunct**: the conclusion (or its consequent, for an
//!   implication-shaped conclusion) is an Or whose disjuncts include one that's
//!   independently a tautology (e.g. `~P > ~P`), letting the whole thing be
//!   proven via Add off an empty subproof — the antecedent is decoration.
//! - **Subformula decoy**: a proper subformula of the antecedent (or of a
//!   premise) already entails the target on its own, meaning the rest of the
//!   antecedent/premise set is unused ballast.
//! - **Disguised identity**: an implication-shaped conclusion `A > B` / `~A v B`
//!   where `A` and `B` are semantically the same formula, just written a small
//!   number of equivalence-rewrites apart — "prove A > B" is secretly "restate
//!   A".
//!
//! None of these are exhaustive proofs of degeneracy — they're heuristic,
//! cheap-to-compute red flags meant to reject candidate theorems before they
//! reach the (much more expensive) prover stage.
//!
//! ## Truth-table engine: dynamic only, never the u32 fast path
//!
//! `services::truth_table`'s u32 engine (`is_tautology`/`are_equivalent`/
//! `entails`) only recognizes the literal atom names P, Q, R, S, T —
//! `var_truth_table` silently defaults every OTHER atom name to P's own
//! pattern (`truth_table.rs`, `_ => 0xFFFF0000`). `obfuscate_gen::build_atom_pool`
//! only stays within P–T for theorems with ≤5 atoms; anything with 6+ (the
//! harder generator tiers routinely go there) pulls in A, B, C, D, ... . Two
//! *different* non-standard atoms would then collapse onto the identical
//! bit pattern, silently merging distinct propositional variables into one —
//! e.g. `is_tautology("A > B")` would wrongly evaluate as `P > P` (always
//! true) instead of correctly seeing A and B as independent. Every semantic
//! check in this file therefore goes through the dynamic engine
//! (`is_tautology_dynamic`, plus the local `are_equivalent_dynamic` /
//! `entails_dynamic` below — the crate only exposes a dynamic tautology
//! check, not dynamic equivalence/entailment, so those two are hand-rolled
//! here from `DynTruthTable`'s public combinators), which builds each
//! formula's table over its own real atoms instead of a fixed P–T slot map.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::models::rules::equivalence::EquivalenceRule;
use crate::models::Formula;

use super::truth_table::{is_tautology_dynamic, DynTruthTable};

/// The sorted union of every atom appearing across `formulas` — the shared
/// variable universe two (or more) formulas must be evaluated over before
/// their `DynTruthTable`s are comparable. `compute_truth_table_dynamic`
/// (crate-level) builds this per-formula, which is fine for a single-formula
/// tautology check but wrong for comparing two formulas: each would get its
/// OWN independent atom-to-index mapping, so bit position `0` could mean "A"
/// in one table and "C" in the other. Sharing one mapping across both sides
/// of a comparison is what `compute_truth_table_dynamic` alone can't give us.
fn atom_universe(formulas: &[&Formula]) -> Vec<String> {
    let mut atoms: BTreeSet<String> = BTreeSet::new();
    for f in formulas {
        atoms.extend(f.atoms());
    }
    atoms.into_iter().collect()
}

/// Evaluate `formula` into a `DynTruthTable` over an EXTERNALLY-supplied
/// atom→index mapping (rather than one derived from `formula`'s own atoms
/// alone), so two formulas evaluated against the same `index`/`num_vars`
/// produce directly-comparable tables. Mirrors `truth_table::eval_dyn`
/// (private to that module, so reimplemented here) via `DynTruthTable`'s
/// public combinators. An atom missing from `index` (shouldn't happen when
/// `index` was built via `atom_universe` over every formula in play) falls
/// back to an all-true table, matching the crate's own defensive convention
/// in `eval_dyn` — deliberately NOT index 0, so an unmapped atom doesn't
/// silently alias onto whichever atom happens to occupy that slot.
fn dyn_table_over(formula: &Formula, index: &HashMap<&str, u8>, num_vars: u8) -> DynTruthTable {
    match formula {
        Formula::Atom(name) => match index.get(name.as_str()) {
            Some(&idx) => DynTruthTable::new_var(idx, num_vars),
            None => DynTruthTable::tautology(num_vars),
        },
        Formula::Not(inner) => dyn_table_over(inner, index, num_vars).not(),
        Formula::And(l, r) => {
            dyn_table_over(l, index, num_vars).and(&dyn_table_over(r, index, num_vars))
        }
        Formula::Or(l, r) => {
            dyn_table_over(l, index, num_vars).or(&dyn_table_over(r, index, num_vars))
        }
        Formula::Implies(l, r) => {
            dyn_table_over(l, index, num_vars).implies(&dyn_table_over(r, index, num_vars))
        }
        Formula::Biconditional(l, r) => {
            dyn_table_over(l, index, num_vars).biconditional(&dyn_table_over(r, index, num_vars))
        }
        Formula::Contradiction => DynTruthTable::contradiction(num_vars),
    }
}

/// Semantic equivalence over the dynamic engine, safe for any atom names —
/// see the module-level note on why the u32 fast path can't be used here.
fn are_equivalent_dynamic(a: &Formula, b: &Formula) -> bool {
    let atoms = atom_universe(&[a, b]);
    let num_vars = atoms.len().max(1) as u8;
    let index: HashMap<&str, u8> = atoms.iter().enumerate().map(|(i, s)| (s.as_str(), i as u8)).collect();
    dyn_table_over(a, &index, num_vars).eq(&dyn_table_over(b, &index, num_vars))
}

/// Are `formulas` jointly satisfiable — does some assignment make every one
/// of them true simultaneously? Empty input is vacuously satisfiable (the
/// empty conjunction is a tautology). Reuses the same shared-atom-universe
/// machinery as `entails_dynamic`/`are_equivalent_dynamic` above (see the
/// module-level note on why a shared mapping matters once atom pools go
/// past P-T) rather than a second evaluator — used by `golf_gate`'s
/// semantic stage (`GateReject::InconsistentPremises`) and by
/// `sample_premises`'s yield optimization (Ruling F, Task 13).
pub fn is_satisfiable_dynamic(formulas: &[Formula]) -> bool {
    if formulas.is_empty() {
        return true;
    }
    let refs: Vec<&Formula> = formulas.iter().collect();
    let atoms = atom_universe(&refs);
    let num_vars = atoms.len().max(1) as u8;
    let index: HashMap<&str, u8> = atoms.iter().enumerate().map(|(i, s)| (s.as_str(), i as u8)).collect();
    let combined = formulas.iter().fold(DynTruthTable::tautology(num_vars), |acc, f| {
        acc.and(&dyn_table_over(f, &index, num_vars))
    });
    !combined.is_contradiction()
}

/// Semantic entailment over the dynamic engine, safe for any atom names —
/// see the module-level note on why the u32 fast path can't be used here.
fn entails_dynamic(premises: &[Formula], conclusion: &Formula) -> bool {
    let mut all: Vec<&Formula> = premises.iter().collect();
    all.push(conclusion);
    let atoms = atom_universe(&all);
    let num_vars = atoms.len().max(1) as u8;
    let index: HashMap<&str, u8> = atoms.iter().enumerate().map(|(i, s)| (s.as_str(), i as u8)).collect();
    let combined = premises.iter().fold(DynTruthTable::tautology(num_vars), |acc, p| {
        acc.and(&dyn_table_over(p, &index, num_vars))
    });
    let conclusion_tt = dyn_table_over(conclusion, &index, num_vars);
    combined.and(&conclusion_tt.not()).is_contradiction()
}

/// Report of cheap cheese checks run against a candidate theorem. Each field
/// is `None` when that particular defect wasn't found; all three checks run
/// independently, so a theorem can be flagged by more than one at once.
#[derive(Debug, Clone)]
pub struct CheeseReport {
    /// The first disjunct (of the conclusion's consequent, or of the
    /// conclusion itself if it isn't implication-shaped) that is
    /// independently a tautology — provable via Add without touching the
    /// antecedent.
    pub tautologous_disjunct: Option<Formula>,
    /// A proper subformula of a premise or of the antecedent that, alone,
    /// already entails the target — the rest of the premise/antecedent is
    /// unused.
    pub subformula_decoy: Option<Formula>,
    /// `Some(d)` if the conclusion is `A > B` / `~A v B` and `A` rewrites to
    /// `B` in `d` equivalence-rule applications (`d <= max_rewrite_distance`).
    pub identity_rewrite_distance: Option<usize>,
}

/// Run all three cheese checks against a candidate theorem.
///
/// `max_rewrite_distance` bounds the disguised-identity search (see
/// `rewrite_distance`); it does not affect the other two checks.
pub fn cheese_check(
    premises: &[Formula],
    conclusion: &Formula,
    max_rewrite_distance: usize,
) -> CheeseReport {
    let parts = implication_parts(conclusion);

    let disjunct_target = match &parts {
        Some((_, consequent)) => consequent.clone(),
        None => conclusion.clone(),
    };
    let tautologous_disjunct = flatten_or(&disjunct_target).into_iter().find(is_tautology_dynamic);

    let mut subformula_decoy = parts
        .as_ref()
        .and_then(|(antecedent, consequent)| find_decoy(antecedent, consequent));
    if subformula_decoy.is_none() {
        for premise in premises {
            if let Some(decoy) = find_decoy(premise, conclusion) {
                subformula_decoy = Some(decoy);
                break;
            }
        }
    }

    let identity_rewrite_distance = parts
        .as_ref()
        .and_then(|(antecedent, consequent)| rewrite_distance(antecedent, consequent, max_rewrite_distance));

    CheeseReport { tautologous_disjunct, subformula_decoy, identity_rewrite_distance }
}

/// `A > B` -> `Some((A, B))`; `~A v B` -> `Some((A, B))`; anything else ->
/// `None`.
fn implication_parts(f: &Formula) -> Option<(Formula, Formula)> {
    match f {
        Formula::Implies(a, b) => Some((a.as_ref().clone(), b.as_ref().clone())),
        Formula::Or(left, b) => match left.as_ref() {
            Formula::Not(a) => Some((a.as_ref().clone(), b.as_ref().clone())),
            _ => None,
        },
        _ => None,
    }
}

/// Flatten a left/right-nested `Or` chain into its leaf disjuncts, left to
/// right. A non-`Or` formula flattens to the single-element list `[f]`.
fn flatten_or(f: &Formula) -> Vec<Formula> {
    match f {
        Formula::Or(left, right) => {
            let mut disjuncts = flatten_or(left.as_ref());
            disjuncts.extend(flatten_or(right.as_ref()));
            disjuncts
        }
        _ => vec![f.clone()],
    }
}

/// Find a proper subformula of `container` that, alone, already entails
/// `target` — i.e. the rest of `container` is unused ballast.
///
/// Skips `s` when it IS `container` (not a proper subformula) or is
/// semantically equivalent to it, and likewise skips `s` when it IS or is
/// equivalent to `target` itself: an atom buried several levels down that
/// happens to spell out the target verbatim (e.g. the `S` inside `R > S`
/// when the target is bare `S`) trivially "entails" it by reflexivity, which
/// isn't a meaningful decoy — it's just the target's own name showing up in
/// unrelated structure. Without this second skip, any antecedent chain that
/// mentions the target's atom anywhere (routine in ordinary Hypothetical-
/// Syllogism-style theorems, e.g. round9's `P.(R>S).(P>Q).(Q>R) > S`) would
/// false-positive on the atom nested inside `R > S`.
fn find_decoy(container: &Formula, target: &Formula) -> Option<Formula> {
    for s in container.subformulas() {
        if &s == container || are_equivalent_dynamic(&s, container) {
            continue;
        }
        if &s == target || are_equivalent_dynamic(&s, target) {
            continue;
        }
        if entails_dynamic(std::slice::from_ref(&s), target) {
            return Some(s);
        }
    }
    None
}

/// Minimum number of single equivalence-rule applications needed to rewrite
/// `a` into exactly `b` (BFS over the rewrite graph), or `None` if `a` and
/// `b` aren't even semantically equivalent, or if no such path was found
/// within `max` steps / before the node cap was hit.
///
/// Each BFS edge is one `(path, rule, equivalent_forms result)` triple:
/// replace the subformula at `path` with one of its equivalent forms under
/// one rule. Visited formulas are deduped on `ascii_string()` rather than
/// `Formula` equality directly, per the task brief.
pub fn rewrite_distance(a: &Formula, b: &Formula, max: usize) -> Option<usize> {
    if !are_equivalent_dynamic(a, b) {
        return None;
    }
    if a == b {
        return Some(0);
    }

    // Cap on distinct nodes visited across the whole search (not per depth).
    // If it's hit, we don't know whether `b` is reachable within `max` steps
    // or not — and since a `None` return here just means "disguised-identity
    // cheese not detected," staying permissive (None) rather than guessing is
    // the safe direction: a truncated search must never cause cheese_check to
    // reject a theorem it didn't actually verify is cheesy.
    const NODE_CAP: usize = 20_000;

    let rules = EquivalenceRule::all();
    let mut visited: HashSet<String> = HashSet::new();
    visited.insert(a.ascii_string());
    let mut frontier = vec![a.clone()];
    let mut node_count = 1usize;

    for depth in 1..=max {
        let mut next_frontier = Vec::new();
        for current in &frontier {
            for (path, sub) in current.subformulas_with_paths() {
                for rule in &rules {
                    for form in rule.equivalent_forms(sub) {
                        let candidate = current.replace_at_path(&path, &form);
                        if &candidate == b {
                            return Some(depth);
                        }
                        if visited.insert(candidate.ascii_string()) {
                            node_count += 1;
                            if node_count > NODE_CAP {
                                return None;
                            }
                            next_frontier.push(candidate);
                        }
                    }
                }
            }
        }
        if next_frontier.is_empty() {
            return None;
        }
        frontier = next_frontier;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        Formula::parse(s).unwrap()
    }

    #[test]
    fn round10_has_tautologous_disjunct() {
        let c = f("{[(R > ~P) v (P > P)] . {S > [(Q v ~S) > ~S]}} > [(P > ~R) v (~P > ~P)]");
        let r = cheese_check(&[], &c, 3);
        assert_eq!(r.tautologous_disjunct, Some(f("~P > ~P")));
    }

    #[test]
    fn round11_is_identity_at_distance_2() {
        let c = f("~{{[(~R v ~R) > R] . P} . [(S v S) > (Q v ~S)]} v {{[(R > ~R) > R] . P} . {~(Q v ~S) > ~(S v S)}}");
        let r = cheese_check(&[], &c, 3);
        assert_eq!(r.identity_rewrite_distance, Some(2));
    }

    #[test]
    fn round9_is_clean_of_cheese() {
        let c = f("{P . {(R > S) . [(P > Q) . (Q > R)]}} > S");
        let r = cheese_check(&[], &c, 3);
        assert!(
            r.tautologous_disjunct.is_none()
                && r.subformula_decoy.is_none()
                && r.identity_rewrite_distance.is_none()
        );
    }

    #[test]
    fn single_impl_rewrite_is_distance_1() {
        assert_eq!(rewrite_distance(&f("P > Q"), &f("~P v Q"), 3), Some(1));
        assert_eq!(rewrite_distance(&f("P"), &f("Q"), 3), None); // not even equivalent
    }

    // ── Fix round 1: dynamic truth tables (generator atoms exceed P/Q/R/S/T) ──
    //
    // Regression coverage for the u32-fast-path bug: `var_truth_table`
    // defaulted every non-P..T atom to P's own bit pattern, so two distinct
    // "unknown" atoms were silently treated as the same variable. The
    // generator's real atom pool (`obfuscate_gen::build_atom_pool`) goes past
    // P–T for any theorem with 6+ atoms, so this was live for real generated
    // theorems, not just a hypothetical.

    #[test]
    fn no_false_tautologous_disjunct_with_non_standard_atoms() {
        // Literal case from the fix-round finding: under the old path, "A"
        // and "B" both defaulted to P's pattern. As implemented, flatten_or
        // splits "A v ~B" into two single-atom disjuncts (A, ~B) — neither
        // was ever individually mistaken for a tautology even under the old
        // bug (a bare atom's collapsed pattern is never all-true), so this is
        // a direct sanity check of the requested scenario rather than a case
        // that flips old-vs-new. See the next test for one that actually
        // does flip.
        let c = f("A v ~B");
        let r = cheese_check(&[], &c, 3);
        assert!(r.tautologous_disjunct.is_none());
    }

    #[test]
    fn no_false_tautologous_disjunct_for_compound_non_flattened_disjunct() {
        // Genuinely discriminating: "A > B" is ONE disjunct (Implies isn't
        // Or, so flatten_or doesn't split it further). Under the OLD u32
        // path, A and B both collapsed to P's pattern, making "A > B"
        // evaluate as "P > P" — always true — wrongly flagging it as a
        // tautologous disjunct. With A and B genuinely independent, "A > B"
        // is not a tautology (A=true, B=false is a counterexample), so
        // neither disjunct should trigger under the fixed dynamic path.
        let c = f("(A > B) v C");
        let r = cheese_check(&[], &c, 3);
        assert!(r.tautologous_disjunct.is_none());
    }

    #[test]
    fn rewrite_distance_is_correct_with_non_standard_atoms() {
        // Requested literal case. Note this one does NOT actually flip
        // old-vs-new: both sides of "A > B" / "~A v B" collapse to the same
        // degenerate all-true pattern under the old bug too (P>P and ~PvP
        // are both tautologies), so the old `are_equivalent` gate happened to
        // return true here for the wrong reason, and rewrite_distance's BFS
        // is purely syntactic (equivalence rules never rename atoms, and the
        // goal check is structural `Formula` equality) — so it would have
        // found the same real 1-step Implication rewrite regardless. Kept
        // as explicit end-to-end coverage that the function is now actually
        // exercised with generator-realistic atoms, which it never was
        // before this fix round.
        assert_eq!(rewrite_distance(&f("A > B"), &f("~A v B"), 3), Some(1));
    }

    #[test]
    fn decoy_check_stays_clean_for_pure_non_standard_atoms() {
        // Sanity check, NOT a discriminating regression test — see the next
        // test for one that actually flips old-vs-new. Every formula built
        // ENTIRELY from non-P..T atoms collapses under the old bug to one of
        // only 4 possible u32 patterns (P, ~P, tautology, or contradiction —
        // a formula evaluated with every "variable" tied to the same signal
        // is necessarily a function of one boolean input, and a 1-input
        // boolean function has only 4 possible truth tables). Among those 4,
        // the only non-self entailments are "anything entails tautology" and
        // "contradiction entails anything" — both real, valid entailments
        // even under correct semantics, not bugs. So two DIFFERENT-shaped
        // all-non-standard subformulas can only get a false-positive
        // `entails` by collapsing to the IDENTICAL pattern, which is exactly
        // what `find_decoy`'s existing "skip if equivalent" filters already
        // catch (added for the round9 fix) — they incidentally close this
        // bug's attack surface too, for the pure-non-standard case.
        let c = f("(A . B) > C");
        let r = cheese_check(&[], &c, 3);
        assert!(r.subformula_decoy.is_none());
    }

    // ── Round 2: positive-path coverage (subformula_decoy actually firing) ──
    //
    // Every test above that touches subformula_decoy asserts `.is_none()`;
    // none proves the field is ever `Some`. These two do, on straightforward
    // Add-shortcut shapes: a conjunct of the antecedent (or a premise) that
    // alone already entails the target via the disjunction-introduction
    // pattern (`P` entails `P v anything`).

    #[test]
    fn decoy_fires_on_add_shortcut_shape() {
        // Antecedent "P.Q": its left conjunct "P" alone already entails the
        // consequent "P v Q v Z" (Add), independent of "Q" or "Z". Checked
        // via subformulas() in left-to-right order, so "P" is found before
        // "Q" is ever considered.
        let c = f("(P . Q) > (P v Q v Z)");
        let r = cheese_check(&[], &c, 3);
        assert_eq!(r.subformula_decoy, Some(f("P")));
    }

    #[test]
    fn decoy_fires_from_premises() {
        // No implication-shaped conclusion here (conclusion is a bare "P v
        // Z", not "~A v B" — left disjunct "P" isn't a Not), so this only
        // exercises the premises branch: proper subformula "P" of the
        // premise "P . Junk" alone already entails "P v Z" (Add); "Junk" is
        // unused ballast, real or fake.
        let c = f("P v Z");
        let r = cheese_check(&[f("P . Junk")], &c, 3);
        assert_eq!(r.subformula_decoy, Some(f("P")));
    }

    #[test]
    fn decoy_check_catches_mixed_standard_and_nonstandard_atom_bug() {
        // Genuinely discriminating (verified: fails under the old u32 path,
        // passes under the fix). A non-standard atom defaults to EXACTLY
        // real P's bit pattern under the old bug, so it inherits whatever
        // real relationships P happens to have — here, P's real entailment
        // of "P v Q" (Add). Antecedent "A . R": proper subformula "A" is a
        // completely independent variable in truth, but under the bug its
        // collapsed pattern is a subset of "P v Q"'s true-rows purely
        // because it LOOKS like P, wrongly flagging "A" as a decoy. "R" is
        // there only so the antecedent is a genuine conjunction; it plays no
        // role in triggering (or avoiding) the bug. This mixed shape is also
        // the realistic one: `build_atom_pool` always includes all of P..T
        // before adding any extended letter, so any real 6+-atom generated
        // theorem necessarily mixes both ranges in one formula — a pure
        // A/B/C-only formula (previous test) could never actually come out
        // of the generator.
        let c = f("(A . R) > (P v Q)");
        let r = cheese_check(&[], &c, 3);
        assert!(r.subformula_decoy.is_none());
    }
}
