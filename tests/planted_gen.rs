use logic_core::models::rules::ProofTechnique;
use logic_core::models::{Formula, Justification, Proof};
use logic_core::services::truth_table::{is_tautology_dynamic, DynTruthTable};
use logic_core::services::{golf_gate, plant, GateConfig, OptimalConfig, PlantedCandidate, PlantSpec};

fn small_spec() -> PlantSpec {
    PlantSpec {
        atoms: 4,
        par_min: 6,
        par_max: 12,
        max_premises: 4,
        max_formula_len: 90,
        subproofs: 0,
        obfuscation_passes: 0,
    }
}

fn spec_with_subproofs(n: u8) -> PlantSpec {
    let mut spec = small_spec();
    spec.subproofs = n;
    spec
}

fn spec_with_obfuscation(passes: u8) -> PlantSpec {
    let mut spec = small_spec();
    spec.obfuscation_passes = passes;
    spec
}

#[test]
fn plant_produces_valid_complete_proof_in_band() {
    let spec = small_spec();
    let mut found = 0;
    for seed in 0..200u64 {
        if let Ok(c) = plant(&spec, seed) {
            found += 1;
            assert!(c.par >= 6 && c.par <= 12);
            assert_eq!(c.par, c.proof.lines.len() - c.theorem.premises.len());
            let mut p = c.proof.clone();
            logic_core::services::ProofVerifier::verify_proof(&mut p);
            assert!(p.lines.iter().all(|l| l.is_valid));
            assert!(p.check_complete());
        }
    }
    assert!(found >= 20, "yield too low at small pars: {found}/200");
}

#[test]
fn plant_is_deterministic() {
    let spec = small_spec();
    let a = plant(&spec, 42);
    let b = plant(&spec, 42);

    match (a, b) {
        (Ok(ca), Ok(cb)) => {
            assert_eq!(ca.par, cb.par);
            let premises_a: Vec<String> = ca
                .theorem
                .premises
                .iter()
                .map(|f| f.ascii_string_bracketed())
                .collect();
            let premises_b: Vec<String> = cb
                .theorem
                .premises
                .iter()
                .map(|f| f.ascii_string_bracketed())
                .collect();
            assert_eq!(premises_a, premises_b);
            assert_eq!(
                ca.theorem.conclusion.ascii_string_bracketed(),
                cb.theorem.conclusion.ascii_string_bracketed()
            );
            assert_eq!(ca.proof.lines.len(), cb.proof.lines.len());
            for (la, lb) in ca.proof.lines.iter().zip(cb.proof.lines.iter()) {
                assert_eq!(la.formula.ascii_string_bracketed(), lb.formula.ascii_string_bracketed());
            }
        }
        (Err(ea), Err(eb)) => {
            assert_eq!(format!("{:?}", ea), format!("{:?}", eb));
        }
        other => panic!("plant(&spec, 42) is not deterministic across calls: {other:?}"),
    }
}

/// Shared by `cone_has_no_dead_lines` and its subproof-covering sibling
/// below: every non-premise, non-conclusion line must be reachable from the
/// conclusion by walking `referenced_lines()` alone.
fn assert_cone_has_no_dead_lines(c: &PlantedCandidate, seed: u64) {
    let n_premises = c.theorem.premises.len();
    // The rebuild always appends the conclusion last (every other cone
    // member is something the conclusion transitively depends on, so it
    // must have a strictly earlier line number).
    let conclusion_line = c.proof.lines.len();

    let mut cited = std::collections::HashSet::new();
    let mut stack = vec![conclusion_line];
    while let Some(idx) = stack.pop() {
        if cited.insert(idx) {
            if let Some(line) = c.proof.get_line(idx) {
                for r in line.justification.referenced_lines() {
                    stack.push(r);
                }
            }
        }
    }

    for line in &c.proof.lines {
        let is_premise = line.line_number <= n_premises;
        let is_conclusion = line.line_number == conclusion_line;
        if !is_premise && !is_conclusion {
            assert!(
                cited.contains(&line.line_number),
                "seed {seed}: line {} is dead (not cited by the conclusion)",
                line.line_number
            );
        }
    }
}

#[test]
fn cone_has_no_dead_lines() {
    let spec = small_spec();
    let mut checked = 0;
    for seed in 0..50u64 {
        if let Ok(c) = plant(&spec, seed) {
            checked += 1;
            assert_cone_has_no_dead_lines(&c, seed);
        }
    }
    assert!(checked > 0, "no seeds produced a candidate to check");
}

/// Extends the plain-growth check above to subproof-bearing candidates, now
/// that scope-internal pruning (Ruling A, Task 8b) makes the conclusion's
/// full `referenced_lines()` closure exactly equal to the proof's line set.
/// Pre-fix this failed here too: a scope's filler lines were pulled in by
/// `compute_cone`'s old whole-range pull but were never reachable by this
/// walk. `subproofs: 2` also exercises nested scopes.
#[test]
fn cone_has_no_dead_lines_with_subproofs() {
    let spec = spec_with_subproofs(2);
    let mut checked = 0;
    for seed in 0..300u64 {
        if let Ok(c) = plant(&spec, seed) {
            checked += 1;
            assert_cone_has_no_dead_lines(&c, seed);
        }
    }
    assert!(checked > 0, "no seeds produced a candidate to check");
}

/// A proof "contains a subproof" iff it has both an `Assumption` line and a
/// `SubproofConclusion` (discharge) line.
fn contains_subproof(proof: &logic_core::models::Proof) -> bool {
    let has_assumption = proof
        .lines
        .iter()
        .any(|l| matches!(l.justification, Justification::Assumption { .. }));
    let has_discharge = proof
        .lines
        .iter()
        .any(|l| matches!(l.justification, Justification::SubproofConclusion { .. }));
    has_assumption && has_discharge
}

#[test]
fn plant_subproofs_1_yields_cp_ip_candidates() {
    let spec = spec_with_subproofs(1);
    let mut subproof_accepts = 0;
    for seed in 0..300u64 {
        if let Ok(c) = plant(&spec, seed) {
            assert!(c.par >= spec.par_min && c.par <= spec.par_max);
            if contains_subproof(&c.proof) {
                subproof_accepts += 1;
                let mut p = c.proof.clone();
                logic_core::services::ProofVerifier::verify_proof(&mut p);
                assert!(
                    p.lines.iter().all(|l| l.is_valid),
                    "seed {seed}: subproof-bearing candidate failed native verification"
                );
                assert!(
                    p.check_complete(),
                    "seed {seed}: subproof-bearing candidate is not complete"
                );
            }
        }
    }
    assert!(
        subproof_accepts >= 15,
        "yield too low for subproofs:1 — {subproof_accepts}/300 accepted candidates contained a subproof"
    );
}

#[test]
fn plant_is_deterministic_with_subproofs() {
    // Seed 12 is confirmed (by inspection) to produce an accepted,
    // subproof-bearing candidate under this spec — so this test actually
    // exercises determinism of the new scope/replay machinery, not just
    // determinism of two matching `Err`s.
    let spec = spec_with_subproofs(1);
    let a = plant(&spec, 12);
    let b = plant(&spec, 12);

    match (a, b) {
        (Ok(ca), Ok(cb)) => {
            assert_eq!(ca.par, cb.par);
            let premises_a: Vec<String> = ca
                .theorem
                .premises
                .iter()
                .map(|f| f.ascii_string_bracketed())
                .collect();
            let premises_b: Vec<String> = cb
                .theorem
                .premises
                .iter()
                .map(|f| f.ascii_string_bracketed())
                .collect();
            assert_eq!(premises_a, premises_b);
            assert_eq!(
                ca.theorem.conclusion.ascii_string_bracketed(),
                cb.theorem.conclusion.ascii_string_bracketed()
            );
            assert_eq!(ca.proof.lines.len(), cb.proof.lines.len());
            for (la, lb) in ca.proof.lines.iter().zip(cb.proof.lines.iter()) {
                assert_eq!(la.formula.ascii_string_bracketed(), lb.formula.ascii_string_bracketed());
                assert_eq!(la.depth, lb.depth);
                assert_eq!(
                    la.justification.display_string(),
                    lb.justification.display_string()
                );
            }
        }
        (Err(ea), Err(eb)) => {
            assert_eq!(format!("{:?}", ea), format!("{:?}", eb));
        }
        other => panic!("plant(&spec, 12) is not deterministic across calls: {other:?}"),
    }
}

#[test]
fn plant_subproofs_2_reaches_nesting_depth_2() {
    let spec = spec_with_subproofs(2);
    let mut found_depth_2 = false;
    for seed in 0..500u64 {
        if let Ok(c) = plant(&spec, seed) {
            assert!(c.par >= spec.par_min && c.par <= spec.par_max);
            if c.proof.lines.iter().any(|l| l.depth == 2) {
                found_depth_2 = true;
                let mut p = c.proof.clone();
                logic_core::services::ProofVerifier::verify_proof(&mut p);
                assert!(
                    p.lines.iter().all(|l| l.is_valid),
                    "seed {seed}: depth-2 candidate failed native verification"
                );
                assert!(p.check_complete(), "seed {seed}: depth-2 candidate is not complete");
                break;
            }
        }
    }
    assert!(
        found_depth_2,
        "no seed in 0..500 produced a nesting-depth-2 candidate under subproofs:2"
    );
}

/// (a) Costumed candidates still verify natively, are complete, and `par` is
/// exactly `proof.lines.len() - theorem.premises.len()` — the costume pass
/// adds prologue/epilogue lines on top of the (already band-checked) cone,
/// so unlike the plain-growth tests above we do NOT assert `par` stays
/// within `[par_min, par_max]`; only that the accounting itself is exact.
#[test]
fn plant_with_obfuscation_verifies_and_pars_exactly() {
    let spec = spec_with_obfuscation(2);
    let mut checked = 0;
    for seed in 0..200u64 {
        if let Ok(c) = plant(&spec, seed) {
            checked += 1;
            assert_eq!(
                c.par,
                c.proof.lines.len() - c.theorem.premises.len(),
                "seed {seed}: par must equal total lines minus premises"
            );
            let mut p = c.proof.clone();
            logic_core::services::ProofVerifier::verify_proof(&mut p);
            assert!(
                p.lines.iter().all(|l| l.is_valid),
                "seed {seed}: costumed candidate failed native verification"
            );
            assert!(p.check_complete(), "seed {seed}: costumed candidate is not complete");
        }
    }
    assert!(checked >= 20, "yield too low with obfuscation_passes:2: {checked}/200");
}

/// (b) The costume pass actually does something: for at least one seed, the
/// theorem's conclusion produced with `obfuscation_passes: 2` differs from
/// the conclusion produced by the un-obfuscated run of the same seed
/// (`obfuscation_passes: 0`) — everything upstream of costuming (premises,
/// growth, cone selection) is byte-identical between the two specs, so any
/// difference is attributable to the costume pass.
#[test]
fn plant_with_obfuscation_changes_the_conclusion_for_at_least_one_seed() {
    let costumed_spec = spec_with_obfuscation(2);
    let plain_spec = spec_with_obfuscation(0);
    let mut found = false;
    for seed in 0..200u64 {
        if let (Ok(costumed), Ok(plain)) = (plant(&costumed_spec, seed), plant(&plain_spec, seed)) {
            if costumed.theorem.conclusion.ascii_string_bracketed()
                != plain.theorem.conclusion.ascii_string_bracketed()
            {
                found = true;
                break;
            }
        }
    }
    assert!(found, "no seed in 0..200 produced a costume-changed conclusion");
}

/// (c) Determinism holds through the costume pass too: same seed, same
/// spec, byte-identical proof — including the new Equivalence
/// (prologue/epilogue) lines' formulas, depths, and justification strings.
#[test]
fn plant_with_obfuscation_is_deterministic() {
    let spec = spec_with_obfuscation(2);
    let seed = (0..200u64)
        .find(|&seed| plant(&spec, seed).is_ok())
        .expect("no seed in 0..200 produced an accepted candidate with obfuscation_passes:2");

    let a = plant(&spec, seed).expect("seed was already confirmed Ok above");
    let b = plant(&spec, seed).expect("seed was already confirmed Ok above");

    assert_eq!(a.par, b.par);
    let premises_a: Vec<String> = a.theorem.premises.iter().map(|f| f.ascii_string_bracketed()).collect();
    let premises_b: Vec<String> = b.theorem.premises.iter().map(|f| f.ascii_string_bracketed()).collect();
    assert_eq!(premises_a, premises_b);
    assert_eq!(
        a.theorem.conclusion.ascii_string_bracketed(),
        b.theorem.conclusion.ascii_string_bracketed()
    );
    assert_eq!(a.proof.lines.len(), b.proof.lines.len());
    for (la, lb) in a.proof.lines.iter().zip(b.proof.lines.iter()) {
        assert_eq!(la.formula.ascii_string_bracketed(), lb.formula.ascii_string_bracketed());
        assert_eq!(la.depth, lb.depth);
        assert_eq!(la.justification.display_string(), lb.justification.display_string());
    }
}

/// `subproofs > 0` and `obfuscation_passes > 0` composed together: the
/// costume pass's body replay must preserve subproof scope structure
/// (open_subproof/close_subproof, exactly as `rebuild_proof` does) around
/// prologue/epilogue Equivalence lines. This is the highest integration
/// risk in Task 5 — a silent regression here would corrupt subproof-bearing
/// answer-key entries — so it needs its own committed coverage rather than
/// being inferred from the subproof-only and obfuscation-only tests above.
/// Mirrors test (a)'s shape (verify + complete + par-exact), and
/// additionally requires several checked candidates to actually contain a
/// subproof so the assertions aren't vacuously true. Seed budget calibrated
/// small (0..150 yields ~19 accepted candidates, all subproof-bearing, in
/// well under a second) to keep suite runtime sane per review guidance.
#[test]
fn plant_with_subproofs_and_obfuscation_compose() {
    let mut spec = spec_with_subproofs(2);
    spec.obfuscation_passes = 2;
    let mut checked = 0;
    let mut with_subproof = 0;
    for seed in 0..150u64 {
        if let Ok(c) = plant(&spec, seed) {
            checked += 1;
            assert_eq!(
                c.par,
                c.proof.lines.len() - c.theorem.premises.len(),
                "seed {seed}: par must equal total lines minus premises"
            );
            let mut p = c.proof.clone();
            logic_core::services::ProofVerifier::verify_proof(&mut p);
            assert!(
                p.lines.iter().all(|l| l.is_valid),
                "seed {seed}: subproof+costume candidate failed native verification"
            );
            assert!(
                p.check_complete(),
                "seed {seed}: subproof+costume candidate is not complete"
            );
            if contains_subproof(&c.proof) {
                with_subproof += 1;
            }
        }
    }
    assert!(checked >= 10, "yield too low for subproofs:2 + obfuscation:2: {checked}/150");
    assert!(
        with_subproof >= 3,
        "too few subproof-bearing candidates to meaningfully exercise the composition: {with_subproof}/{checked}"
    );
}

// ─── Task 8b: scope dead-line pruning + duplicate-discharge rejection ──────

/// Positions reachable from `anchor` (inclusive) by walking
/// `referenced_lines()`, only recursing into references that fall inside
/// `[start, end]` — mirrors the within-scope half of the anchor-transitive
/// pruning rule `compute_cone` now applies in `planted_gen.rs` (a reference
/// pointing outside the scope is an outer cone edge, not a scope-internal
/// dependency, so it's excluded here without being followed further).
fn within_scope_reachable(proof: &Proof, start: usize, end: usize) -> std::collections::HashSet<usize> {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![end];
    seen.insert(end);
    while let Some(pos) = stack.pop() {
        if let Some(line) = proof.get_line(pos) {
            for r in line.justification.referenced_lines() {
                if r >= start && r <= end && seen.insert(r) {
                    stack.push(r);
                }
            }
        }
    }
    seen
}

/// Ruling A (Task 8b), fix 1: within a kept IP scope, only the assumption
/// and whatever the contradiction line transitively requires should survive
/// — filler growth `grow_ip_subproof` may add before closing the
/// contradiction must NOT ride along "for free". Pre-fix, Task 8 measured
/// this failing for 76% of IP scopes (44/58, mean 1.45 dead lines each); see
/// `docs/superpowers/plans/2026-08-24-proof-golf-MEASUREMENTS.md` §4.
#[test]
fn ip_scopes_carry_no_dead_lines() {
    let spec = spec_with_subproofs(1);
    let mut ip_bearing_accepts = 0usize;
    let mut scopes_checked = 0usize;
    let mut violations: Vec<String> = Vec::new();
    let mut seed = 0u64;
    while ip_bearing_accepts < 10 && seed < 5000 {
        if let Ok(c) = plant(&spec, seed) {
            let mut has_ip = false;
            for line in &c.proof.lines {
                if let Justification::SubproofConclusion {
                    technique: ProofTechnique::IndirectProof,
                    subproof_start,
                    subproof_end,
                } = &line.justification
                {
                    let (start, end) = (*subproof_start, *subproof_end);
                    has_ip = true;
                    scopes_checked += 1;
                    let required = within_scope_reachable(&c.proof, start, end);
                    for pos in (start + 1)..=end {
                        if !required.contains(&pos) {
                            violations.push(format!(
                                "seed {seed}: IP scope [{start},{end}] line {pos} is dead \
                                 (not transitively cited by the contradiction at {end})"
                            ));
                        }
                    }
                }
            }
            if has_ip {
                ip_bearing_accepts += 1;
            }
        }
        seed += 1;
    }
    assert!(
        ip_bearing_accepts >= 10,
        "only found {ip_bearing_accepts} IP-bearing accepts in seeds 0..{seed}"
    );
    assert!(
        violations.is_empty(),
        "{} dead scope-internal line(s) across {scopes_checked} IP scopes:\n{}",
        violations.len(),
        violations.join("\n")
    );
}

/// Ruling A (Task 8b), fix 1: within a kept CP scope, only the assumption
/// and whatever the discharged consequent (the scope's final inner line)
/// transitively requires should survive.
#[test]
fn cp_scopes_carry_no_dead_lines() {
    let spec = spec_with_subproofs(1);
    let mut cp_bearing_accepts = 0usize;
    let mut scopes_checked = 0usize;
    let mut violations: Vec<String> = Vec::new();
    let mut seed = 0u64;
    while cp_bearing_accepts < 10 && seed < 5000 {
        if let Ok(c) = plant(&spec, seed) {
            let mut has_cp = false;
            for line in &c.proof.lines {
                if let Justification::SubproofConclusion {
                    technique: ProofTechnique::ConditionalProof,
                    subproof_start,
                    subproof_end,
                } = &line.justification
                {
                    let (start, end) = (*subproof_start, *subproof_end);
                    has_cp = true;
                    scopes_checked += 1;
                    let required = within_scope_reachable(&c.proof, start, end);
                    for pos in (start + 1)..=end {
                        if !required.contains(&pos) {
                            violations.push(format!(
                                "seed {seed}: CP scope [{start},{end}] line {pos} is dead \
                                 (not transitively cited by the discharged consequent at {end})"
                            ));
                        }
                    }
                }
            }
            if has_cp {
                cp_bearing_accepts += 1;
            }
        }
        seed += 1;
    }
    assert!(
        cp_bearing_accepts >= 10,
        "only found {cp_bearing_accepts} CP-bearing accepts in seeds 0..{seed}"
    );
    assert!(
        violations.is_empty(),
        "{} dead scope-internal line(s) across {scopes_checked} CP scopes:\n{}",
        violations.len(),
        violations.join("\n")
    );
}

/// Ruling E (Task 8c): an IP discharge must be a FRESH formula — not
/// byte-equal to any formula on an earlier line accessible from the
/// discharge's own position, not merely a re-statement of the seed line's
/// formula. Pre-v0.3.2, `grow_ip_subproof` always discharged exactly its
/// own seed line's formula verbatim, so this must fail against v0.3.1 for
/// every single IP-bearing accept — see the report for the recorded
/// pre-fix count.
#[test]
fn ip_discharges_are_fresh_formulas() {
    let spec = spec_with_subproofs(1);
    let mut ip_bearing_accepts = 0usize;
    let mut violations: Vec<String> = Vec::new();
    let mut seed = 0u64;
    while ip_bearing_accepts < 10 && seed < 5000 {
        if let Ok(c) = plant(&spec, seed) {
            let mut has_ip = false;
            for line in &c.proof.lines {
                if let Justification::SubproofConclusion {
                    technique: ProofTechnique::IndirectProof, ..
                } = &line.justification
                {
                    has_ip = true;
                    let dup = c.proof.lines.iter().any(|earlier| {
                        earlier.line_number < line.line_number
                            && earlier.formula == line.formula
                            && c.proof.is_line_accessible(line.line_number, earlier.line_number)
                    });
                    if dup {
                        violations.push(format!(
                            "seed {seed}: IP discharge at line {} duplicates an earlier accessible formula",
                            line.line_number
                        ));
                    }
                }
            }
            if has_ip {
                ip_bearing_accepts += 1;
            }
        }
        seed += 1;
    }
    assert!(
        ip_bearing_accepts >= 10,
        "only found {ip_bearing_accepts} IP-bearing accepts in seeds 0..{seed}"
    );
    assert!(
        violations.is_empty(),
        "{} IP discharge(s) duplicated an earlier accessible formula across {ip_bearing_accepts} IP-bearing accepts:\n{}",
        violations.len(),
        violations.join("\n")
    );
}

/// Ruling A (Task 8b), fix 2, unconditional as of Ruling E (Task 8c): a
/// subproof's discharge must not reproduce a formula that was already
/// accessible before the scope opened — that's the measured redundant-chain
/// pattern (`g1-100029`: three sequential IP subproofs re-deriving the same
/// formula, 15 of 21 par lines wasted; see MEASUREMENTS.md §4's "Bonus
/// observation").
///
/// Pre-Task-8c, IP's discharge was *definitionally* its own seed line's
/// formula, so exactly one accessible match (the seed itself) was
/// unavoidable and had to be tolerated (threshold 2, vs. 1 for CP's fresh
/// implication). Task 8c's template-based `grow_ip_subproof` discharges a
/// genuinely fresh compound formula never tied to the seed, so IP now holds
/// to the same threshold-1 (zero tolerance) bar as CP.
#[test]
fn no_duplicate_discharge() {
    let spec = spec_with_subproofs(1);
    let mut checked = 0usize;
    let mut violations: Vec<String> = Vec::new();
    for seed in 0..2000u64 {
        if let Ok(c) = plant(&spec, seed) {
            checked += 1;
            for line in &c.proof.lines {
                if !matches!(line.justification, Justification::SubproofConclusion { .. }) {
                    continue;
                }
                let matches: Vec<usize> = c
                    .proof
                    .lines
                    .iter()
                    .filter(|earlier| {
                        earlier.line_number < line.line_number
                            && earlier.formula == line.formula
                            && c.proof.is_line_accessible(line.line_number, earlier.line_number)
                    })
                    .map(|earlier| earlier.line_number)
                    .collect();
                if !matches.is_empty() {
                    violations.push(format!(
                        "seed {seed}: discharge at line {} duplicates accessible line(s) {matches:?}",
                        line.line_number
                    ));
                }
            }
        }
    }
    assert!(checked > 0, "no seeds produced a candidate to check");
    assert!(
        violations.is_empty(),
        "{} duplicate discharge(s) found across {checked} accepted candidates:\n{}",
        violations.len(),
        violations.join("\n")
    );
}

/// Determinism holds through the new scope-internal pruning and
/// duplicate-discharge rejection (Ruling A, Task 8b) — not just for one
/// hand-picked seed (`plant_is_deterministic_with_subproofs` above), but
/// across a broad range, so the new logic's several branches (pruned-empty
/// interior, nested-scope recursion, IP rejection, CP rejection) all get
/// exercised at least once under a same-seed-twice check.
#[test]
fn plant_is_deterministic_across_many_subproof_seeds() {
    let spec = spec_with_subproofs(2);
    let mut checked = 0usize;
    for seed in 0..300u64 {
        let a = plant(&spec, seed);
        let b = plant(&spec, seed);
        match (a, b) {
            (Ok(ca), Ok(cb)) => {
                checked += 1;
                assert_eq!(ca.par, cb.par, "seed {seed}: par mismatch");
                assert_eq!(ca.proof.lines.len(), cb.proof.lines.len(), "seed {seed}: line count mismatch");
                for (la, lb) in ca.proof.lines.iter().zip(cb.proof.lines.iter()) {
                    assert_eq!(la.formula, lb.formula, "seed {seed}: formula mismatch");
                    assert_eq!(la.depth, lb.depth, "seed {seed}: depth mismatch");
                    assert_eq!(
                        la.justification.display_string(),
                        lb.justification.display_string(),
                        "seed {seed}: justification mismatch"
                    );
                }
            }
            (Err(ea), Err(eb)) => {
                assert_eq!(format!("{ea:?}"), format!("{eb:?}"), "seed {seed}: error mismatch");
            }
            other => panic!("seed {seed}: plant(&spec, {seed}) is not deterministic across calls: {other:?}"),
        }
    }
    assert!(checked > 0, "no seeds under subproofs:2 produced a candidate to check");
}

// ─── Ruling F / Task 13: semantic gate + zero accessible duplicate lines ───

/// Per-band `PlantSpec`, copying propbench's `spec_for_band`
/// (`propbench/src/golf.rs`) shipped constants verbatim — these are the
/// pre-costume par windows the real frozen set was generated at.
fn spec_for_band(band: u8) -> PlantSpec {
    let (par_min, par_max) = match band {
        1 => (7, 11),
        2 => (14, 19),
        3 => (19, 26),
        other => panic!("band must be 1..=3, got {other}"),
    };
    PlantSpec {
        atoms: 4,
        par_min,
        par_max,
        max_premises: 5,
        max_formula_len: 90,
        subproofs: 1,
        obfuscation_passes: 2,
    }
}

/// The shared-atom-universe union of every formula's own atoms — needed
/// before separately-evaluated `DynTruthTable`s can be compared/combined
/// (each formula's own `atoms()` alone isn't enough: two formulas over
/// different atom sets would otherwise get bit position 0 meaning a
/// different variable in each).
fn atoms_of_all(formulas: &[Formula]) -> Vec<String> {
    let mut atoms: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for f in formulas {
        atoms.extend(f.atoms());
    }
    atoms.into_iter().collect()
}

fn table_over(f: &Formula, index: &std::collections::HashMap<&str, u8>, num_vars: u8) -> DynTruthTable {
    match f {
        Formula::Atom(name) => match index.get(name.as_str()) {
            Some(&i) => DynTruthTable::new_var(i, num_vars),
            None => DynTruthTable::tautology(num_vars),
        },
        Formula::Not(inner) => table_over(inner, index, num_vars).not(),
        Formula::And(l, r) => table_over(l, index, num_vars).and(&table_over(r, index, num_vars)),
        Formula::Or(l, r) => table_over(l, index, num_vars).or(&table_over(r, index, num_vars)),
        Formula::Implies(l, r) => table_over(l, index, num_vars).implies(&table_over(r, index, num_vars)),
        Formula::Biconditional(l, r) => {
            table_over(l, index, num_vars).biconditional(&table_over(r, index, num_vars))
        }
        Formula::Contradiction => DynTruthTable::contradiction(num_vars),
    }
}

/// Self-contained joint-satisfiability check — mirrors, but does not call,
/// logic-core's own `services::cheese::is_satisfiable_dynamic`, so this
/// test file compiles and runs unmodified against both pre-fix (b098f65,
/// where no such crate function exists yet) and post-fix code, giving an
/// apples-to-apples RED-then-GREEN comparison (see task-13-report.md for
/// the pre-fix run).
fn premises_satisfiable(premises: &[Formula]) -> bool {
    if premises.is_empty() {
        return true;
    }
    let atoms = atoms_of_all(premises);
    let num_vars = atoms.len().max(1) as u8;
    let index: std::collections::HashMap<&str, u8> =
        atoms.iter().enumerate().map(|(i, a)| (a.as_str(), i as u8)).collect();
    let combined = premises
        .iter()
        .fold(DynTruthTable::tautology(num_vars), |acc, f| acc.and(&table_over(f, &index, num_vars)));
    !combined.is_contradiction()
}

/// Ruling F / Critical 1 (Task 13): every candidate `golf_gate` accepts must
/// have jointly satisfiable premises and a non-tautologous conclusion —
/// otherwise any conclusion follows by a short indirect proof (inconsistent
/// premises), or the "theorem" is provable premise-free (tautologous
/// conclusion), neither being a real theorem regardless of its cone's par.
///
/// Probe effectively OFF, cheese and greedy at FULL default fidelity (team-
/// lead ruling, Task 13 review response): the semantic property under test
/// is guaranteed by stage 2 alone (unconditional — `Ok(())` is impossible
/// without passing it), and the prover stages are both irrelevant to it and
/// the dominant cost (a companion measurement doc,
/// `docs/superpowers/plans/2026-08-24-proof-golf-MEASUREMENTS.md` Task 8,
/// recorded ~60s of exhaustive RELEASE-mode search per accept at
/// `OptimalConfig::default()`'s 200k nodes for band 1 alone). Rather than
/// shrinking cheese/probe's budgets (which weakens what the test actually
/// exercises), `probe_off()` below sets `max_lines: 0` — `optimal_prove`'s
/// `for depth in 1..=cfg.max_lines` loop is then the empty range `1..=0`,
/// so it returns `NotProvedWithinBounds` without ever calling `search` once:
/// a true zero-cost no-op, not just a small budget. `freeze` stays `None`
/// (already the default — that stage is skipped unconditionally already).
fn probe_off_cfg() -> GateConfig {
    GateConfig { probe: OptimalConfig { max_lines: 0, max_nodes: 0, equiv_moves_per_state: 0 }, ..GateConfig::default() }
}

/// Shared band-soundness check: collect `accept_target` accepts (or give up
/// at `seed_cap`), asserting every one has satisfiable premises and a
/// non-tautologous conclusion. Returns `(accepts_found, violations)` so
/// callers can assert on both — used directly by three per-band `#[test]`s
/// below (team-lead ruling: no single test should exceed ~90s debug, so
/// bands are split rather than looped in one test) and, unmodified, by the
/// pre-fix RED check recorded in task-13-report.md (isolated against
/// b098f65 via `git stash`).
///
/// MUST FAIL against b098f65 (the review measured 43-52% plant-level
/// incidence, ungated; existing gates remove most tautologies but few
/// inconsistencies) — see task-13-report.md for the recorded pre-fix count.
fn check_band_semantically_sound(band: u8, accept_target: usize, seed_cap: u64) -> (usize, Vec<String>) {
    let cfg = probe_off_cfg();
    let spec = spec_for_band(band);
    let mut violations: Vec<String> = Vec::new();
    let mut accepts = 0usize;
    let mut seed = 0u64;
    while accepts < accept_target && seed < seed_cap {
        if let Ok(c) = plant(&spec, seed) {
            if golf_gate(&c, &cfg).is_ok() {
                accepts += 1;
                if !premises_satisfiable(&c.theorem.premises) {
                    violations.push(format!("band {band} seed {seed}: inconsistent premises {:?}", c.theorem.premises));
                }
                if is_tautology_dynamic(&c.theorem.conclusion) {
                    violations.push(format!("band {band} seed {seed}: tautologous conclusion {:?}", c.theorem.conclusion));
                }
            }
        }
        seed += 1;
    }
    (accepts, violations)
}

fn assert_band_semantically_sound(band: u8, accept_target: usize, seed_cap: u64) {
    let (accepts, violations) = check_band_semantically_sound(band, accept_target, seed_cap);
    assert!(accepts >= accept_target, "band {band}: only collected {accepts} accepts within the seed budget");
    assert!(
        violations.is_empty(),
        "{} semantic violation(s) across {accepts} accepts:\n{}",
        violations.len(),
        violations.join("\n")
    );
}

#[test]
fn accepted_candidates_are_semantically_sound_band1() {
    assert_band_semantically_sound(1, 30, 8_000);
}

#[test]
fn accepted_candidates_are_semantically_sound_band2() {
    assert_band_semantically_sound(2, 30, 8_000);
}

/// Band 3's `plant()` succeeds (lands in-band at all) for only ~1% of
/// seeds — a pre-existing, inherent cost of that band's wide/high par
/// window, unrelated to this fix (confirmed: with probe effectively off,
/// the remaining cost is almost entirely `plant()`'s own growth attempts,
/// not gate-side prover search). 10 accepts (not bands 1/2's 30) per
/// team-lead ruling, since 30 would need many tens of thousands of seeds;
/// 10 independent accepts is still a meaningful sample against the
/// review's 43-52% pre-fix incidence rate. NOT `#[ignore]`d: this reaches
/// 10 accepts within budget comfortably under ~90s debug — see
/// task-13-report.md for the measured wall time.
#[test]
fn accepted_candidates_are_semantically_sound_band3() {
    assert_band_semantically_sound(3, 10, 200_000);
}

/// Ruling F / Important 3 (Task 13): no derived line's formula may
/// byte-equal an earlier line accessible at that position (premises count
/// as accessible). Subsumes `no_duplicate_discharge` above (checks EVERY
/// derived line, not just discharges) — kept per the brief rather than
/// removed, since it's still valid, narrower coverage.
///
/// MUST FAIL against b098f65 (review: 9.5% / 12.3% / 17.8% incidence for
/// bands 1/2/3) — see task-13-report.md for the recorded pre-fix count.
///
/// 1000 seeds/band, not `no_duplicate_discharge`'s 2000: band 3's `plant()`
/// success rate is much lower than bands 1/2 (see
/// `accepted_candidates_are_semantically_sound_band3`'s doc comment), and "a
/// few thousand seeds" across all three bands combined (3000 total) still
/// meets the brief's own phrasing while fitting this file's "<2 min debug"
/// budget.
#[test]
fn no_accessible_duplicate_lines() {
    let mut checked = 0usize;
    let mut violations: Vec<String> = Vec::new();
    for band in 1..=3u8 {
        let spec = spec_for_band(band);
        for seed in 0..1000u64 {
            if let Ok(c) = plant(&spec, seed) {
                checked += 1;
                for line in &c.proof.lines {
                    if matches!(line.justification, Justification::Premise) {
                        continue;
                    }
                    let matches: Vec<usize> = c
                        .proof
                        .lines
                        .iter()
                        .filter(|earlier| {
                            earlier.line_number < line.line_number
                                && earlier.formula == line.formula
                                && c.proof.is_line_accessible(line.line_number, earlier.line_number)
                        })
                        .map(|earlier| earlier.line_number)
                        .collect();
                    if !matches.is_empty() {
                        violations.push(format!(
                            "band {band} seed {seed}: line {} duplicates accessible line(s) {matches:?}",
                            line.line_number
                        ));
                    }
                }
            }
        }
    }
    assert!(checked > 0, "no seeds produced a candidate to check");
    assert!(
        violations.is_empty(),
        "{} duplicate line(s) found across {checked} accepted candidates:\n{}",
        violations.len(),
        violations.join("\n")
    );
}

/// Dedicated regression test for Important 3's fourth mechanism (Task 13,
/// found empirically while verifying the review's three named mechanisms,
/// not itself named in the review): `grow_cp_subproof`'s and
/// `grow_ip_subproof`'s freshly-sampled ASSUMPTION formula was never checked
/// against the outer accessible pool — only their DISCHARGE was
/// (`formula_duplicates_pool`, née `discharge_duplicates_outer_pool`, was
/// only ever called on the discharge). A trivially simple assumption (a bare
/// atom) can coincidentally match an already-accessible line with zero
/// growth needed, giving an instant free re-citation duplicate the moment
/// the assumption is asserted.
///
/// First found via band 3's spec (subproofs 1, passes 2), seed 106: pre-fix,
/// that seed produced a CP assumption (bare `S`) at line 10 that
/// byte-duplicated line 3 (a costume-prologue line restoring premise `S.S`
/// back to the body's `S`), and a SECOND CP subproof's assumption again
/// duplicated the same line 3 at line 20 — confirmed via a direct proof dump
/// (see task-13-report.md) before this fix landed. Seed 106 itself is NOT
/// pinned here, deliberately: this same fix changes what seed 106 grows into
/// (post-fix it lands `OutOfBand` instead), which is the fix working as
/// intended, not a reason to keep chasing that exact seed. Scanning a seed
/// range at the same spec instead keeps the regression check meaningful
/// regardless of which specific seeds land in-band on any given version.
/// Assertion is general (any assumption, not just the original line 10/20/3
/// case), so it also guards the IP-assumption half of the same fix even
/// though seed 106 only ever exercised CP.
#[test]
fn subproof_assumption_never_duplicates_outer_pool() {
    let spec = spec_for_band(3);
    let mut checked = 0usize;
    let mut violations: Vec<String> = Vec::new();
    for seed in 0..500u64 {
        let Ok(c) = plant(&spec, seed) else { continue };
        checked += 1;
        for line in &c.proof.lines {
            if !matches!(line.justification, Justification::Assumption { .. }) {
                continue;
            }
            let matches: Vec<usize> = c
                .proof
                .lines
                .iter()
                .filter(|earlier| {
                    earlier.line_number < line.line_number
                        && earlier.formula == line.formula
                        && c.proof.is_line_accessible(line.line_number, earlier.line_number)
                })
                .map(|earlier| earlier.line_number)
                .collect();
            if !matches.is_empty() {
                violations.push(format!(
                    "seed {seed}: assumption at line {} duplicates accessible line(s) {matches:?}: {:?}",
                    line.line_number, line.formula
                ));
            }
        }
    }
    assert!(checked > 0, "no seeds produced a candidate to check");
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}
