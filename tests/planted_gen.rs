use logic_core::models::Justification;
use logic_core::services::{plant, PlantSpec};

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

#[test]
fn cone_has_no_dead_lines() {
    let spec = small_spec();
    let mut checked = 0;
    for seed in 0..50u64 {
        if let Ok(c) = plant(&spec, seed) {
            checked += 1;
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
