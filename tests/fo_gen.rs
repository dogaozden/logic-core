//! The monadic first-order generator: every theorem comes with its own proof, which the
//! verifier accepts; trivial theorems are rejected; every difficulty band is reachable.

use std::time::Instant;

use logic_core::models::{Difficulty, Formula, Proof};
use logic_core::services::{generate_first_order, plant_first_order, regenerate_first_order, FoGenError, FoSpec, ProofVerifier};

const LEVELS: [Difficulty; 4] = [Difficulty::Easy, Difficulty::Medium, Difficulty::Hard, Difficulty::Expert];

/// Verify the generator's proof from scratch: fresh validity flags, every line re-checked.
fn reverify(proof: &Proof) -> Result<(), String> {
    let mut p = proof.clone();
    for l in p.lines.iter_mut() {
        l.is_valid = true;
        l.validation_message = None;
    }
    ProofVerifier::verify_proof(&mut p);
    if let Some(bad) = p.lines.iter().find(|l| !l.is_valid) {
        return Err(format!("line {}: {:?}", bad.line_number, bad.validation_message));
    }
    if !p.check_complete() {
        return Err("incomplete".into());
    }
    Ok(())
}

fn is_trivial(premises: &[Formula], conclusion: &Formula) -> bool {
    premises.iter().any(|p| {
        p.alpha_eq(conclusion)
            || matches!(p, Formula::ForAll(v, body)
                if matches!(logic_core::models::rules::first_order::instance_of(v, body, conclusion), Ok(Some(_))))
    })
}

#[test]
fn two_hundred_seeds_verify_and_fill_every_band() {
    let started = Instant::now();
    let mut histogram = [0usize; 4];
    for seed in 0..200u64 {
        let level = LEVELS[(seed % 4) as usize];
        let c = generate_first_order(level, seed * 7919).unwrap_or_else(|e| panic!("seed {seed} {level:?}: {e:?}"));
        reverify(&c.proof).unwrap_or_else(|e| panic!("seed {seed}: {e}\n{:#?}", c.proof.lines.iter().map(|l| format!("{} {} {}", l.line_number, l.formula.display_string(), l.justification.display_string())).collect::<Vec<_>>()));
        assert!(!is_trivial(&c.theorem.premises, &c.theorem.conclusion), "seed {seed}: trivial theorem");
        assert_eq!(c.score.difficulty(), Some(level), "seed {seed}: score {} outside {level:?}", c.score.total());
        assert!(c.proof.lines.len() - c.theorem.premises.len() >= 2);
        histogram[LEVELS.iter().position(|l| *l == level).unwrap()] += 1;
    }
    let elapsed = started.elapsed();
    eprintln!("histogram {histogram:?} in {elapsed:?}");
    assert!(histogram.iter().all(|&n| n > 0));
    // The 2 s budget is for the optimized build the trainer ships (wasm release); run
    // `cargo test --release --test fo_gen` to check it. Debug builds only get a loose bound.
    let budget = if cfg!(debug_assertions) { 60.0 } else { 2.0 };
    assert!(elapsed.as_secs_f64() < budget, "200 theorems took {elapsed:?}");
}

#[test]
fn raw_seeds_never_produce_an_invalid_proof() {
    for level in LEVELS {
        let spec = FoSpec::for_difficulty(level);
        for seed in 0..300 {
            match plant_first_order(&spec, seed) {
                Ok(c) => reverify(&c.proof).unwrap_or_else(|e| panic!("{level:?} seed {seed}: {e}")),
                Err(FoGenError::NoConclusion) | Err(FoGenError::Unsatisfiable) => {}
                Err(e) => panic!("{level:?} seed {seed}: {e:?}"),
            }
        }
    }
}

#[test]
fn ids_regenerate_the_same_theorem() {
    for (k, level) in LEVELS.into_iter().enumerate() {
        let c = generate_first_order(level, 4242 + k as u64).unwrap();
        let again = regenerate_first_order(&c.theorem.id).unwrap();
        assert_eq!(again.theorem.premises, c.theorem.premises);
        assert_eq!(again.theorem.conclusion, c.theorem.conclusion);
        assert!(!c.hint().is_empty());
    }
    assert!(regenerate_first_order("halmos-0-1").is_err());
}

#[test]
fn harder_levels_use_existential_subproofs() {
    let with_ee = (0..40u64)
        .filter_map(|s| generate_first_order(Difficulty::Hard, s * 31).ok())
        .filter(|c| c.proof.lines.iter().any(|l| l.justification.display_string().starts_with("∃E")))
        .count();
    assert!(with_ee > 0);
}

#[test]
fn inconsistent_premises_are_detected() {
    let f = |s: &str| Formula::parse(s).unwrap();
    assert!(!logic_core::services::monadic_satisfiable(&[f("∀x(F(x) ⊃ G(x))"), f("F(a)"), f("~G(a)")]));
    assert!(!logic_core::services::monadic_satisfiable(&[f("∀x ~F(x)"), f("∃x F(x)")]));
    assert!(logic_core::services::monadic_satisfiable(&[f("∀x(F(x) ⊃ G(x))"), f("∃x F(x)"), f("~G(a)")]));
}

/// `cargo test --test fo_gen samples -- --ignored --nocapture` prints a few theorems per level.
#[test]
#[ignore]
fn samples() {
    for level in LEVELS {
        let mut tried = 0;
        for k in 0..6u64 {
            let start = 1000 + k * 977;
            let c = generate_first_order(level, start).unwrap();
            tried += c.seed - start + 1;
            let premises: Vec<String> = c.theorem.premises.iter().map(|p| p.display_string()).collect();
            println!("{level:?} score {} [{}] ⊢ {}", c.score.total(), premises.join(", "), c.theorem.conclusion.display_string());
            if k == 0 {
                for l in &c.proof.lines {
                    println!("    {:>2} {}{}   {}", l.line_number, "| ".repeat(l.depth), l.formula.display_string(), l.justification.display_string());
                }
                println!("    hint: {}", c.hint());
            }
        }
        println!("  seeds tried per theorem: {:.1}", tried as f64 / 6.0);
    }
}

/// Yield diagnostics: the best score each seed reaches with the band opened up.
#[test]
#[ignore]
fn band_yield() {
    for level in LEVELS {
        let mut spec = FoSpec::for_difficulty(level);
        let band = spec.band;
        spec.band = (3, 100);
        let mut hist = std::collections::BTreeMap::new();
        let mut fails = 0;
        for seed in 0..200 {
            match plant_first_order(&spec, seed) {
                Ok(c) => *hist.entry(c.score.total()).or_insert(0) += 1,
                Err(_) => fails += 1,
            }
        }
        println!("{level:?} band {band:?}: best-score histogram {hist:?}, failures {fails}");
    }
}
