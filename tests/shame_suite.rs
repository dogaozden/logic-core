//! The shame suite: theorems that the tournament already served once and that
//! must never be served again. Each is pinned to its exact rejection reason
//! from `analyze_for_serving`'s nine-reason pipeline (see serve_filter.rs).
//! This file IS the CI gate from spec §5 -- if any future generator change
//! would let one of these four back through, `cargo test` fails.

use logic_core::models::rules::{EquivalenceRule, ProofTechnique};
use logic_core::models::*;
use logic_core::services::{analyze_for_serving, ProofVerifier, ServeAnalysis, ServeConfig, ServeRejection};

fn f(s: &str) -> Formula {
    Formula::parse(s).unwrap()
}

fn zero_premise_theorem(conclusion: &str) -> Theorem {
    Theorem {
        id: "test".to_string(),
        premises: vec![],
        conclusion: f(conclusion),
        difficulty: Difficulty::Medium,
        difficulty_value: 50,
        tier: None,
        theme: None,
        name: None,
        is_classic: false,
    }
}

// Exact served formulas — tournament ground truth. Do not reformat.
const ROUND9_HALLWAY: &str = "{P . {(R > S) . [(P > Q) . (Q > R)]}} > S";
const ROUND10_VACUOUS_DISJUNCT: &str =
    "{[(R > ~P) v (P > P)] . {S > [(Q v ~S) > ~S]}} > [(P > ~R) v (~P > ~P)]";
const ROUND11_IDENTITY_TRENCHCOAT: &str =
    "~{{[(~R v ~R) > R] . P} . [(S v S) > (Q v ~S)]} v {{[(R > ~R) > R] . P} . {~(Q v ~S) > ~(S v S)}}";
const ROUND3_EXCLUDED_MIDDLE: &str = "P v ~P";

fn serve(conclusion: &str) -> ServeAnalysis {
    analyze_for_serving(&zero_premise_theorem(conclusion), &ServeConfig::default())
}

#[test]
fn round9_rejected() {
    // CONTROLLER RULING (2026-08-15, amends brief): R9 legitimately has route
    // choices (branch_points=10, single_path=false -- the tournament record
    // shows two routes were played) AND its optimal search honestly Exhausts
    // its node cap, so analyze_for_serving reports OptimalUnknown rather than
    // Hallway. Empirically confirmed in T10 against the real provers.
    // NOTE: runs the real bounded-optimal search to exhaustion -- ~20-30s.
    assert_eq!(serve(ROUND9_HALLWAY).rejection, Some(ServeRejection::OptimalUnknown));
}

#[test]
fn round10_rejected() {
    assert_eq!(
        serve(ROUND10_VACUOUS_DISJUNCT).rejection,
        Some(ServeRejection::TautologousDisjunct)
    );
}

#[test]
fn round11_rejected() {
    assert_eq!(
        serve(ROUND11_IDENTITY_TRENCHCOAT).rejection,
        Some(ServeRejection::DisguisedIdentity { distance: 2 })
    );
}

#[test]
fn round3_rejected() {
    assert_eq!(
        serve(ROUND3_EXCLUDED_MIDDLE).rejection,
        Some(ServeRejection::TooShort { optimal: 4 })
    );
}

#[test]
fn round11_five_line_proof_validates() {
    let a = f("{[(~R v ~R) > R] . P} . [(S v S) > (Q v ~S)]");
    let a2 = f("{[(R > ~R) > R] . P} . [(S v S) > (Q v ~S)]");
    let b = f("{[(R > ~R) > R] . P} . {~(Q v ~S) > ~(S v S)}");
    let mut proof = Proof::new(zero_premise_theorem(ROUND11_IDENTITY_TRENCHCOAT));
    proof.open_subproof(a.clone(), ProofTechnique::ConditionalProof);
    proof.add_line(
        a2,
        Justification::Equivalence { rule: EquivalenceRule::Implication, line: 1 },
    );
    proof.add_line(
        b.clone(),
        Justification::Equivalence { rule: EquivalenceRule::Contraposition, line: 2 },
    );
    proof.close_subproof(
        Formula::Implies(Box::new(a), Box::new(b)),
        ProofTechnique::ConditionalProof,
    );
    proof.add_line(
        f(ROUND11_IDENTITY_TRENCHCOAT),
        Justification::Equivalence { rule: EquivalenceRule::Implication, line: 4 },
    );
    ProofVerifier::verify_proof(&mut proof);
    for line in &proof.lines {
        assert!(line.is_valid, "line {}: {:?}", line.line_number, line.validation_message);
    }
    assert!(proof.check_complete());
}
