use logic_core::models::*;
use logic_core::models::rules::{ProofTechnique, EquivalenceRule};
use logic_core::services::ProofVerifier;

fn f(s: &str) -> Formula { Formula::parse(s).unwrap() }

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

#[test]
fn round3_cp_1_1_proof_validates() {
    let mut proof = Proof::new(zero_premise_theorem("P v ~P"));
    proof.open_subproof(f("~P"), ProofTechnique::ConditionalProof);          // 1. ~P  ACP
    proof.close_subproof(f("~P > ~P"), ProofTechnique::ConditionalProof);    // 2. CP 1-1
    proof.add_line(f("~~P v ~P"), Justification::Equivalence {              // 3. Impl 2
        rule: EquivalenceRule::Implication, line: 2 });
    proof.add_line(f("P v ~P"), Justification::Equivalence {                // 4. DN 3
        rule: EquivalenceRule::DoubleNegation, line: 3 });
    ProofVerifier::verify_proof(&mut proof);
    for line in &proof.lines {
        assert!(line.is_valid, "line {} invalid: {:?}", line.line_number, line.validation_message);
    }
    assert!(proof.check_complete());
}
