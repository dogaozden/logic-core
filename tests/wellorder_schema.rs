//! Well-orderings (WellOrd), ordinals (Ord) as Def abbreviations, and the well-ordering schema.
//! Each accepted unfolding has a rejected twin: a weakened or reversed clause must not pass.

use logic_core::models::rules::first_order::definition_unfoldings;
use logic_core::models::rules::InferenceRule as R;
use logic_core::models::{Difficulty, Formula, Justification, Proof, Theorem};
use logic_core::services::ProofVerifier;

fn f(s: &str) -> Formula {
    Formula::parse(s).unwrap_or_else(|e| panic!("parse {s}: {e}"))
}

fn proof(premises: &[&str], conclusion: &str) -> Proof {
    Proof::new(Theorem::new(
        premises.iter().map(|p| f(p)).collect(),
        f(conclusion),
        Difficulty::Easy,
        None,
        Some("wellorder".to_string()),
    ))
}

fn step(p: &mut Proof, formula: &str, j: Justification) -> Result<(), String> {
    p.add_line(f(formula), j);
    let i = p.lines.len() - 1;
    let r = ProofVerifier::verify_line(&p.lines[i], p);
    if r.is_valid {
        p.lines[i].is_valid = true;
        Ok(())
    } else {
        p.lines.pop();
        Err(r.message.unwrap_or_default())
    }
}

fn simp(line: usize) -> Justification {
    Justification::Inference { rule: R::Simplification, lines: vec![line] }
}

fn mp(a: usize, b: usize) -> Justification {
    Justification::Inference { rule: R::ModusPonens, lines: vec![a, b] }
}

#[test]
fn wellorder_unfolds_to_subset_linearity_and_least_members() {
    let unfolded = definition_unfoldings(&f("WellOrd(r, a)"));
    assert_eq!(unfolded.len(), 1);
    let expected = f(
        "r ⊆ a × a . ∀u∀v((u ∈ a . v ∈ a) ⊃ (⟨u, v⟩ ∈ r ∨ u = v ∨ ⟨v, u⟩ ∈ r)) . \
         ∀k((k ⊆ a . ∃t(t ∈ k)) ⊃ ∃z(z ∈ k . ∀t(t ∈ k ⊃ (t = z ∨ ⟨z, t⟩ ∈ r))))",
    );
    assert!(unfolded[0].alpha_eq(&expected), "got {:?}", unfolded[0]);
}

#[test]
fn wellorder_linearity_needs_all_three_cases() {
    let unfolded = definition_unfoldings(&f("WellOrd(r, a)"));
    let weakened = f(
        "r ⊆ a × a . ∀u∀v((u ∈ a . v ∈ a) ⊃ (⟨u, v⟩ ∈ r ∨ ⟨v, u⟩ ∈ r)) . \
         ∀k((k ⊆ a . ∃t(t ∈ k)) ⊃ ∃z(z ∈ k . ∀t(t ∈ k ⊃ (t = z ∨ ⟨z, t⟩ ∈ r))))",
    );
    assert!(!unfolded[0].alpha_eq(&weakened), "dropping u = v must change the unfolding");
}

#[test]
fn least_member_of_a_subset_is_not_given_without_the_subset_premise() {
    let mut p = proof(&["WellOrd(r, a)", "∃t(t ∈ s)"], "∃z(z ∈ s . ∀t(t ∈ s ⊃ (t = z ∨ ⟨z, t⟩ ∈ r)))");
    step(
        &mut p,
        "r ⊆ a × a . ∀u∀v((u ∈ a . v ∈ a) ⊃ (⟨u, v⟩ ∈ r ∨ u = v ∨ ⟨v, u⟩ ∈ r)) . \
         ∀k((k ⊆ a . ∃t(t ∈ k)) ⊃ ∃z(z ∈ k . ∀t(t ∈ k ⊃ (t = z ∨ ⟨z, t⟩ ∈ r))))",
        Justification::Equivalence { rule: logic_core::models::rules::EquivalenceRule::Definition, line: 1 },
    )
    .unwrap();
    step(
        &mut p,
        "∀k((k ⊆ a . ∃t(t ∈ k)) ⊃ ∃z(z ∈ k . ∀t(t ∈ k ⊃ (t = z ∨ ⟨z, t⟩ ∈ r))))",
        simp(3),
    )
    .unwrap();
    step(
        &mut p,
        "(s ⊆ a . ∃t(t ∈ s)) ⊃ ∃z(z ∈ s . ∀t(t ∈ s ⊃ (t = z ∨ ⟨z, t⟩ ∈ r)))",
        Justification::Inference { rule: R::UniversalElimination, lines: vec![4] },
    )
    .unwrap();
    let rejected = step(
        &mut p,
        "∃z(z ∈ s . ∀t(t ∈ s ⊃ (t = z ∨ ⟨z, t⟩ ∈ r)))",
        mp(5, 2),
    );
    assert!(rejected.is_err(), "MP needs s ⊆ a as the antecedent; line 2 is only ∃t(t ∈ s)");
}

#[test]
fn ordinal_unfolds_to_transitivity_linearity_and_minimal_members() {
    let unfolded = definition_unfoldings(&f("Ord(a)"));
    assert_eq!(unfolded.len(), 1);
    let expected = f(
        "∀x(x ∈ a ⊃ x ⊆ a) . \
         ∀u∀v((u ∈ a . v ∈ a) ⊃ (u ∈ v ∨ u = v ∨ v ∈ u)) . \
         ∀s((s ⊆ a . ∃t(t ∈ s)) ⊃ ∃l(l ∈ s . ∀t(t ∈ s ⊃ ~(t ∈ l))))",
    );
    assert!(unfolded[0].alpha_eq(&expected), "got {:?}", unfolded[0]);
}

#[test]
fn ordinal_minimal_member_is_not_a_maximal_one() {
    let unfolded = definition_unfoldings(&f("Ord(a)"));
    let reversed = f(
        "∀x(x ∈ a ⊃ x ⊆ a) . \
         ∀u∀v((u ∈ a . v ∈ a) ⊃ (u ∈ v ∨ u = v ∨ v ∈ u)) . \
         ∀s((s ⊆ a . ∃t(t ∈ s)) ⊃ ∃l(l ∈ s . ∀t(t ∈ s ⊃ ~(l ∈ t))))",
    );
    assert!(!unfolded[0].alpha_eq(&reversed), "the least member has no element of s below it, not the reverse");
}
