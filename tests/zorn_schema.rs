//! Zorn's lemma as a premise schema, the `Chain` abbreviation it uses, and the function
//! terms the Arithmetic track already relies on. Each accepted step has a rejected twin.

use logic_core::models::rules::first_order::definition_unfoldings;
use logic_core::models::rules::InferenceRule as R;
use logic_core::models::{Difficulty, Formula, Justification, Proof, Theorem};
use logic_core::services::ProofVerifier;

fn f(s: &str) -> Formula {
    Formula::parse(s).unwrap_or_else(|e| panic!("parse {s}: {e}"))
}

fn zorn() -> &'static str {
    "∀x((∀c((c ⊆ x . Chain(c)) ⊃ ⋃c ∈ x)) ⊃ ∃m(m ∈ x . ∀y((y ∈ x . m ⊆ y) ⊃ m = y)))"
}

fn chain_hypothesis() -> &'static str {
    "∀c((c ⊆ a . Chain(c)) ⊃ ⋃c ∈ a)"
}

fn maximal() -> &'static str {
    "∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y))"
}

fn proof(premises: &[&str], conclusion: &str) -> Proof {
    Proof::new(Theorem::new(
        premises.iter().map(|p| f(p)).collect(),
        f(conclusion),
        Difficulty::Easy,
        None,
        Some("zorn".to_string()),
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

fn mp(a: usize, b: usize) -> Justification {
    Justification::Inference { rule: R::ModusPonens, lines: vec![a, b] }
}

fn forall_e(line: usize) -> Justification {
    Justification::Inference { rule: R::UniversalElimination, lines: vec![line] }
}

#[test]
fn chain_unfolds_to_pairwise_comparability() {
    let chain = f("Chain(c)");
    let unfolded = definition_unfoldings(&chain);
    assert_eq!(unfolded.len(), 1);
    let expected = f("∀x∀y((x ∈ c . y ∈ c) ⊃ (x ⊆ y ∨ y ⊆ x))");
    assert!(unfolded[0].alpha_eq(&expected), "got {:?}", unfolded[0]);
}

#[test]
fn chain_is_not_membership_in_a_chain() {
    let unfolded = definition_unfoldings(&f("Chain(c)"));
    let wrong = f("∀x∀y((x ∈ c . y ∈ c) ⊃ (x ∈ y ∨ y ∈ x))");
    assert!(!unfolded[0].alpha_eq(&wrong));
}

#[test]
fn zorn_instance_with_chain_hypothesis_gives_a_maximal_member() {
    let mut p = proof(&[zorn(), chain_hypothesis()], maximal());
    step(&mut p, "(∀c((c ⊆ a . Chain(c)) ⊃ ⋃c ∈ a)) ⊃ ∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y))", forall_e(1))
        .expect("∀E on Zorn's schema at a is valid");
    step(&mut p, maximal(), mp(3, 2)).expect("MP with the chain hypothesis");
    assert!(p.check_complete());
}

#[test]
fn zorn_without_the_chain_hypothesis_is_rejected() {
    let mut p = proof(&[zorn()], maximal());
    step(&mut p, "(∀c((c ⊆ a . Chain(c)) ⊃ ⋃c ∈ a)) ⊃ ∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y))", forall_e(1))
        .expect("the instance itself is fine");
    assert!(step(&mut p, maximal(), mp(3, 1)).is_err(), "MP needs the antecedent, not the schema");
}

#[test]
fn zorn_conclusion_with_reversed_inclusion_is_rejected() {
    let mut p = proof(&[zorn(), chain_hypothesis()], "∃m(m ∈ a . ∀y((y ∈ a . y ⊆ m) ⊃ m = y))");
    step(&mut p, "(∀c((c ⊆ a . Chain(c)) ⊃ ⋃c ∈ a)) ⊃ ∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y))", forall_e(1))
        .expect("the instance itself is fine");
    assert!(
        step(&mut p, "∃m(m ∈ a . ∀y((y ∈ a . y ⊆ m) ⊃ m = y))", mp(3, 2)).is_err(),
        "the schema gives m ⊆ y, not y ⊆ m"
    );
}

#[test]
fn zorn_instance_on_another_family_does_not_discharge_the_chain_hypothesis() {
    let mut p = proof(&[zorn(), chain_hypothesis()], maximal());
    step(&mut p, "(∀c((c ⊆ b . Chain(c)) ⊃ ⋃c ∈ b)) ⊃ ∃m(m ∈ b . ∀y((y ∈ b . m ⊆ y) ⊃ m = y))", forall_e(1))
        .expect("∀E at b is a valid instance");
    assert!(
        step(&mut p, "∃m(m ∈ b . ∀y((y ∈ b . m ⊆ y) ⊃ m = y))", mp(3, 2)).is_err(),
        "the hypothesis is about a, so MP against the b instance must fail"
    );
}

#[test]
fn function_terms_round_trip_through_parse_and_display() {
    for s in ["p(a, ∅) = a", "p(a, b ∪ {b}) = p(a, b) ∪ {p(a, b)}", "f(g(a), b) ∈ c"] {
        let once = f(s);
        let again = f(&once.display_string());
        assert_eq!(once, again, "round trip {s}");
    }
}

#[test]
fn an_existential_does_not_give_its_witness_as_a_conjunct() {
    let mut p = proof(&[zorn(), chain_hypothesis()], maximal());
    step(&mut p, "(∀c((c ⊆ a . Chain(c)) ⊃ ⋃c ∈ a)) ⊃ ∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y))", forall_e(1)).unwrap();
    step(&mut p, maximal(), mp(3, 2)).unwrap();
    assert!(
        step(&mut p, "m ∈ a", Justification::Inference { rule: R::Simplification, lines: vec![4] }).is_err(),
        "Simp needs a conjunction; the ∃ line is not one"
    );
}
