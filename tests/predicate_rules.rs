//! Predicate logic, identity and set-theory definitions: every rule accepts its correct uses
//! and rejects the classic bad moves.

use logic_core::models::rules::{EquivalenceRule as Eq, InferenceRule as R, ProofTechnique as T};
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
        Some("test".to_string()),
    ))
}

/// Add a line and verify it; returns the error message when rejected (and drops the line).
fn step(p: &mut Proof, formula: &str, j: Justification) -> Result<(), String> {
    p.add_line(f(formula), j);
    check_last(p)
}

fn check_last(p: &mut Proof) -> Result<(), String> {
    let i = p.lines.len() - 1;
    let r = ProofVerifier::verify_line(&p.lines[i], p);
    p.lines[i].is_valid = r.is_valid;
    p.lines[i].validation_message = r.message.clone();
    if r.is_valid {
        Ok(())
    } else {
        p.remove_last_line();
        Err(r.message.unwrap_or_default())
    }
}

fn inf(p: &mut Proof, formula: &str, rule: R, lines: &[usize]) -> Result<(), String> {
    step(p, formula, Justification::Inference { rule, lines: lines.to_vec() })
}

fn eqv(p: &mut Proof, formula: &str, rule: Eq, line: usize) -> Result<(), String> {
    step(p, formula, Justification::Equivalence { rule, line })
}

fn assume(p: &mut Proof, formula: &str, t: T) -> Result<(), String> {
    p.open_subproof(f(formula), t);
    check_last(p)
}

fn close(p: &mut Proof, formula: &str, t: T) -> Result<(), String> {
    match p.close_subproof(f(formula), t) {
        None => Err("could not close".to_string()),
        Some(_) => {
            let i = p.lines.len() - 1;
            let r = ProofVerifier::verify_line(&p.lines[i], p);
            p.lines[i].is_valid = r.is_valid;
            if r.is_valid {
                Ok(())
            } else {
                Err(r.message.unwrap_or_default())
            }
        }
    }
}

fn complete(p: &mut Proof) -> bool {
    p.check_complete()
}

#[test]
fn parse_and_display_round_trip() {
    for s in [
        "∀x(F(x) ⊃ G(x))",
        "∃x F(x)",
        "∀x ∃y R(x, y)",
        "∀x ~F(x)",
        "~∀x F(x)",
        "a = b",
        "a ≠ b",
        "a ∈ b ∪ c",
        "a ∉ ∅",
        "∀x(x ∈ a ⊃ x ∈ a ∪ b)",
        "{a, b} = {b, a}",
        "a ∈ {a}",
        "⟨a, b⟩ = {{a}, {a, b}}",
        "a ∈ ℘(b)",
        "a ∈ ⋃b",
        "(a ∪ b) ∩ c ⊆ a ∪ (b ∩ c)",
        "∀x(x ∈ a ≡ x ∈ b) ⊃ a = b",
        "∀x ∀y(∀z(z ∈ x ≡ z ∈ y) ⊃ x = y)",
        "∃y ∀x(x ∉ y)",
        "f(a) = b",
        "{∀x[F(x) . (G(x) ∨ H(x))] ⊃ (P ⊃ Q)} . R",
    ] {
        let parsed = f(s);
        let shown = parsed.display_string();
        assert_eq!(f(&shown), parsed, "display of {s} is {shown}, which parses differently");
        assert_eq!(f(&parsed.ascii_string()), parsed, "ascii of {s}");
        assert_eq!(f(&parsed.ascii_string_bracketed()), parsed, "bracketed ascii of {s}");
    }
}

#[test]
fn ascii_spellings() {
    assert_eq!(f("\\A x (F(x) -> G(x))"), f("∀x(F(x) ⊃ G(x))"));
    assert_eq!(f("\\E y R(a, y)"), f("∃y R(a, y)"));
    assert_eq!(f("(x)(F(x) > G(x))"), f("∀x(F(x) ⊃ G(x))"));
    assert_eq!(f("(∃x)F(x)"), f("∃x F(x)"));
    assert_eq!(f("a \\in b \\cup c"), f("a ∈ b ∪ c"));
    assert_eq!(f("a != b"), f("~(a = b)"));
    assert_eq!(f("x \\notin \\empty"), f("~(x ∈ ∅)"));
    assert_eq!(f("{} = \\empty"), f("∅ = ∅"));
}

#[test]
fn propositional_parsing_unchanged() {
    // Lowercase sentence letters, grouping braces and (p)-style parentheses keep their old meaning.
    assert_eq!(f("p ⊃ q"), Formula::Implies(Box::new(Formula::Atom("p".into())), Box::new(Formula::Atom("q".into()))));
    assert_eq!(f("(p) ⊃ q"), f("p ⊃ q"));
    assert_eq!(f("{p . q} v r"), f("(p . q) ∨ r"));
    assert_eq!(f("a => b"), f("a ⊃ b"));
    assert_eq!(f("Rain > Wet"), Formula::Implies(Box::new(Formula::Atom("Rain".into())), Box::new(Formula::Atom("Wet".into()))));
    assert!(Formula::parse("P(Q)").is_err());
}

#[test]
fn universal_elimination() {
    let mut p = proof(&["∀x(F(x) ⊃ G(x))", "∀x ∃y R(x, y)"], "G(a)");
    inf(&mut p, "F(a) ⊃ G(a)", R::UniversalElimination, &[1]).unwrap();
    inf(&mut p, "∃y R(b, y)", R::UniversalElimination, &[2]).unwrap();
    // Not an instance: different terms for the same variable.
    assert!(inf(&mut p, "F(a) ⊃ G(b)", R::UniversalElimination, &[1]).is_err());
    // Capture: putting y for x lands under ∃y.
    let e = inf(&mut p, "∃y R(y, y)", R::UniversalElimination, &[2]).unwrap_err();
    assert!(e.contains("captured"), "{e}");
    // ∀E needs a universal line.
    assert!(inf(&mut p, "F(a)", R::UniversalElimination, &[3]).is_err());
}

#[test]
fn existential_introduction() {
    let mut p = proof(&["R(a, a)", "R(a, b)"], "∃x R(x, a)");
    inf(&mut p, "∃x R(x, a)", R::ExistentialIntroduction, &[1]).unwrap();
    inf(&mut p, "∃x R(x, x)", R::ExistentialIntroduction, &[1]).unwrap();
    assert!(inf(&mut p, "∃x R(x, x)", R::ExistentialIntroduction, &[2]).is_err());
    assert!(inf(&mut p, "∀x R(x, a)", R::ExistentialIntroduction, &[1]).is_err());
    assert!(complete(&mut p));
}

#[test]
fn universal_introduction_classic_proof() {
    // ∀x(F ⊃ G), ∀x F ⊢ ∀x G
    let mut p = proof(&["∀x(F(x) ⊃ G(x))", "∀x F(x)"], "∀x G(x)");
    inf(&mut p, "F(a) ⊃ G(a)", R::UniversalElimination, &[1]).unwrap();
    inf(&mut p, "F(a)", R::UniversalElimination, &[2]).unwrap();
    inf(&mut p, "G(a)", R::ModusPonens, &[3, 4]).unwrap();
    inf(&mut p, "∀x G(x)", R::UniversalIntroduction, &[5]).unwrap();
    assert!(complete(&mut p));
    // Bound-variable names are free to differ from the goal's.
    let mut q = proof(&["∀x F(x)"], "∀x F(x)");
    inf(&mut q, "F(a)", R::UniversalElimination, &[1]).unwrap();
    inf(&mut q, "∀y F(y)", R::UniversalIntroduction, &[2]).unwrap();
    assert!(complete(&mut q));
}

#[test]
fn universal_introduction_rejects_name_in_premise() {
    let mut p = proof(&["F(a)"], "∀x F(x)");
    let e = inf(&mut p, "∀x F(x)", R::UniversalIntroduction, &[1]).unwrap_err();
    assert!(e.contains("premise"), "{e}");
}

#[test]
fn universal_introduction_rejects_name_in_open_assumption() {
    let mut p = proof(&[], "F(a) ⊃ ∀x F(x)");
    assume(&mut p, "F(a)", T::ConditionalProof).unwrap();
    let e = inf(&mut p, "∀x F(x)", R::UniversalIntroduction, &[1]).unwrap_err();
    assert!(e.contains("open assumption"), "{e}");
}

#[test]
fn universal_introduction_after_assumption_discharged() {
    // ⊢ ∀x(F(x) ⊃ F(x)): the CP assumption on a is closed before ∀I.
    let mut p = proof(&[], "∀x(F(x) ⊃ F(x))");
    assume(&mut p, "F(a)", T::ConditionalProof).unwrap();
    close(&mut p, "F(a) ⊃ F(a)", T::ConditionalProof).unwrap();
    inf(&mut p, "∀x(F(x) ⊃ F(x))", R::UniversalIntroduction, &[2]).unwrap();
    assert!(complete(&mut p));
}

#[test]
fn universal_introduction_rejects_partial_generalization() {
    let mut p = proof(&["∀x R(x, x)"], "∀x R(x, x)");
    inf(&mut p, "R(a, a)", R::UniversalElimination, &[1]).unwrap();
    let e = inf(&mut p, "∀x R(x, a)", R::UniversalIntroduction, &[2]).unwrap_err();
    assert!(e.contains("every occurrence"), "{e}");
    inf(&mut p, "∀x R(x, x)", R::UniversalIntroduction, &[2]).unwrap();
}

#[test]
fn existential_elimination_classic_proof() {
    // ∃x F, ∀x(F ⊃ G) ⊢ ∃x G
    let mut p = proof(&["∃x F(x)", "∀x(F(x) ⊃ G(x))"], "∃x G(x)");
    assume(&mut p, "F(a)", T::ExistentialElimination).unwrap();
    inf(&mut p, "F(a) ⊃ G(a)", R::UniversalElimination, &[2]).unwrap();
    inf(&mut p, "G(a)", R::ModusPonens, &[4, 3]).unwrap();
    inf(&mut p, "∃x G(x)", R::ExistentialIntroduction, &[5]).unwrap();
    close(&mut p, "∃x G(x)", T::ExistentialElimination).unwrap();
    assert!(matches!(
        p.lines[6].justification,
        Justification::ExistentialElimination { existential_line: 1, subproof_start: 3, subproof_end: 6 }
    ));
    assert!(complete(&mut p));
}

#[test]
fn existential_elimination_rejects_escape() {
    let mut p = proof(&["∃x F(x)"], "F(a)");
    assume(&mut p, "F(a)", T::ExistentialElimination).unwrap();
    let e = close(&mut p, "F(a)", T::ExistentialElimination).unwrap_err();
    assert!(e.contains("escapes"), "{e}");
}

#[test]
fn existential_elimination_rejects_old_name() {
    let mut p = proof(&["G(a)", "∃x F(x)"], "∃x(F(x) . G(x))");
    let e = assume(&mut p, "F(a)", T::ExistentialElimination).unwrap_err();
    assert!(e.contains("premise"), "{e}");
    // A name already in the existential line is not new either.
    let mut q = proof(&["∃x R(x, a)"], "∃x R(x, x)");
    assert!(assume(&mut q, "R(a, a)", T::ExistentialElimination).is_err());
    // And the assumption must be an instance of an accessible ∃ line at all.
    let mut r = proof(&["∃x F(x)"], "∃x F(x)");
    assert!(assume(&mut r, "G(b)", T::ExistentialElimination).is_err());
}

#[test]
fn universal_introduction_on_existential_witness_rejected() {
    // ∃x F(x) ⊬ ∀x F(x): inside the ∃E subproof the witness is in an open assumption.
    let mut p = proof(&["∃x F(x)"], "∀x F(x)");
    assume(&mut p, "F(a)", T::ExistentialElimination).unwrap();
    let e = inf(&mut p, "∀x F(x)", R::UniversalIntroduction, &[2]).unwrap_err();
    assert!(e.contains("open assumption"), "{e}");
}

#[test]
fn identity_rules() {
    let mut p = proof(&["a = b", "F(a)", "∀b R(a, b)"], "b = a");
    inf(&mut p, "F(b)", R::IdentityElimination, &[1, 2]).unwrap();
    inf(&mut p, "a = a", R::IdentityIntroduction, &[]).unwrap();
    inf(&mut p, "b = a", R::IdentityElimination, &[1, 5]).unwrap();
    assert!(complete(&mut p));
    assert!(inf(&mut p, "a = b", R::IdentityIntroduction, &[]).is_err());
    assert!(inf(&mut p, "F(c)", R::IdentityElimination, &[1, 2]).is_err());
    // Capture: replacing a by b under ∀b changes the meaning.
    assert!(inf(&mut p, "∀b R(b, b)", R::IdentityElimination, &[1, 3]).is_err());
}

#[test]
fn quantifier_negation() {
    let mut p = proof(&["~∀x F(x)", "~∃x G(x)"], "∃x ~F(x)");
    eqv(&mut p, "∃x ~F(x)", Eq::QuantifierNegation, 1).unwrap();
    eqv(&mut p, "∀x ~G(x)", Eq::QuantifierNegation, 2).unwrap();
    eqv(&mut p, "~∀x F(x)", Eq::QuantifierNegation, 3).unwrap();
    eqv(&mut p, "∃y ~F(y)", Eq::QuantifierNegation, 1).unwrap();
    assert!(eqv(&mut p, "∀x ~F(x)", Eq::QuantifierNegation, 1).is_err());
    assert!(complete(&mut p));
}

#[test]
fn equivalence_rules_inside_quantifiers() {
    let mut p = proof(&["∀x ~(F(x) . G(x))"], "∀x(~F(x) ∨ ~G(x))");
    eqv(&mut p, "∀x(~F(x) ∨ ~G(x))", Eq::DeMorgan, 1).unwrap();
    assert!(complete(&mut p));
}

#[test]
fn definitions_unfold_and_fold() {
    let mut p = proof(&["a ⊆ b", "c ∈ a ∪ b", "c ∈ ℘(a)", "d ∈ ∅", "⟨a, b⟩ = c"], "c ∈ a ∨ c ∈ b");
    eqv(&mut p, "∀y(y ∈ a ⊃ y ∈ b)", Eq::Definition, 1).unwrap();
    eqv(&mut p, "a ⊆ b", Eq::Definition, 6).unwrap();
    eqv(&mut p, "c ∈ a ∨ c ∈ b", Eq::Definition, 2).unwrap();
    eqv(&mut p, "c ∈ a ∪ b", Eq::Definition, 8).unwrap();
    eqv(&mut p, "c ⊆ a", Eq::Definition, 3).unwrap();
    eqv(&mut p, "⊥", Eq::Definition, 4).unwrap();
    eqv(&mut p, "{{a}, {a, b}} = c", Eq::Definition, 5).unwrap();
    // A wrong unfolding, and a capturing variable choice, are rejected.
    assert!(eqv(&mut p, "c ∈ a . c ∈ b", Eq::Definition, 2).is_err());
    let mut q = proof(&["a ⊆ x"], "a ⊆ x");
    assert!(eqv(&mut q, "∀x(x ∈ a ⊃ x ∈ x)", Eq::Definition, 1).is_err());
    eqv(&mut q, "∀y(y ∈ a ⊃ y ∈ x)", Eq::Definition, 1).unwrap();
}

#[test]
fn first_order_rules_stay_out_of_propositional_lists() {
    assert!(R::all().iter().all(|r| !r.is_first_order()));
    assert!(Eq::all().iter().all(|r| !r.is_first_order()));
    assert_eq!(R::all().len(), 9);
    assert_eq!(Eq::all().len(), 10);
}
