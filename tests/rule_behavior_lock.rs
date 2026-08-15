use logic_core::models::Formula;
use logic_core::models::rules::{InferenceRule, EquivalenceRule};

fn f(s: &str) -> Formula { Formula::parse(s).unwrap() }

fn equiv_reaches(rule: EquivalenceRule, from: &str, to: &str) -> bool {
    rule.equivalent_forms(&f(from)).contains(&f(to))
}

#[test]
fn add_house_rule_both_sides() {
    // house rule: from p, both p∨q and q∨p — verifier extracts q from either side
    assert!(InferenceRule::Addition.verify(&[&f("P")], &f("P v Q"), Some(&f("Q"))));
    assert!(InferenceRule::Addition.verify(&[&f("P")], &f("Q v P"), Some(&f("Q"))));
}

#[test]
fn ds_both_directions() {
    assert!(InferenceRule::DisjunctiveSyllogism.verify(&[&f("P v Q"), &f("~P")], &f("Q"), None));
    assert!(InferenceRule::DisjunctiveSyllogism.verify(&[&f("P v Q"), &f("~Q")], &f("P"), None));
}

#[test]
fn simp_both_conjuncts() {
    assert!(InferenceRule::Simplification.verify(&[&f("P . Q")], &f("P"), None));
    assert!(InferenceRule::Simplification.verify(&[&f("P . Q")], &f("Q"), None));
}

#[test]
fn premise_order_agnostic() {
    assert!(InferenceRule::ModusPonens.verify(&[&f("P"), &f("P > Q")], &f("Q"), None));
    assert!(InferenceRule::ModusTollens.verify(&[&f("~Q"), &f("P > Q")], &f("~P"), None));
    assert!(InferenceRule::HypotheticalSyllogism.verify(&[&f("Q > R"), &f("P > Q")], &f("P > R"), None));
}

#[test]
fn comm_both_connectives() {
    assert!(equiv_reaches(EquivalenceRule::Commutation, "P v Q", "Q v P"));
    assert!(equiv_reaches(EquivalenceRule::Commutation, "P . Q", "Q . P"));
}

#[test]
fn assoc_both_connectives() {
    assert!(equiv_reaches(EquivalenceRule::Association, "P v (Q v R)", "(P v Q) v R"));
    assert!(equiv_reaches(EquivalenceRule::Association, "P . (Q . R)", "(P . Q) . R"));
}

#[test]
fn demorgan_both_forms_both_directions() {
    assert!(equiv_reaches(EquivalenceRule::DeMorgan, "~(P . Q)", "~P v ~Q"));
    assert!(equiv_reaches(EquivalenceRule::DeMorgan, "~P v ~Q", "~(P . Q)"));
    assert!(equiv_reaches(EquivalenceRule::DeMorgan, "~(P v Q)", "~P . ~Q"));
    assert!(equiv_reaches(EquivalenceRule::DeMorgan, "~P . ~Q", "~(P v Q)"));
}

#[test]
fn dist_both_forms() {
    assert!(equiv_reaches(EquivalenceRule::Distribution, "P . (Q v R)", "(P . Q) v (P . R)"));
    assert!(equiv_reaches(EquivalenceRule::Distribution, "P v (Q . R)", "(P v Q) . (P v R)"));
}

#[test]
fn impl_contra_exp_taut_dn_bidirectional() {
    assert!(equiv_reaches(EquivalenceRule::Implication, "P > Q", "~P v Q"));
    assert!(equiv_reaches(EquivalenceRule::Implication, "~P v Q", "P > Q"));
    assert!(equiv_reaches(EquivalenceRule::Contraposition, "P > Q", "~Q > ~P"));
    assert!(equiv_reaches(EquivalenceRule::Exportation, "(P . Q) > R", "P > (Q > R)"));
    assert!(equiv_reaches(EquivalenceRule::Exportation, "P > (Q > R)", "(P . Q) > R"));
    assert!(equiv_reaches(EquivalenceRule::Tautology, "P", "P . P"));
    assert!(equiv_reaches(EquivalenceRule::Tautology, "P", "P v P"));
    assert!(equiv_reaches(EquivalenceRule::DoubleNegation, "P", "~~P"));
    assert!(equiv_reaches(EquivalenceRule::DoubleNegation, "~~P", "P"));
}

#[test]
fn equiv_form_one_both_directions() {
    assert!(equiv_reaches(EquivalenceRule::Equivalence, "P <-> Q", "(P > Q) . (Q > P)"));
    assert!(equiv_reaches(EquivalenceRule::Equivalence, "(P > Q) . (Q > P)", "P <-> Q"));
}
