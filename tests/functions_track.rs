//! The §8 rules (Fun, ×): what the verifier accepts and, more importantly, what it refuses.
//! Scripts use the halmos_track language, but a failing step is an `Err`, not a panic, so a
//! test can assert that a bad proof is rejected at a named line.

use logic_core::models::rules::{EquivalenceRule as Eq, InferenceRule as R, ProofTechnique as T};
use logic_core::models::{Formula, Justification, Proof, Theorem};
use logic_core::models::theorem::Difficulty;
use logic_core::services::ProofVerifier;

fn f(s: &str) -> Formula {
    Formula::parse(s).unwrap_or_else(|e| panic!("formula {s}: {e}"))
}

fn just(rule: &str, lines: Vec<usize>) -> Justification {
    let inference = match rule {
        "MP" => Some(R::ModusPonens),
        "Simp" => Some(R::Simplification),
        "Conj" => Some(R::Conjunction),
        "∀E" => Some(R::UniversalElimination),
        "∃I" => Some(R::ExistentialIntroduction),
        "=I" => Some(R::IdentityIntroduction),
        "=E" => Some(R::IdentityElimination),
        _ => None,
    };
    if let Some(rule) = inference {
        return Justification::Inference { rule, lines };
    }
    let rule = match rule {
        "Def" => Eq::Definition,
        "Equiv" => Eq::Equivalence,
        "Comm" => Eq::Commutation,
        other => panic!("unknown rule {other}"),
    };
    Justification::Equivalence { rule, line: lines[0] }
}

/// Run a script; `Err((step, reason))` names the first step the verifier refuses.
fn run(premises: &[&str], conclusion: &str, script: &[&str]) -> Result<(), (String, String)> {
    let theorem = Theorem::new(
        premises.iter().map(|p| f(p)).collect(),
        f(conclusion),
        Difficulty::Easy,
        None,
        None,
    );
    let mut p = Proof::new(theorem);
    for step in script {
        if let Some((tech, formula)) = step.split_once("> ") {
            let t = match tech {
                "∃E" => T::ExistentialElimination,
                "CP" => T::ConditionalProof,
                _ => panic!("technique {tech}"),
            };
            p.open_subproof(f(formula), t);
            continue;
        }
        if let Some(rest) = step.strip_prefix('<') {
            let (tech, formula) = rest.split_once(' ').unwrap();
            let t = match tech {
                "∃E" => T::ExistentialElimination,
                "CP" => T::ConditionalProof,
                _ => panic!("technique {tech}"),
            };
            if p.close_subproof(f(formula), t).is_none() {
                return Err((step.to_string(), "cannot close".to_string()));
            }
        } else {
            let (formula, j) = step.split_once(" :: ").unwrap_or_else(|| panic!("no :: in {step}"));
            let mut parts = j.split_whitespace();
            let rule = parts.next().unwrap();
            let lines: Vec<usize> = parts
                .flat_map(|x| x.split(','))
                .filter(|x| !x.is_empty())
                .map(|x| x.parse().unwrap())
                .collect();
            p.add_line(f(formula), just(rule, lines));
        }
        let last = p.lines.len() - 1;
        let r = ProofVerifier::verify_line(&p.lines[last], &p);
        if !r.is_valid {
            return Err((step.to_string(), r.message.unwrap_or_default()));
        }
        p.lines[last].is_valid = true;
    }
    Ok(())
}

fn accepted(premises: &[&str], conclusion: &str, script: &[&str]) {
    if let Err((step, why)) = run(premises, conclusion, script) {
        panic!("expected acceptance, refused at `{step}`: {why}");
    }
}

fn refused_at(premises: &[&str], conclusion: &str, script: &[&str], step_text: &str) {
    match run(premises, conclusion, script) {
        Ok(()) => panic!("a bad proof was accepted: {script:?}"),
        Err((step, _)) => assert_eq!(step, step_text, "refused at the wrong step"),
    }
}

// ---- parsing and display ----

#[test]
fn product_round_trips_through_display() {
    for s in ["f ⊆ a × b", "⟨c, d⟩ ∈ a × b", "x ∈ a × b ∪ c", "x ∈ (a ∪ b) × c"] {
        let once = f(s).display_string();
        assert_eq!(f(&once).display_string(), once, "{s}");
    }
}

#[test]
fn product_binds_tighter_than_union() {
    let parsed = f("x ∈ a ∪ b × c");
    let tight = f("x ∈ a ∪ (b × c)");
    assert_eq!(parsed, tight);
    assert_ne!(parsed, f("x ∈ (a ∪ b) × c"));
}

#[test]
fn product_parses_with_the_ascii_spelling() {
    assert_eq!(f("x ∈ a \\times b"), f("x ∈ a × b"));
}

// ---- Fun ----

#[test]
fn fun_unfolds_to_its_definition() {
    accepted(
        &["Fun(f, a, b)"],
        "f ⊆ a × b",
        &["f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Def 1", "f ⊆ a × b :: Simp 2"],
    );
}

#[test]
fn fun_refuses_a_partial_unfolding() {
    // Dropping the uniqueness clause is not the definition of Fun.
    refused_at(
        &["Fun(f, a, b)"],
        "f ⊆ a × b",
        &["f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f)) :: Def 1"],
        "f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f)) :: Def 1",
    );
}

#[test]
fn fun_refuses_a_different_relation_as_its_unfolding() {
    refused_at(
        &["Fun(f, a, b)"],
        "f ⊆ b × a",
        &["f ⊆ b × a . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Def 1"],
        "f ⊆ b × a . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Def 1",
    );
}

#[test]
fn fun_gives_a_value_for_each_point_of_its_domain() {
    accepted(
        &["Fun(f, a, b)", "c ∈ a"],
        "∃y(⟨c, y⟩ ∈ f)",
        &[
            "f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Def 1",
            "∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Simp 3",
            "c ∈ a ⊃ ∃y(⟨c, y⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = y)) :: ∀E 4",
            "∃y(⟨c, y⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = y)) :: MP 5,2",
            "∃E> ⟨c, d⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = d)",
            "⟨c, d⟩ ∈ f :: Simp 7",
            "∃y(⟨c, y⟩ ∈ f) :: ∃I 8",
            "<∃E ∃y(⟨c, y⟩ ∈ f)",
        ],
    );
}

#[test]
fn fun_gives_no_value_outside_its_domain() {
    // Without c ∈ a, ∀E yields only the conditional: MP cannot fire, so the value is not derivable.
    refused_at(
        &["Fun(f, a, b)"],
        "∃y(⟨c, y⟩ ∈ f)",
        &[
            "f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Def 1",
            "∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Simp 2",
            "c ∈ a ⊃ ∃y(⟨c, y⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = y)) :: ∀E 3",
            "∃y(⟨c, y⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = y)) :: MP 4,1",
        ],
        "∃y(⟨c, y⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = y)) :: MP 4,1",
    );
}

#[test]
fn fun_refuses_instantiating_the_value_without_the_domain() {
    // ∀E on the unfolded Fun instantiates the conditional, never ⟨c, d⟩ ∈ f itself.
    refused_at(
        &["Fun(f, a, b)"],
        "⟨c, d⟩ ∈ f",
        &[
            "f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Def 1",
            "∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Simp 2",
            "⟨c, d⟩ ∈ f :: ∀E 3",
        ],
        "⟨c, d⟩ ∈ f :: ∀E 3",
    );
}

// ---- × ----

#[test]
fn product_membership_unfolds_with_fresh_bound_names() {
    // x ∈ a × b unfolds with bound names y, z: the free name x must not be captured.
    accepted(
        &["x ∈ a × b"],
        "∃y∃z(y ∈ a . z ∈ b . x = ⟨y, z⟩)",
        &["∃y∃z(y ∈ a . z ∈ b . x = ⟨y, z⟩) :: Def 1"],
    );
}

#[test]
fn product_unfolding_refuses_a_capturing_binder() {
    // The bound name x would capture the free x of the membership: not an unfolding.
    refused_at(
        &["x ∈ a × b"],
        "∃x∃z(x ∈ a . z ∈ b . x = ⟨x, z⟩)",
        &["∃x∃z(x ∈ a . z ∈ b . x = ⟨x, z⟩) :: Def 1"],
        "∃x∃z(x ∈ a . z ∈ b . x = ⟨x, z⟩) :: Def 1",
    );
}

#[test]
fn pair_is_in_the_product_only_with_both_coordinates() {
    accepted(
        &["c ∈ a", "d ∈ b"],
        "⟨c, d⟩ ∈ a × b",
        &[
            "c ∈ a . d ∈ b :: Conj 1,2",
            "⟨c, d⟩ = ⟨c, d⟩ :: =I",
            "c ∈ a . d ∈ b . ⟨c, d⟩ = ⟨c, d⟩ :: Conj 3,4",
            "∃y(c ∈ a . y ∈ b . ⟨c, d⟩ = ⟨c, y⟩) :: ∃I 5",
            "∃x ∃y(x ∈ a . y ∈ b . ⟨c, d⟩ = ⟨x, y⟩) :: ∃I 6",
            "⟨c, d⟩ ∈ a × b :: Def 7",
        ],
    );
    // The same chain without d ∈ b cannot even form the conjunction on line 3.
    refused_at(
        &["c ∈ a"],
        "⟨c, d⟩ ∈ a × b",
        &["c ∈ a . d ∈ b :: Conj 1,1"],
        "c ∈ a . d ∈ b :: Conj 1,1",
    );
}

#[test]
fn product_refuses_a_fold_missing_a_coordinate() {
    // ∃x∃y(x ∈ a . ⟨c, d⟩ = ⟨x, y⟩) has no y ∈ b: it is not the unfolding of ⟨c, d⟩ ∈ a × b.
    refused_at(
        &["∃x∃y(x ∈ a . ⟨c, d⟩ = ⟨x, y⟩)"],
        "⟨c, d⟩ ∈ a × b",
        &["⟨c, d⟩ ∈ a × b :: Def 1"],
        "⟨c, d⟩ ∈ a × b :: Def 1",
    );
}

// ---- Rev and Comp (§10) ----

#[test]
fn inverse_refuses_the_pair_in_the_wrong_order() {
    // ∀y(⟨a, y⟩ ∈ f ≡ ⟨y, a⟩ ∈ g) at y := b is ⟨a, b⟩ ∈ f ≡ ⟨b, a⟩ ∈ g; it does not give ⟨a, b⟩ ∈ g.
    refused_at(
        &["Rev(f, g)", "⟨a, b⟩ ∈ f"],
        "⟨a, b⟩ ∈ g",
        &[
            "∀x∀y(⟨x, y⟩ ∈ f ≡ ⟨y, x⟩ ∈ g) :: Def 1",
            "∀y(⟨a, y⟩ ∈ f ≡ ⟨y, a⟩ ∈ g) :: ∀E 3",
            "⟨a, b⟩ ∈ g :: ∀E 4",
        ],
        "⟨a, b⟩ ∈ g :: ∀E 4",
    );
}

#[test]
fn composite_refuses_the_factors_swapped() {
    // h = g∘f means first f, then g. With ⟨a, b⟩ ∈ g and ⟨b, c⟩ ∈ f the ∃I has no ⟨a, z⟩ ∈ f witness.
    refused_at(
        &["Comp(g, f, h)", "⟨a, b⟩ ∈ g", "⟨b, c⟩ ∈ f"],
        "⟨a, c⟩ ∈ h",
        &[
            "∀x∀y(⟨x, y⟩ ∈ h ≡ ∃z(⟨x, z⟩ ∈ f . ⟨z, y⟩ ∈ g)) :: Def 1",
            "∀y(⟨a, y⟩ ∈ h ≡ ∃z(⟨a, z⟩ ∈ f . ⟨z, y⟩ ∈ g)) :: ∀E 4",
            "⟨a, c⟩ ∈ h ≡ ∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g) :: ∀E 5",
            "(⟨a, c⟩ ∈ h ⊃ ∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g)) . (∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g) ⊃ ⟨a, c⟩ ∈ h) :: Equiv 6",
            "∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g) ⊃ ⟨a, c⟩ ∈ h :: Simp 7",
            "⟨a, b⟩ ∈ g . ⟨b, c⟩ ∈ f :: Conj 2,3",
            "∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g) :: ∃I 9",
        ],
        "∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g) :: ∃I 9",
    );
}
