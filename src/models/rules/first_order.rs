//! Structural checks for the quantifier and identity rules. Context conditions (an
//! arbitrary name for ∀I, a fresh name for ∃E) are checked by the verifier, which sees
//! the whole proof.

use crate::models::formula::Formula;
use crate::models::term::Term;

/// Does `target` arise from `quantified` (∀x φ or ∃x φ, by `body`/`var`) by putting one term
/// for the free occurrences of `var`? Returns that term (`None` when `var` is not free).
pub fn instance_of(var: &str, body: &Formula, target: &Formula) -> Result<Option<Term>, String> {
    let term = Formula::instance_term(body, var, target).map_err(|_| {
        format!(
            "{} is not an instance of {}: no single term put for {} gives it",
            target.display_string(),
            body.display_string(),
            var
        )
    })?;
    match &term {
        None => Ok(None),
        Some(t) => match body.substitute_free(var, t) {
            Err(capture) => Err(format!(
                "Putting {} for {} is not allowed: {} would be captured by the quantifier on {}",
                t.display_string(),
                var,
                t.display_string(),
                capture.binder
            )),
            Ok(result) if result == *target => Ok(term),
            Ok(_) => Err(format!(
                "{} is not an instance of {}",
                target.display_string(),
                body.display_string()
            )),
        },
    }
}

/// ∀E: from ∀x φ infer φ[t/x].
pub fn universal_elimination(premise: &Formula, conclusion: &Formula) -> Result<(), String> {
    match premise {
        Formula::ForAll(var, body) => instance_of(var, body, conclusion).map(|_| ()),
        _ => Err(format!(
            "∀E needs a universally quantified line (∀x …), but the cited line is {}",
            premise.display_string()
        )),
    }
}

/// ∃I: from φ[t/x] infer ∃x φ.
pub fn existential_introduction(premise: &Formula, conclusion: &Formula) -> Result<(), String> {
    match conclusion {
        Formula::Exists(var, body) => instance_of(var, body, premise).map(|_| ()),
        _ => Err(format!(
            "∃I concludes an existential formula (∃x …), not {}",
            conclusion.display_string()
        )),
    }
}

/// ∀I, structural part: from φ[c/x] infer ∀x φ, where every occurrence of the name c is
/// generalized. Returns the generalized name (`None` for a vacuous quantifier); the caller
/// checks that the name is arbitrary.
pub fn universal_introduction(premise: &Formula, conclusion: &Formula) -> Result<Option<String>, String> {
    let (var, body) = match conclusion {
        Formula::ForAll(var, body) => (var, body),
        _ => {
            return Err(format!(
                "∀I concludes a universal formula (∀x …), not {}",
                conclusion.display_string()
            ))
        }
    };
    match instance_of(var, body, premise)? {
        None => Ok(None),
        Some(Term::Name(c)) => {
            if conclusion.has_free_name(&c) {
                Err(format!(
                    "∀I must generalize every occurrence of {}: it still occurs in {}",
                    c,
                    conclusion.display_string()
                ))
            } else {
                Ok(Some(c))
            }
        }
        Some(t) => Err(format!(
            "∀I generalizes on a name, not on the compound term {}",
            t.display_string()
        )),
    }
}

/// =I: infer t = t from nothing.
pub fn identity_introduction(conclusion: &Formula) -> Result<(), String> {
    match conclusion {
        Formula::Identity(a, b) if a == b => Ok(()),
        _ => Err(format!("=I gives only t = t, not {}", conclusion.display_string())),
    }
}

/// =E: from a = b and φ infer φ with some free occurrences of a replaced by b (or b by a).
pub fn identity_elimination(premises: &[&Formula], conclusion: &Formula) -> Result<(), String> {
    if premises.len() != 2 {
        return Err("=E cites two lines: an identity a = b and the line to rewrite".to_string());
    }
    for (i, j) in [(0, 1), (1, 0)] {
        if let Formula::Identity(a, b) = premises[i] {
            if Formula::is_identity_replacement(premises[j], conclusion, a, b) {
                return Ok(());
            }
        }
    }
    if !premises.iter().any(|p| matches!(p, Formula::Identity(_, _))) {
        return Err("=E needs an identity line (a = b) among the cited lines".to_string());
    }
    Err(format!(
        "{} does not come from the cited line by replacing terms named equal",
        conclusion.display_string()
    ))
}

/// QN: ~∀xφ :: ∃x~φ, ~∃xφ :: ∀x~φ, ∀xφ :: ~∃x~φ, ∃xφ :: ~∀x~φ (both directions).
pub fn quantifier_negation_forms(f: &Formula) -> Vec<Formula> {
    let not = |g: Formula| Formula::Not(Box::new(g));
    let mut out = Vec::new();
    match f {
        Formula::Not(inner) => match inner.as_ref() {
            Formula::ForAll(x, body) => {
                out.push(Formula::Exists(x.clone(), Box::new(not((**body).clone()))));
                if let Formula::Not(b) = body.as_ref() {
                    out.push(Formula::Exists(x.clone(), b.clone()));
                }
            }
            Formula::Exists(x, body) => {
                out.push(Formula::ForAll(x.clone(), Box::new(not((**body).clone()))));
                if let Formula::Not(b) = body.as_ref() {
                    out.push(Formula::ForAll(x.clone(), b.clone()));
                }
            }
            _ => {}
        },
        Formula::ForAll(x, body) => {
            out.push(not(Formula::Exists(x.clone(), Box::new(not((**body).clone())))));
            if let Formula::Not(b) = body.as_ref() {
                out.push(not(Formula::Exists(x.clone(), b.clone())));
            }
        }
        Formula::Exists(x, body) => {
            out.push(not(Formula::ForAll(x.clone(), Box::new(not((**body).clone())))));
            if let Formula::Not(b) = body.as_ref() {
                out.push(not(Formula::ForAll(x.clone(), b.clone())));
            }
        }
        _ => {}
    }
    out
}

/// Def: unfold one defined symbol in an atomic formula. Folding is the converse and is
/// checked by the verifier in the other direction.
///
/// t ⊆ s :: ∀x(x ∈ t ⊃ x ∈ s)      t ∈ ∅ :: ⊥                t ∈ {s} :: t = s
/// t ∈ {s, r} :: t = s ∨ t = r      t ∈ s ∪ r :: t ∈ s ∨ t ∈ r t ∈ s ∩ r :: t ∈ s . t ∈ r
/// t ∈ s − r :: t ∈ s . t ∉ r       t ∈ ℘(s) :: t ⊆ s          t ∈ ⋃s :: ∃x(x ∈ s . t ∈ x)
/// ⟨s, r⟩ = {{s}, {s, r}} (anywhere in an atomic formula)
///
/// t ∈ s × r :: ∃x∃y(x ∈ s . y ∈ r . t = ⟨x, y⟩)
/// Fun(f, a, b) :: f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y)))
///   (Halmos §8: f is a function from a to b. The predicate is an abbreviation, not syntax.)
pub fn definition_unfoldings(f: &Formula) -> Vec<Formula> {
    let mem = |a: &Term, b: &Term| Formula::Membership(a.clone(), b.clone());
    let id = |a: &Term, b: &Term| Formula::Identity(a.clone(), b.clone());
    let fresh = |ts: &[&Term]| {
        let used: std::collections::BTreeSet<String> = ts.iter().flat_map(|t| t.names()).collect();
        Formula::fresh_name(&used)
    };
    // Fresh bound names: avoid every name in `used`, and each other.
    let fresh_avoiding = |used: &mut std::collections::BTreeSet<String>| {
        let n = Formula::fresh_name(used);
        used.insert(n.clone());
        n
    };
    let mut out = Vec::new();
    match f {
        Formula::Membership(t, Term::Product(s, r)) => {
            let mut used: std::collections::BTreeSet<String> =
                [t, s.as_ref(), r.as_ref()].iter().flat_map(|t| t.names()).collect();
            let x = Term::Name(fresh_avoiding(&mut used));
            let y = Term::Name(fresh_avoiding(&mut used));
            let pair = Term::OrderedPair(Box::new(x.clone()), Box::new(y.clone()));
            let body = Formula::And(
                Box::new(Formula::And(Box::new(mem(&x, s)), Box::new(mem(&y, r)))),
                Box::new(id(t, &pair)),
            );
            out.push(Formula::Exists(
                x.display_string(),
                Box::new(Formula::Exists(y.display_string(), Box::new(body))),
            ));
        }
        Formula::Predicate(name, args) if name == "Fun" && args.len() == 3 => {
            let (fe, a, b) = (&args[0], &args[1], &args[2]);
            let mut used: std::collections::BTreeSet<String> = args.iter().flat_map(|t| t.names()).collect();
            let x = Term::Name(fresh_avoiding(&mut used));
            let y = Term::Name(fresh_avoiding(&mut used));
            let z = Term::Name(fresh_avoiding(&mut used));
            let inner = Formula::ForAll(
                z.display_string(),
                Box::new(Formula::Implies(
                    Box::new(mem(&Term::OrderedPair(Box::new(x.clone()), Box::new(z.clone())), fe)),
                    Box::new(id(&z, &y)),
                )),
            );
            let some_y = Formula::Exists(
                y.display_string(),
                Box::new(Formula::And(
                    Box::new(mem(&Term::OrderedPair(Box::new(x.clone()), Box::new(y.clone())), fe)),
                    Box::new(inner),
                )),
            );
            let every_x = Formula::ForAll(
                x.display_string(),
                Box::new(Formula::Implies(Box::new(mem(&x, a)), Box::new(some_y))),
            );
            out.push(Formula::And(
                Box::new(Formula::Subset(fe.clone(), Term::Product(Box::new(a.clone()), Box::new(b.clone())))),
                Box::new(every_x),
            ));
        }
        Formula::Predicate(name, args) if name == "Rev" && args.len() == 2 => {
            // Rev(f, g) :: g is the inverse of f: ∀x∀y(⟨x, y⟩ ∈ f ≡ ⟨y, x⟩ ∈ g)
            let (fe, ge) = (&args[0], &args[1]);
            let mut used: std::collections::BTreeSet<String> = args.iter().flat_map(|t| t.names()).collect();
            let x = Term::Name(fresh_avoiding(&mut used));
            let y = Term::Name(fresh_avoiding(&mut used));
            let xy = Term::OrderedPair(Box::new(x.clone()), Box::new(y.clone()));
            let yx = Term::OrderedPair(Box::new(y.clone()), Box::new(x.clone()));
            let body = Formula::Biconditional(Box::new(mem(&xy, fe)), Box::new(mem(&yx, ge)));
            out.push(Formula::ForAll(
                x.display_string(),
                Box::new(Formula::ForAll(y.display_string(), Box::new(body))),
            ));
        }
        Formula::Predicate(name, args) if name == "Comp" && args.len() == 3 => {
            // Comp(g, f, h) :: h = g∘f: ∀x∀z(⟨x, z⟩ ∈ h ≡ ∃y(⟨x, y⟩ ∈ f . ⟨y, z⟩ ∈ g))
            let (ge, fe, he) = (&args[0], &args[1], &args[2]);
            let mut used: std::collections::BTreeSet<String> = args.iter().flat_map(|t| t.names()).collect();
            let x = Term::Name(fresh_avoiding(&mut used));
            let z = Term::Name(fresh_avoiding(&mut used));
            let y = Term::Name(fresh_avoiding(&mut used));
            let xz = Term::OrderedPair(Box::new(x.clone()), Box::new(z.clone()));
            let xy = Term::OrderedPair(Box::new(x.clone()), Box::new(y.clone()));
            let yz = Term::OrderedPair(Box::new(y.clone()), Box::new(z.clone()));
            let some_y = Formula::Exists(
                y.display_string(),
                Box::new(Formula::And(Box::new(mem(&xy, fe)), Box::new(mem(&yz, ge)))),
            );
            out.push(Formula::ForAll(
                x.display_string(),
                Box::new(Formula::ForAll(
                    z.display_string(),
                    Box::new(Formula::Biconditional(Box::new(mem(&xz, he)), Box::new(some_y))),
                )),
            ));
        }
        Formula::Subset(t, s) => {
            let x = Term::Name(fresh(&[t, s]));
            out.push(Formula::ForAll(
                x.display_string(),
                Box::new(Formula::Implies(Box::new(mem(&x, t)), Box::new(mem(&x, s)))),
            ));
        }
        Formula::Membership(t, set) => match set {
            Term::Empty => out.push(Formula::Contradiction),
            Term::Singleton(s) => out.push(id(t, s)),
            Term::Pair(s, r) => out.push(Formula::Or(Box::new(id(t, s)), Box::new(id(t, r)))),
            Term::Union(s, r) => out.push(Formula::Or(Box::new(mem(t, s)), Box::new(mem(t, r)))),
            Term::Intersection(s, r) => out.push(Formula::And(Box::new(mem(t, s)), Box::new(mem(t, r)))),
            Term::Difference(s, r) => out.push(Formula::And(
                Box::new(mem(t, s)),
                Box::new(Formula::Not(Box::new(mem(t, r)))),
            )),
            Term::PowerSet(s) => out.push(Formula::Subset(t.clone(), (**s).clone())),
            Term::BigUnion(s) => {
                let x = Term::Name(fresh(&[t, s]));
                out.push(Formula::Exists(
                    x.display_string(),
                    Box::new(Formula::And(Box::new(mem(&x, s)), Box::new(mem(t, &x)))),
                ));
            }
            _ => {}
        },
        _ => {}
    }
    if f.is_atomic() {
        let mut pairs: Vec<Term> = Vec::new();
        for t in f.all_terms() {
            if let Term::OrderedPair(a, b) = &t {
                if !pairs.contains(&t) {
                    pairs.push(t.clone());
                    let kuratowski = Term::Pair(
                        Box::new(Term::Singleton(a.clone())),
                        Box::new(Term::Pair(a.clone(), b.clone())),
                    );
                    out.push(f.replace_term_everywhere(&t, &kuratowski));
                }
            }
        }
    }
    out
}
