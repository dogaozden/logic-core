//! First-order structure on formulas: rendering of predicates, identity, membership and
//! quantifiers; free names; capture-avoiding substitution; alphabetic variants; instance
//! matching for the quantifier rules; and the identity-replacement check for =E.

use super::formula::Formula;
use super::term::Term;
use std::collections::BTreeSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Render {
    Unicode,
    AsciiBracketed,
    Ascii,
}

/// Why a substitution of a term for a variable is not allowed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Capture {
    /// The quantified variable that would capture a name of the substituted term.
    pub binder: String,
}

impl Formula {
    /// Atomic formulas: sentence letters, ⊥, predications, identities, memberships and inclusions.
    pub fn is_atomic(&self) -> bool {
        matches!(
            self,
            Formula::Atom(_)
                | Formula::Contradiction
                | Formula::Predicate(_, _)
                | Formula::Identity(_, _)
                | Formula::Membership(_, _)
                | Formula::Subset(_, _)
        )
    }

    /// Does the formula use any first-order syntax (predicates, terms, quantifiers)?
    pub fn is_first_order(&self) -> bool {
        match self {
            Formula::Atom(_) | Formula::Contradiction => false,
            Formula::Not(inner) => inner.is_first_order(),
            Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) | Formula::Biconditional(l, r) => {
                l.is_first_order() || r.is_first_order()
            }
            _ => true,
        }
    }

    /// A quantifier body that can follow `∀x ` without brackets.
    pub(crate) fn is_tight_quantifier_body(&self) -> bool {
        match self {
            Formula::Atom(_)
            | Formula::Contradiction
            | Formula::Predicate(_, _)
            | Formula::ForAll(_, _)
            | Formula::Exists(_, _) => true,
            Formula::Not(inner) => !matches!(inner.as_ref(), Formula::Identity(_, _) | Formula::Membership(_, _)),
            _ => false,
        }
    }

    fn render(&self, mode: Render) -> String {
        match mode {
            Render::Unicode => self.display_string(),
            Render::AsciiBracketed => self.ascii_string_bracketed(),
            Render::Ascii => self.ascii_string(),
        }
    }

    /// Rendering of the first-order constructs; `None` for propositional connectives.
    pub(crate) fn first_order_string(&self, mode: Render) -> Option<String> {
        let ascii = mode != Render::Unicode;
        let term = |t: &Term| if ascii { t.ascii_string() } else { t.display_string() };
        let infix = |l: &Term, op_unicode: &str, op_ascii: &str, r: &Term| {
            format!("{} {} {}", term(l), if ascii { op_ascii } else { op_unicode }, term(r))
        };
        Some(match self {
            Formula::Predicate(name, args) => {
                format!("{}({})", name, args.iter().map(term).collect::<Vec<_>>().join(", "))
            }
            Formula::Identity(l, r) => infix(l, "=", "=", r),
            Formula::Membership(l, r) => infix(l, "∈", "\\in", r),
            Formula::Subset(l, r) => infix(l, "⊆", "\\sub", r),
            Formula::Not(inner) => match inner.as_ref() {
                Formula::Identity(l, r) => infix(l, "≠", "!=", r),
                Formula::Membership(l, r) => infix(l, "∉", "\\notin", r),
                _ => return None,
            },
            Formula::ForAll(v, body) | Formula::Exists(v, body) => {
                let q = match (self, ascii) {
                    (Formula::ForAll(_, _), false) => "∀".to_string(),
                    (Formula::ForAll(_, _), true) => "\\A ".to_string(),
                    (_, false) => "∃".to_string(),
                    (_, true) => "\\E ".to_string(),
                };
                let inner = body.render(mode);
                if body.is_tight_quantifier_body() {
                    format!("{}{} {}", q, v, inner)
                } else {
                    let (open, close) = match mode {
                        Render::Ascii => ("(", ")"),
                        _ => Self::brackets_for_body(body.bracket_depth() + 1),
                    };
                    format!("{}{}{}{}{}", q, v, open, inner, close)
                }
            }
            _ => return None,
        })
    }

    fn brackets_for_body(levels: usize) -> (&'static str, &'static str) {
        match (levels - 1).min(2) {
            0 => ("(", ")"),
            1 => ("[", "]"),
            _ => ("{", "}"),
        }
    }

    /// Every term occurring in an atomic formula (not descending into binders).
    fn atomic_terms(&self) -> Vec<&Term> {
        match self {
            Formula::Predicate(_, args) => args.iter().collect(),
            Formula::Identity(l, r) | Formula::Membership(l, r) | Formula::Subset(l, r) => vec![l, r],
            _ => vec![],
        }
    }

    fn with_atomic_terms(&self, ts: Vec<Term>) -> Formula {
        match self {
            Formula::Predicate(n, _) => Formula::Predicate(n.clone(), ts),
            Formula::Identity(_, _) => Formula::Identity(ts[0].clone(), ts[1].clone()),
            Formula::Membership(_, _) => Formula::Membership(ts[0].clone(), ts[1].clone()),
            Formula::Subset(_, _) => Formula::Subset(ts[0].clone(), ts[1].clone()),
            _ => self.clone(),
        }
    }

    /// Names occurring free (not bound by a quantifier above them).
    pub fn free_names(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_free(&mut Vec::new(), &mut out);
        out
    }

    fn collect_free(&self, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
        match self {
            Formula::Atom(_) | Formula::Contradiction => {}
            Formula::Not(inner) => inner.collect_free(bound, out),
            Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) | Formula::Biconditional(l, r) => {
                l.collect_free(bound, out);
                r.collect_free(bound, out);
            }
            Formula::ForAll(v, body) | Formula::Exists(v, body) => {
                bound.push(v.clone());
                body.collect_free(bound, out);
                bound.pop();
            }
            _ => {
                for t in self.atomic_terms() {
                    for n in t.names() {
                        if !bound.contains(&n) {
                            out.insert(n);
                        }
                    }
                }
            }
        }
    }

    /// Every name in the formula, bound variables included.
    pub fn all_names(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_all_names(&mut out);
        out
    }

    fn collect_all_names(&self, out: &mut BTreeSet<String>) {
        match self {
            Formula::Atom(_) | Formula::Contradiction => {}
            Formula::Not(inner) => inner.collect_all_names(out),
            Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) | Formula::Biconditional(l, r) => {
                l.collect_all_names(out);
                r.collect_all_names(out);
            }
            Formula::ForAll(v, body) | Formula::Exists(v, body) => {
                out.insert(v.clone());
                body.collect_all_names(out);
            }
            _ => {
                for t in self.atomic_terms() {
                    t.collect_names(out);
                }
            }
        }
    }

    pub fn has_free_name(&self, name: &str) -> bool {
        self.free_names().contains(name)
    }

    /// Replace the free occurrences of `var` by `term`, refusing captures:
    /// a quantifier on a name of `term` above a free occurrence of `var`.
    pub fn substitute_free(&self, var: &str, term: &Term) -> Result<Formula, Capture> {
        let names = term.names();
        self.subst_inner(var, term, &names)
    }

    fn subst_inner(&self, var: &str, term: &Term, names: &BTreeSet<String>) -> Result<Formula, Capture> {
        Ok(match self {
            Formula::Atom(_) | Formula::Contradiction => self.clone(),
            Formula::Not(inner) => Formula::Not(Box::new(inner.subst_inner(var, term, names)?)),
            Formula::And(l, r) => Formula::And(Box::new(l.subst_inner(var, term, names)?), Box::new(r.subst_inner(var, term, names)?)),
            Formula::Or(l, r) => Formula::Or(Box::new(l.subst_inner(var, term, names)?), Box::new(r.subst_inner(var, term, names)?)),
            Formula::Implies(l, r) => {
                Formula::Implies(Box::new(l.subst_inner(var, term, names)?), Box::new(r.subst_inner(var, term, names)?))
            }
            Formula::Biconditional(l, r) => Formula::Biconditional(
                Box::new(l.subst_inner(var, term, names)?),
                Box::new(r.subst_inner(var, term, names)?),
            ),
            Formula::ForAll(v, body) | Formula::Exists(v, body) => {
                if v == var || !body.has_free_name(var) {
                    self.clone()
                } else if names.contains(v) {
                    return Err(Capture { binder: v.clone() });
                } else {
                    let b = Box::new(body.subst_inner(var, term, names)?);
                    match self {
                        Formula::ForAll(_, _) => Formula::ForAll(v.clone(), b),
                        _ => Formula::Exists(v.clone(), b),
                    }
                }
            }
            _ => self.with_atomic_terms(self.atomic_terms().into_iter().map(|t| t.replace_name(var, term)).collect()),
        })
    }

    /// Equality up to renaming of bound variables.
    pub fn alpha_eq(&self, other: &Formula) -> bool {
        if self == other {
            return true;
        }
        Self::alpha(self, other, &mut Vec::new())
    }

    fn alpha(a: &Formula, b: &Formula, env: &mut Vec<(String, String)>) -> bool {
        match (a, b) {
            (Formula::Atom(x), Formula::Atom(y)) => x == y,
            (Formula::Contradiction, Formula::Contradiction) => true,
            (Formula::Not(x), Formula::Not(y)) => Self::alpha(x, y, env),
            (Formula::And(a1, a2), Formula::And(b1, b2))
            | (Formula::Or(a1, a2), Formula::Or(b1, b2))
            | (Formula::Implies(a1, a2), Formula::Implies(b1, b2))
            | (Formula::Biconditional(a1, a2), Formula::Biconditional(b1, b2)) => {
                Self::alpha(a1, b1, env) && Self::alpha(a2, b2, env)
            }
            (Formula::ForAll(v, x), Formula::ForAll(w, y)) | (Formula::Exists(v, x), Formula::Exists(w, y)) => {
                env.push((v.clone(), w.clone()));
                let ok = Self::alpha(x, y, env);
                env.pop();
                ok
            }
            (Formula::Predicate(p, xs), Formula::Predicate(q, ys)) => {
                p == q && xs.len() == ys.len() && xs.iter().zip(ys).all(|(s, t)| Self::alpha_term(s, t, env))
            }
            (Formula::Identity(a1, a2), Formula::Identity(b1, b2))
            | (Formula::Membership(a1, a2), Formula::Membership(b1, b2))
            | (Formula::Subset(a1, a2), Formula::Subset(b1, b2)) => {
                Self::alpha_term(a1, b1, env) && Self::alpha_term(a2, b2, env)
            }
            _ => false,
        }
    }

    fn alpha_term(s: &Term, t: &Term, env: &[(String, String)]) -> bool {
        match (s, t) {
            (Term::Name(x), Term::Name(y)) => {
                for (v, w) in env.iter().rev() {
                    if v == x || w == y {
                        return v == x && w == y;
                    }
                }
                x == y
            }
            (Term::Function(f, xs), Term::Function(g, ys)) => {
                f == g && xs.len() == ys.len() && xs.iter().zip(ys).all(|(a, b)| Self::alpha_term(a, b, env))
            }
            _ => {
                std::mem::discriminant(s) == std::mem::discriminant(t)
                    && s.children().len() == t.children().len()
                    && s.children().iter().zip(t.children()).all(|(a, b)| Self::alpha_term(a, b, env))
            }
        }
    }

    /// Find the term `t` with `pattern[t/var] == target`.
    /// `Ok(Some(t))`: the free occurrences of `var` all stand for `t`.
    /// `Ok(None)`: `var` does not occur free in `pattern`, and pattern equals target.
    /// `Err(())`: no such term.
    pub fn instance_term(pattern: &Formula, var: &str, target: &Formula) -> Result<Option<Term>, ()> {
        let mut found: Option<Term> = None;
        if Self::match_instance(pattern, var, target, &mut found, &mut Vec::new()) {
            Ok(found)
        } else {
            Err(())
        }
    }

    fn match_instance(p: &Formula, var: &str, t: &Formula, found: &mut Option<Term>, bound: &mut Vec<String>) -> bool {
        match (p, t) {
            (Formula::Atom(x), Formula::Atom(y)) => x == y,
            (Formula::Contradiction, Formula::Contradiction) => true,
            (Formula::Not(x), Formula::Not(y)) => Self::match_instance(x, var, y, found, bound),
            (Formula::And(a1, a2), Formula::And(b1, b2))
            | (Formula::Or(a1, a2), Formula::Or(b1, b2))
            | (Formula::Implies(a1, a2), Formula::Implies(b1, b2))
            | (Formula::Biconditional(a1, a2), Formula::Biconditional(b1, b2)) => {
                Self::match_instance(a1, var, b1, found, bound) && Self::match_instance(a2, var, b2, found, bound)
            }
            (Formula::ForAll(v, x), Formula::ForAll(w, y)) | (Formula::Exists(v, x), Formula::Exists(w, y)) => {
                if v != w {
                    return false;
                }
                bound.push(v.clone());
                let ok = Self::match_instance(x, var, y, found, bound);
                bound.pop();
                ok
            }
            (Formula::Predicate(a, xs), Formula::Predicate(b, ys)) => {
                a == b
                    && xs.len() == ys.len()
                    && xs.iter().zip(ys).all(|(s, u)| Self::match_term(s, var, u, found, bound))
            }
            (Formula::Identity(a1, a2), Formula::Identity(b1, b2))
            | (Formula::Membership(a1, a2), Formula::Membership(b1, b2))
            | (Formula::Subset(a1, a2), Formula::Subset(b1, b2)) => {
                Self::match_term(a1, var, b1, found, bound) && Self::match_term(a2, var, b2, found, bound)
            }
            _ => false,
        }
    }

    fn match_term(p: &Term, var: &str, t: &Term, found: &mut Option<Term>, bound: &[String]) -> bool {
        match p {
            Term::Name(n) if n == var && !bound.iter().any(|b| b == var) => match found {
                Some(prev) => prev == t,
                None => {
                    *found = Some(t.clone());
                    true
                }
            },
            Term::Name(_) | Term::Empty => p == t,
            Term::Function(f, xs) => match t {
                Term::Function(g, ys) => {
                    f == g && xs.len() == ys.len() && xs.iter().zip(ys).all(|(a, b)| Self::match_term(a, var, b, found, bound))
                }
                _ => false,
            },
            _ => {
                std::mem::discriminant(p) == std::mem::discriminant(t)
                    && p.children().iter().zip(t.children()).all(|(a, b)| Self::match_term(a, var, b, found, bound))
            }
        }
    }

    /// Is `to` obtained from `from` by replacing some free occurrences of `a` by `b` (or of
    /// `b` by `a`), with neither term captured at the replaced positions?
    pub fn is_identity_replacement(from: &Formula, to: &Formula, a: &Term, b: &Term) -> bool {
        let names: BTreeSet<String> = a.names().union(&b.names()).cloned().collect();
        Self::id_replace(from, to, a, b, &names, &mut Vec::new())
    }

    fn id_replace(f: &Formula, g: &Formula, a: &Term, b: &Term, names: &BTreeSet<String>, bound: &mut Vec<String>) -> bool {
        match (f, g) {
            (Formula::Atom(x), Formula::Atom(y)) => x == y,
            (Formula::Contradiction, Formula::Contradiction) => true,
            (Formula::Not(x), Formula::Not(y)) => Self::id_replace(x, y, a, b, names, bound),
            (Formula::And(a1, a2), Formula::And(b1, b2))
            | (Formula::Or(a1, a2), Formula::Or(b1, b2))
            | (Formula::Implies(a1, a2), Formula::Implies(b1, b2))
            | (Formula::Biconditional(a1, a2), Formula::Biconditional(b1, b2)) => {
                Self::id_replace(a1, b1, a, b, names, bound) && Self::id_replace(a2, b2, a, b, names, bound)
            }
            (Formula::ForAll(v, x), Formula::ForAll(w, y)) | (Formula::Exists(v, x), Formula::Exists(w, y)) => {
                if v != w {
                    return false;
                }
                bound.push(v.clone());
                let ok = Self::id_replace(x, y, a, b, names, bound);
                bound.pop();
                ok
            }
            (Formula::Predicate(p, xs), Formula::Predicate(q, ys)) => {
                p == q && xs.len() == ys.len() && xs.iter().zip(ys).all(|(s, t)| Self::id_term(s, t, a, b, names, bound))
            }
            (Formula::Identity(a1, a2), Formula::Identity(b1, b2))
            | (Formula::Membership(a1, a2), Formula::Membership(b1, b2))
            | (Formula::Subset(a1, a2), Formula::Subset(b1, b2)) => {
                Self::id_term(a1, b1, a, b, names, bound) && Self::id_term(a2, b2, a, b, names, bound)
            }
            _ => false,
        }
    }

    fn id_term(s: &Term, t: &Term, a: &Term, b: &Term, names: &BTreeSet<String>, bound: &[String]) -> bool {
        if s == t {
            return true;
        }
        let free_here = !bound.iter().any(|v| names.contains(v));
        if free_here && ((s == a && t == b) || (s == b && t == a)) {
            return true;
        }
        match (s, t) {
            (Term::Function(f, xs), Term::Function(g, ys)) => {
                f == g && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| Self::id_term(x, y, a, b, names, bound))
            }
            (Term::Name(_), _) | (Term::Empty, _) => false,
            _ => {
                std::mem::discriminant(s) == std::mem::discriminant(t)
                    && s.children().iter().zip(t.children()).all(|(x, y)| Self::id_term(x, y, a, b, names, bound))
            }
        }
    }

    /// Every term occurring anywhere in the formula (free or not), outermost first.
    pub fn all_terms(&self) -> Vec<Term> {
        let mut out = Vec::new();
        self.collect_terms(&mut out);
        out
    }

    fn collect_terms(&self, out: &mut Vec<Term>) {
        match self {
            Formula::Atom(_) | Formula::Contradiction => {}
            Formula::Not(inner) | Formula::ForAll(_, inner) | Formula::Exists(_, inner) => inner.collect_terms(out),
            Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) | Formula::Biconditional(l, r) => {
                l.collect_terms(out);
                r.collect_terms(out);
            }
            _ => {
                for t in self.atomic_terms() {
                    for s in t.subterms() {
                        if !out.contains(s) {
                            out.push(s.clone());
                        }
                    }
                }
            }
        }
    }

    /// A variable name not occurring anywhere in any of the given formulas.
    pub fn fresh_variable(avoid: &[&Formula]) -> String {
        let used: BTreeSet<String> = avoid.iter().flat_map(|f| f.all_names()).collect();
        Self::fresh_name(&used)
    }

    /// The first of x, y, z, w, u, x1, x2, … not in `used`.
    pub fn fresh_name(used: &BTreeSet<String>) -> String {
        for base in ["x", "y", "z", "w", "u"] {
            if !used.contains(base) {
                return base.to_string();
            }
        }
        (1..)
            .map(|i| format!("x{}", i))
            .find(|n| !used.contains(n))
            .expect("an unused numbered variable exists")
    }
}

/// Defect: a propositional-only service (truth tables, generators, provers) received a
/// first-order formula. Callers are responsible for keeping first-order formulas out.
pub fn propositional_only(f: &Formula) -> ! {
    panic!("propositional-only service reached a first-order formula: {}", f.display_string())
}

impl Formula {
    /// Replace every occurrence of the term `from` (as a subterm of an atomic formula) by `to`.
    /// Used for definitional rewriting of closed terms; no binders are involved at atomic level.
    pub fn replace_term_everywhere(&self, from: &Term, to: &Term) -> Formula {
        fn go(t: &Term, from: &Term, to: &Term) -> Term {
            if t == from {
                return to.clone();
            }
            match t {
                Term::Name(_) | Term::Empty => t.clone(),
                _ => t.with_children(t.children().into_iter().map(|c| go(c, from, to)).collect()),
            }
        }
        match self {
            Formula::Atom(_) | Formula::Contradiction => self.clone(),
            Formula::Not(inner) => Formula::Not(Box::new(inner.replace_term_everywhere(from, to))),
            Formula::ForAll(v, inner) => Formula::ForAll(v.clone(), Box::new(inner.replace_term_everywhere(from, to))),
            Formula::Exists(v, inner) => Formula::Exists(v.clone(), Box::new(inner.replace_term_everywhere(from, to))),
            Formula::And(l, r) => Formula::And(Box::new(l.replace_term_everywhere(from, to)), Box::new(r.replace_term_everywhere(from, to))),
            Formula::Or(l, r) => Formula::Or(Box::new(l.replace_term_everywhere(from, to)), Box::new(r.replace_term_everywhere(from, to))),
            Formula::Implies(l, r) => Formula::Implies(Box::new(l.replace_term_everywhere(from, to)), Box::new(r.replace_term_everywhere(from, to))),
            Formula::Biconditional(l, r) => Formula::Biconditional(Box::new(l.replace_term_everywhere(from, to)), Box::new(r.replace_term_everywhere(from, to))),
            _ => self.with_atomic_terms(self.atomic_terms().into_iter().map(|t| go(t, from, to)).collect()),
        }
    }
}
