//! Terms of first-order logic and the set-theory term operators.
//!
//! A name is a lowercase letter followed by digits or primes (`a`, `x`, `b2`, `y'`).
//! A name is a variable where a quantifier binds it and a constant everywhere else.

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(tag = "type", content = "value")]
pub enum Term {
    Name(String),
    /// Function application `f(t1, …, tn)`
    Function(String, Vec<Term>),
    /// ∅
    Empty,
    /// {t}
    Singleton(Box<Term>),
    /// {t, s}
    Pair(Box<Term>, Box<Term>),
    /// ⟨t, s⟩
    OrderedPair(Box<Term>, Box<Term>),
    /// t ∪ s
    Union(Box<Term>, Box<Term>),
    /// t ∩ s
    Intersection(Box<Term>, Box<Term>),
    /// t − s
    Difference(Box<Term>, Box<Term>),
    /// ℘(t)
    PowerSet(Box<Term>),
    /// ⋃t
    BigUnion(Box<Term>),
}

impl Term {
    pub fn name(n: &str) -> Term {
        Term::Name(n.to_string())
    }

    /// Immediate subterms, left to right.
    pub fn children(&self) -> Vec<&Term> {
        match self {
            Term::Name(_) | Term::Empty => vec![],
            Term::Function(_, args) => args.iter().collect(),
            Term::Singleton(t) | Term::PowerSet(t) | Term::BigUnion(t) => vec![t],
            Term::Pair(a, b)
            | Term::OrderedPair(a, b)
            | Term::Union(a, b)
            | Term::Intersection(a, b)
            | Term::Difference(a, b) => vec![a, b],
        }
    }

    /// Rebuild this term with new immediate subterms (same arity as `children`).
    pub fn with_children(&self, mut kids: Vec<Term>) -> Term {
        let mut next = || Box::new(kids.remove(0));
        match self {
            Term::Name(_) | Term::Empty => self.clone(),
            Term::Function(f, _) => Term::Function(f.clone(), kids),
            Term::Singleton(_) => Term::Singleton(next()),
            Term::PowerSet(_) => Term::PowerSet(next()),
            Term::BigUnion(_) => Term::BigUnion(next()),
            Term::Pair(_, _) => {
                let a = next();
                Term::Pair(a, next())
            }
            Term::OrderedPair(_, _) => {
                let a = next();
                Term::OrderedPair(a, next())
            }
            Term::Union(_, _) => {
                let a = next();
                Term::Union(a, next())
            }
            Term::Intersection(_, _) => {
                let a = next();
                Term::Intersection(a, next())
            }
            Term::Difference(_, _) => {
                let a = next();
                Term::Difference(a, next())
            }
        }
    }

    pub fn collect_names(&self, out: &mut BTreeSet<String>) {
        match self {
            Term::Name(n) => {
                out.insert(n.clone());
            }
            _ => {
                for c in self.children() {
                    c.collect_names(out);
                }
            }
        }
    }

    pub fn names(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_names(&mut out);
        out
    }

    pub fn contains_name(&self, name: &str) -> bool {
        match self {
            Term::Name(n) => n == name,
            _ => self.children().iter().any(|c| c.contains_name(name)),
        }
    }

    /// Replace every occurrence of the name `name` by `replacement`.
    pub fn replace_name(&self, name: &str, replacement: &Term) -> Term {
        match self {
            Term::Name(n) if n == name => replacement.clone(),
            Term::Name(_) | Term::Empty => self.clone(),
            _ => self.with_children(
                self.children()
                    .into_iter()
                    .map(|c| c.replace_name(name, replacement))
                    .collect(),
            ),
        }
    }

    /// Every subterm, including this one.
    pub fn subterms(&self) -> Vec<&Term> {
        let mut out = vec![self];
        for c in self.children() {
            out.extend(c.subterms());
        }
        out
    }

    fn is_simple(&self) -> bool {
        !matches!(
            self,
            Term::Union(_, _) | Term::Intersection(_, _) | Term::Difference(_, _)
        )
    }

    fn operand(&self, ascii: bool) -> String {
        if self.is_simple() {
            self.render(ascii)
        } else {
            format!("({})", self.render(ascii))
        }
    }

    pub fn display_string(&self) -> String {
        self.render(false)
    }

    pub fn ascii_string(&self) -> String {
        self.render(true)
    }

    fn render(&self, ascii: bool) -> String {
        let list = |ts: &[&Term]| ts.iter().map(|t| t.render(ascii)).collect::<Vec<_>>().join(", ");
        match self {
            Term::Name(n) => n.clone(),
            Term::Function(f, args) => format!("{}({})", f, list(&args.iter().collect::<Vec<_>>())),
            Term::Empty => (if ascii { "\\empty" } else { "∅" }).to_string(),
            Term::Singleton(t) => format!("{{{}}}", t.render(ascii)),
            Term::Pair(a, b) => format!("{{{}}}", list(&[a, b])),
            Term::OrderedPair(a, b) => {
                if ascii {
                    format!("<{}>", list(&[a, b]))
                } else {
                    format!("⟨{}⟩", list(&[a, b]))
                }
            }
            Term::Union(a, b) => format!(
                "{} {} {}",
                a.operand(ascii),
                if ascii { "\\cup" } else { "∪" },
                b.operand(ascii)
            ),
            Term::Intersection(a, b) => format!(
                "{} {} {}",
                a.operand(ascii),
                if ascii { "\\cap" } else { "∩" },
                b.operand(ascii)
            ),
            Term::Difference(a, b) => format!(
                "{} {} {}",
                a.operand(ascii),
                if ascii { "\\minus" } else { "−" },
                b.operand(ascii)
            ),
            Term::PowerSet(t) => format!("{}({})", if ascii { "\\pow" } else { "℘" }, t.render(ascii)),
            Term::BigUnion(t) => {
                let sym = if ascii { "\\Union " } else { "⋃" };
                format!("{}{}", sym, t.operand(ascii))
            }
        }
    }
}

/// Is `s` a well-formed name (lowercase letter, then digits or primes)?
pub fn is_name(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_lowercase() => chars.all(|c| c.is_ascii_digit() || c == '\''),
        _ => false,
    }
}
