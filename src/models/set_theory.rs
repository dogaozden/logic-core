//! Set-theory mode: the ZFC axioms in the order Halmos's *Naive Set Theory* introduces them,
//! and a chapter-by-chapter exercise track. Every exercise has a machine-checked solution in
//! `tests/halmos_track.rs`.
//!
//! The defined symbols (⊆, ∅, {a}, {a, b}, ∪, ∩, −, ℘, ⋃, ⟨a, b⟩) are unfolded with the
//! Def rule. Each definition is licensed by the chapter that proves the set exists and is
//! unique (∅ in chapter 2, pairs in 3, unions in 4, powers in 5, ordered pairs in 6).

use super::formula::Formula;
use super::theorem::{Difficulty, Theorem};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Axiom {
    pub id: String,
    pub name: String,
    /// The axiom (for a schema: the general shape, with φ a placeholder sentence letter)
    pub formula: Formula,
    pub note: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrackExercise {
    pub id: String,
    pub title: String,
    pub hint: String,
    /// Axiom ids used as premises, in premise order (other premises are hypotheses)
    pub axioms: Vec<String>,
    pub theorem: Theorem,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrackChapter {
    /// Stable progress key (not a section number)
    pub id: String,
    /// Section number in Halmos's *Naive Set Theory*; `None` for material outside the book
    pub number: Option<u8>,
    pub title: String,
    pub summary: String,
    /// Axioms introduced in this chapter
    pub axioms: Vec<Axiom>,
    pub exercises: Vec<TrackExercise>,
}

fn f(s: &str) -> Formula {
    Formula::parse(s).unwrap_or_else(|e| panic!("set-theory table formula {s}: {e}"))
}

/// The axioms, keyed by id. Schemas appear as instances inside the exercises that use them.
pub fn axioms() -> Vec<(u8, Axiom)> {
    let ax = |ch: u8, id: &str, name: &str, formula: &str, note: &str| {
        (ch, Axiom { id: id.to_string(), name: name.to_string(), formula: f(formula), note: note.to_string() })
    };
    vec![
        ax(1, "ext", "Extension", "∀x ∀y(∀z(z ∈ x ≡ z ∈ y) ⊃ x = y)",
            "Two sets are equal if and only if they have the same elements."),
        ax(2, "exist", "Existence", "∃x(x = x)",
            "There is a set. Halmos assumes this at the start of section 2."),
        ax(2, "spec", "Specification (schema)", "∀x ∃y ∀z(z ∈ y ≡ (z ∈ x . S(z)))",
            "To every set and every condition S(z) there is the set of its elements satisfying S. Exercises give the instance they need."),
        ax(3, "pair", "Pairing", "∀x ∀y ∃w ∀z(z ∈ w ≡ (z = x ∨ z = y))",
            "For any two sets there is a set that contains them both (the exact form: exactly them)."),
        ax(4, "union", "Unions", "∀x ∃y ∀z(z ∈ y ≡ ∃w(w ∈ x . z ∈ w))",
            "For every collection of sets there is a set containing all the elements of its members."),
        ax(5, "power", "Powers", "∀x ∃y ∀z(z ∈ y ≡ z ⊆ x)",
            "For each set there is a set containing all its subsets."),
        ax(13, "nat", "Naturals (w = ω)", "Ind(w) . ∀s(Ind(s) ⊃ w ⊆ s)",
            "w is the least inductive set (Halmos §14). Exercises give this as the premise that w is inductive and below every inductive set."),
        ax(13, "add0", "Addition, base", "∀x(x ∈ w ⊃ p(x, ∅) = x)",
            "x + 0 = x for natural x. The recursion theorem (Halmos §15) gives add; the clauses are the premises."),
        ax(13, "adds", "Addition, successor", "∀x∀y((x ∈ w . y ∈ w) ⊃ p(x, y ∪ {y}) = p(x, y) ∪ {p(x, y)})",
            "x + S(y) = S(x + y) for naturals, with successor S(y) = y ∪ {y}."),
        ax(11, "inf", "Infinity", "∃x(∅ ∈ x . ∀y(y ∈ x ⊃ y ∪ {y} ∈ x))",
            "There is a set containing 0 and the successor of each of its elements."),
        ax(15, "choice", "Choice", "∀x((∅ ∉ x . ∀y ∀z((y ∈ x . z ∈ x . y ≠ z) ⊃ y ∩ z = ∅)) ⊃ ∃u ∀y(y ∈ x ⊃ ∃w ∀z(z ∈ y ∩ u ≡ z = w)))",
            "Every collection of disjoint nonempty sets has a set meeting each member in exactly one element."),
        ax(15, "zorn", "Zorn's lemma (schema)",
            "∀x((∀c((c ⊆ x . Chain(c)) ⊃ ⋃c ∈ x)) ⊃ ∃m(m ∈ x . ∀y((y ∈ x . m ⊆ y) ⊃ m = y)))",
            "If every chain of sets in x has its union in x, then x has a ⊆-maximal member. Chain(c) is an abbreviation (Def); exercises give the instance they need."),
        ax(16, "wo", "Well-ordering theorem (schema)", "∀x∃r WellOrd(r, x)",
            "Every set can be well-ordered. WellOrd(r, x) is an abbreviation (Def). Exercises give the instance they need."),
        ax(APPENDIX_KEY, "repl", "Substitution / Replacement (schema)", "∀x(∀y(y ∈ x ⊃ ∃z ∀w(S(y, w) ≡ w = z)) ⊃ ∃u ∀z(z ∈ u ≡ ∃y(y ∈ x . S(y, z))))",
            "The image of a set under a functional condition S(x, y) is a set."),
        ax(APPENDIX_KEY, "found", "Foundation (not in Halmos)", "∀x(∃y(y ∈ x) ⊃ ∃y(y ∈ x . ~∃z(z ∈ y . z ∈ x)))",
            "Every nonempty set has an ∈-minimal element. ZFC includes it; Halmos never uses it."),
    ]
}

fn axiom_formula(id: &str) -> Formula {
    axioms()
        .into_iter()
        .find(|(_, a)| a.id == id)
        .map(|(_, a)| a.formula)
        .unwrap_or_else(|| panic!("unknown axiom id {id}"))
}

struct Ex<'a> {
    title: &'a str,
    level: Difficulty,
    /// Premises: an axiom id (`@ext`) or a formula
    premises: &'a [&'a str],
    conclusion: &'a str,
    hint: &'a str,
}

fn exercise(chapter: u8, n: usize, e: &Ex) -> TrackExercise {
    let mut axioms = Vec::new();
    let premises = e
        .premises
        .iter()
        .map(|p| match p.strip_prefix('@') {
            Some(id) => {
                axioms.push(id.to_string());
                axiom_formula(id)
            }
            None => f(p),
        })
        .collect();
    let mut theorem = Theorem::new(premises, f(e.conclusion), e.level, None, Some(e.title.to_string()));
    theorem.id = format!("halmos-{}-{}", chapter, n);
    TrackExercise { id: theorem.id.clone(), title: e.title.to_string(), hint: e.hint.to_string(), axioms, theorem }
}

/// Chapter keys are progress keys, not section numbers. Keys never change once shipped, so
/// saved progress and the test table stay valid. Key 19 (Foundation) has no Halmos section.
pub const APPENDIX_KEY: u8 = 19;

fn book_section(key: u8) -> Option<u8> {
    match key {
        0 => Some(1),
        1..=18 => Some(key + 2),
        APPENDIX_KEY => None,
        20 => Some(21),
        other => panic!("set-theory chapter key {other} has no Halmos section"),
    }
}

fn chapter(key: u8, title: &str, summary: &str, exercises: &[Ex]) -> TrackChapter {
    TrackChapter {
        id: format!("halmos-{}", key),
        number: book_section(key),
        title: title.to_string(),
        summary: summary.to_string(),
        axioms: axioms().into_iter().filter(|(ch, _)| *ch == key).map(|(_, a)| a).collect(),
        exercises: exercises.iter().enumerate().map(|(i, e)| exercise(key, i + 1, e)).collect(),
    }
}

use Difficulty::{Easy, Expert, Hard, Medium};

/// The Halmos track, easy to hard within each chapter.
pub fn halmos_track() -> Vec<TrackChapter> {
    vec![
        chapter(0, "Very Naive Set Theory, Functions, and Proofs",
            "The quantifier and identity rules on small examples: ∀E, ∀I, ∃I, ∃E, QN, =I, =E.",
            &[
                Ex { title: "All F are G; a is F", level: Easy, premises: &["∀x(F(x) ⊃ G(x))", "F(a)"], conclusion: "G(a)",
                    hint: "∀E with a for x, then MP." },
                Ex { title: "Something is F", level: Easy, premises: &["F(a)"], conclusion: "∃x F(x)",
                    hint: "∃I: replace a by x." },
                Ex { title: "Universal syllogism", level: Easy, premises: &["∀x(F(x) ⊃ G(x))", "∀x F(x)"], conclusion: "∀x G(x)",
                    hint: "Work with a name that occurs in no premise, then ∀I on it." },
                Ex { title: "Some F is G", level: Medium, premises: &["∃x F(x)", "∀x(F(x) ⊃ G(x))"], conclusion: "∃x G(x)",
                    hint: "Open an ∃E subproof assuming F(a) for a new name a; derive ∃x G(x) inside; close with ∃E." },
                Ex { title: "Nothing is F", level: Easy, premises: &["~∃x F(x)"], conclusion: "∀x ~F(x)",
                    hint: "QN." },
                Ex { title: "Distributing ∀ over .", level: Medium, premises: &["∀x(F(x) . G(x))"], conclusion: "∀x F(x) . ∀x G(x)",
                    hint: "Instantiate on a fresh name, Simp, generalize each conjunct, Conj." },
                Ex { title: "Symmetry of identity", level: Easy, premises: &["a = b"], conclusion: "b = a",
                    hint: "=I gives a = a; then =E replaces the first a using a = b." },
                Ex { title: "Transitivity of identity", level: Easy, premises: &["a = b", "b = c"], conclusion: "a = c",
                    hint: "=E: rewrite b in a = b using b = c." },
                Ex { title: "∃∀ implies ∀∃", level: Hard, premises: &["∃x ∀y R(x, y)"], conclusion: "∀y ∃x R(x, y)",
                    hint: "∃E with a new a; inside, ∀E on another new name b, ∃I, then ∀I on b (b is not in the open assumption)." },
            ]),
        chapter(1, "The Axiom of Extension",
            "Belonging (∈), inclusion (⊆) and equality. Two sets are equal iff they have the same elements.",
            &[
                Ex { title: "Inclusion is reflexive", level: Easy, premises: &[], conclusion: "a ⊆ a",
                    hint: "Unfold the goal with Def: ∀x(x ∈ a ⊃ x ∈ a). CP on b ∈ a, ∀I on b, fold with Def." },
                Ex { title: "Same elements, same set", level: Easy, premises: &["@ext", "∀z(z ∈ a ≡ z ∈ b)"], conclusion: "a = b",
                    hint: "∀E twice on Extension, then MP." },
                Ex { title: "Inclusion is transitive", level: Medium, premises: &["a ⊆ b", "b ⊆ c"], conclusion: "a ⊆ c",
                    hint: "Unfold both premises with Def, ∀E on a new name, HS, ∀I, fold." },
                Ex { title: "Equal sets include each other", level: Medium, premises: &["a = b"], conclusion: "a ⊆ b",
                    hint: "Prove a ⊆ a as in 1.1, then =E." },
                Ex { title: "Inclusion is antisymmetric", level: Hard, premises: &["@ext", "a ⊆ b", "b ⊆ a"], conclusion: "a = b",
                    hint: "Unfold, instantiate both on a new c, Conj and Equiv give c ∈ a ≡ c ∈ b; ∀I; then Extension." },
                Ex { title: "Equality is extensional", level: Hard, premises: &["@ext"], conclusion: "a = b ≡ (a ⊆ b . b ⊆ a)",
                    hint: "Both directions by CP, then Conj and Equiv. One direction is 1.4 twice, the other 1.5." },
            ]),
        chapter(2, "The Axiom of Specification",
            "Subsets cut out by a condition. The empty set exists and is unique; nothing contains everything.",
            &[
                Ex { title: "Nothing belongs to ∅", level: Easy, premises: &[], conclusion: "∀x(x ∉ ∅)",
                    hint: "IP: assume a ∈ ∅, Def gives ⊥. Then ∀I." },
                Ex { title: "∅ is included in every set", level: Easy, premises: &[], conclusion: "∅ ⊆ a",
                    hint: "Unfold: ∀x(x ∈ ∅ ⊃ x ∈ a). From b ∈ ∅, Def gives ⊥, and IP on ~(b ∈ a) gives b ∈ a." },
                Ex { title: "The empty set is unique", level: Medium, premises: &["@ext", "∀x(x ∉ a)", "∀x(x ∉ b)"], conclusion: "a = b",
                    hint: "For a new c: ~(c ∈ a) and ~(c ∈ b) give c ∈ a ⊃ c ∈ b and back (Add, Impl). Equiv, ∀I, Extension." },
                Ex { title: "The only subset of ∅", level: Medium, premises: &["@ext", "a ⊆ ∅"], conclusion: "a = ∅",
                    hint: "c ∈ a gives c ∈ ∅; c ∈ ∅ gives ⊥. Build c ∈ a ≡ c ∈ ∅ and use Extension." },
                Ex { title: "Specification gives an empty set", level: Hard,
                    premises: &["@exist", "∀x ∃y ∀z(z ∈ y ≡ (z ∈ x . z ≠ z))"], conclusion: "∃y ∀z(z ∉ y)",
                    hint: "∃E on Existence with a; instantiate the schema at a and ∃E again with b; show no c is in b since c = c." },
                Ex { title: "Nothing contains everything", level: Expert,
                    premises: &["∀x ∃y ∀z(z ∈ y ≡ (z ∈ x . z ∉ z))"], conclusion: "∀x ∃y(y ∉ x)",
                    hint: "Russell: for arbitrary a take b = {z ∈ a : z ∉ z}. If b ∈ a then b ∈ b ≡ b ∉ b. So b ∉ a." },
            ]),
        chapter(3, "Unordered Pairs",
            "{a, b} and singletons {a}, licensed by Pairing plus Extension (uniqueness).",
            &[
                Ex { title: "a belongs to {a}", level: Easy, premises: &[], conclusion: "a ∈ {a}",
                    hint: "=I, then fold with Def." },
                Ex { title: "a belongs to {a, b}", level: Easy, premises: &[], conclusion: "a ∈ {a, b}",
                    hint: "=I, Add, Def." },
                Ex { title: "Pairing gives a set with a and b", level: Medium, premises: &["@pair"], conclusion: "∃p(a ∈ p . b ∈ p)",
                    hint: "∀E twice, ∃E with a new p, ∀E at a and at b, Equiv/Simp, =I and Add." },
                Ex { title: "Equal singletons", level: Medium, premises: &["{a} = {b}"], conclusion: "a = b",
                    hint: "a ∈ {a}, then =E to a ∈ {b}, then Def." },
                Ex { title: "{a, b} = {b, a}", level: Hard, premises: &["@ext"], conclusion: "{a, b} = {b, a}",
                    hint: "For a new c: c ∈ {a, b} ⊃ c ∈ {b, a} by Def, Comm, Def; same back; Conj, Equiv; ∀I; Extension." },
                Ex { title: "{a} = {a, a}", level: Hard, premises: &["@ext"], conclusion: "{a} = {a, a}",
                    hint: "c ∈ {a, a} unfolds to c = a ∨ c = a: Taut." },
            ]),
        chapter(4, "Unions and Intersections",
            "a ∪ b and a ∩ b, from the Axiom of Unions and Specification. The Boolean laws.",
            &[
                Ex { title: "a ⊆ a ∪ b", level: Easy, premises: &[], conclusion: "a ⊆ a ∪ b",
                    hint: "CP on c ∈ a, Add, Def, ∀I, Def." },
                Ex { title: "a ∩ b ⊆ a", level: Easy, premises: &[], conclusion: "a ∩ b ⊆ a",
                    hint: "CP on c ∈ a ∩ b, Def, Simp, ∀I, Def." },
                Ex { title: "∪ is commutative", level: Medium, premises: &["@ext"], conclusion: "a ∪ b = b ∪ a",
                    hint: "Def, Comm, Def inside a biconditional; ∀I; Extension." },
                Ex { title: "∩ is commutative", level: Medium, premises: &["@ext"], conclusion: "a ∩ b = b ∩ a",
                    hint: "As for ∪." },
                Ex { title: "a ∪ ∅ = a", level: Medium, premises: &["@ext"], conclusion: "a ∪ ∅ = a",
                    hint: "c ∈ a ∪ ∅ unfolds to c ∈ a ∨ ⊥; use DS with ~⊥, or CP/IP." },
                Ex { title: "a ∪ a = a", level: Medium, premises: &["@ext"], conclusion: "a ∪ a = a",
                    hint: "Taut." },
                Ex { title: "If a ⊆ b then a ∪ b = b", level: Hard, premises: &["@ext", "a ⊆ b"], conclusion: "a ∪ b = b",
                    hint: "One direction by CD (or cases), the other by Add." },
                Ex { title: "∩ distributes over ∪", level: Hard, premises: &["@ext"], conclusion: "a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c)",
                    hint: "Unfold every membership with Def; the propositional core is Dist." },
            ]),
        chapter(5, "Complements and Powers",
            "Relative complements a − b, De Morgan for sets, and the power set ℘(a).",
            &[
                Ex { title: "a − b ⊆ a", level: Easy, premises: &[], conclusion: "a − b ⊆ a",
                    hint: "Def, Simp." },
                Ex { title: "a ∈ ℘(a)", level: Easy, premises: &[], conclusion: "a ∈ ℘(a)",
                    hint: "Def turns it into a ⊆ a (exercise 1.1)." },
                Ex { title: "∅ ∈ ℘(a)", level: Medium, premises: &[], conclusion: "∅ ∈ ℘(a)",
                    hint: "Def: ∅ ⊆ a (exercise 2.2)." },
                Ex { title: "De Morgan: a − (b ∪ c)", level: Hard, premises: &["@ext"], conclusion: "a − (b ∪ c) = (a − b) ∩ (a − c)",
                    hint: "Unfold; the core is DeM, Dist/Taut and Assoc." },
                Ex { title: "De Morgan: a − (b ∩ c)", level: Hard, premises: &["@ext"], conclusion: "a − (b ∩ c) = (a − b) ∪ (a − c)",
                    hint: "Unfold; DeM then Dist." },
                Ex { title: "℘ is monotone", level: Hard, premises: &["a ⊆ b"], conclusion: "℘(a) ⊆ ℘(b)",
                    hint: "For c ∈ ℘(a): Def gives c ⊆ a, then transitivity (1.3) inside." },
            ]),
        chapter(6, "Ordered Pairs",
            "⟨a, b⟩ = {{a}, {a, b}} (Kuratowski). Def rewrites one into the other.",
            &[
                Ex { title: "{a} ∈ ⟨a, b⟩", level: Easy, premises: &[], conclusion: "{a} ∈ ⟨a, b⟩",
                    hint: "Def to {a} ∈ {{a}, {a, b}}, then Def again: {a} = {a} ∨ {a} = {a, b}." },
                Ex { title: "First coordinates agree", level: Expert, premises: &["⟨a, b⟩ = ⟨c, d⟩"], conclusion: "a = c",
                    hint: "{a} ∈ ⟨a, b⟩ = ⟨c, d⟩, so {a} = {c} or {a} = {c, d}; each case gives a = c." },
            ]),
        chapter(7, "Relations",
            "A relation is a set of ordered pairs. Reflexive, symmetric and transitive relations.",
            &[
                Ex { title: "Symmetric + transitive ⇒ reflexive on the field", level: Hard,
                    premises: &["∀x ∀y(⟨x, y⟩ ∈ r ⊃ ⟨y, x⟩ ∈ r)", "∀x ∀y ∀z((⟨x, y⟩ ∈ r . ⟨y, z⟩ ∈ r) ⊃ ⟨x, z⟩ ∈ r)", "⟨a, b⟩ ∈ r"],
                    conclusion: "⟨a, a⟩ ∈ r",
                    hint: "Symmetry gives ⟨b, a⟩ ∈ r; transitivity with y := b." },
                Ex { title: "Equivalence classes meet only if equal (one direction)", level: Expert,
                    premises: &["∀x ∀y(⟨x, y⟩ ∈ r ⊃ ⟨y, x⟩ ∈ r)", "∀x ∀y ∀z((⟨x, y⟩ ∈ r . ⟨y, z⟩ ∈ r) ⊃ ⟨x, z⟩ ∈ r)", "⟨c, a⟩ ∈ r . ⟨c, b⟩ ∈ r"],
                    conclusion: "∀x(⟨x, a⟩ ∈ r ⊃ ⟨x, b⟩ ∈ r)",
                    hint: "From ⟨c, a⟩ get ⟨a, c⟩; then x ~ a ~ c ~ b." },
            ]),
        chapter(8, "Functions",
            "Fun(f, a, b): f is a function from a to b, an abbreviation for f ⊆ a × b and a unique value for each x in a. Cartesian products a × b.",
            &[
                Ex { title: "A function is a relation from a to b", level: Easy, premises: &["Fun(f, a, b)"], conclusion: "f ⊆ a × b",
                    hint: "Unfold Fun with Def, then Simp." },
                Ex { title: "Every point of a has a value", level: Medium, premises: &["Fun(f, a, b)", "c ∈ a"], conclusion: "∃y(⟨c, y⟩ ∈ f)",
                    hint: "Unfold, Simp, ∀E at c, MP with c ∈ a; ∃E on the value, Simp, ∃I, then close ∃E." },
                Ex { title: "Values are unique", level: Hard, premises: &["Fun(f, a, b)", "c ∈ a", "⟨c, d⟩ ∈ f", "⟨c, e⟩ ∈ f"], conclusion: "d = e",
                    hint: "Both d and e equal the value g given by ∃E; each step is ∀E, MP, then =I and =E to turn g = e into d = e." },
                Ex { title: "Pairs of a and b are in a × b", level: Medium, premises: &["c ∈ a", "d ∈ b"], conclusion: "⟨c, d⟩ ∈ a × b",
                    hint: "Conj the premises with ⟨c, d⟩ = ⟨c, d⟩ (=I), then ∃I twice on the product, then fold with Def." },
            ]),
        chapter(9, "Families",
            "Unions of families: ⋃a collects the members of the members of a. Singletons and pairs of sets give back their members.",
            &[
                Ex { title: "The union of a singleton", level: Medium, premises: &["@ext"], conclusion: "⋃{a} = a",
                    hint: "For c ∈ ⋃{a}: Def gives ∃x(x ∈ {a} . c ∈ x), ∃E on it, then =E turns c ∈ d into c ∈ a. For c ∈ a: ∃I with witness a. Equiv, ∀I, Extension." },
                Ex { title: "The union of a pair", level: Hard, premises: &["@ext"], conclusion: "⋃{a, b} = a ∪ b",
                    hint: "Same shape as 9.1, with two cases: d = a or d = b (Def on d ∈ {a, b}). Each case gives c ∈ a ∪ b; combine them with CD and Taut. The other way, two ∃I witnesses; CD again." },
            ]),
        chapter(10, "Inverses and Composites",
            "Rev(f, g): g is the inverse of f, ⟨x, y⟩ ∈ f iff ⟨y, x⟩ ∈ g. Comp(g, f, h): h = g∘f, first f then g. Both are abbreviations unfolded by Def.",
            &[
                Ex { title: "Inverse reverses a pair", level: Easy, premises: &["Rev(f, g)", "⟨a, b⟩ ∈ f"], conclusion: "⟨b, a⟩ ∈ g",
                    hint: "Def gives ∀x∀y(⟨x, y⟩ ∈ f ≡ ⟨y, x⟩ ∈ g); instantiate twice, Equiv, Simp, then MP." },
                Ex { title: "The inverse of the inverse direction", level: Medium, premises: &["Rev(f, g)"], conclusion: "Rev(g, f)",
                    hint: "Instantiate at d and c with the roles swapped, Equiv, Comm, Equiv again; then ∀I twice and fold with Def." },
                Ex { title: "A composite pair", level: Medium, premises: &["Comp(g, f, h)", "⟨a, b⟩ ∈ f", "⟨b, c⟩ ∈ g"], conclusion: "⟨a, c⟩ ∈ h",
                    hint: "Def and ∀E at a and c; Equiv, then Simp for the direction ∃ ⊃ h. Conj the two premises, ∃I with witness b, MP." },
            ]),
        chapter(11, "Numbers",
            "The successor x ∪ {x}, and the Axiom of Infinity.",
            &[
                Ex { title: "a ∈ a ∪ {a}", level: Easy, premises: &[], conclusion: "a ∈ a ∪ {a}",
                    hint: "Def twice, =I, Add." },
                Ex { title: "There is a set containing 1", level: Medium, premises: &["@inf"], conclusion: "∃s(∅ ∪ {∅} ∈ s)",
                    hint: "∃E on Infinity, Simp, ∀E at ∅, MP, ∃I." },
                Ex { title: "a is included in its successor", level: Medium, premises: &[], conclusion: "a ⊆ a ∪ {a}",
                    hint: "CP on c ∈ a, Add to c ∈ a ∨ c ∈ {a}, Def, ∀I, Def." },
                Ex { title: "The successor is not empty", level: Hard, premises: &[], conclusion: "∅ ≠ a ∪ {a}",
                    hint: "IP: if ∅ = a ∪ {a}, then a ∈ a ∪ {a} gives a ∈ ∅ by =E, and Def gives ⊥." },
            ]),
        chapter(12, "The Peano Axioms",
            "Ind(s): s contains ∅ and the successor x ∪ {x} of each of its elements. The natural numbers are the sets inside every inductive set.",
            &[
                Ex { title: "An inductive set contains ∅", level: Easy, premises: &["Ind(s)"], conclusion: "∅ ∈ s",
                    hint: "Unfold Ind with Def, then Simp." },
                Ex { title: "Successor stays inside", level: Medium, premises: &["Ind(s)", "c ∈ s"], conclusion: "c ∪ {c} ∈ s",
                    hint: "Unfold, Simp for the ∀ part, ∀E at c, MP with c ∈ s." },
                Ex { title: "Inductive sets contain ∅ ∪ {∅}", level: Medium, premises: &["Ind(s)"], conclusion: "∅ ∪ {∅} ∈ s",
                    hint: "Unfold; ∀E at ∅ on the closure clause, MP with ∅ ∈ s." },
                Ex { title: "The intersection of two inductive sets is inductive", level: Hard,
                    premises: &["Ind(s)", "Ind(t)"], conclusion: "Ind(s ∩ t)",
                    hint: "Unfold both; ∅ ∈ s . ∅ ∈ t gives ∅ ∈ s ∩ t. For c ∈ s ∩ t, closure in s and in t, Conj, Def; ∀I; fold." },
            ]),
        chapter(13, "Arithmetic",
            "Addition defined by its two recursion clauses on w. Induction is assumed as a premise instance for each exercise, as the hints say; the instance is itself provable from the least-inductive-set premise and Specification.",
            &[
                Ex { title: "a + 0 = a", level: Easy, premises: &["@add0", "a ∈ w"], conclusion: "p(a, ∅) = a",
                    hint: "∀E on the base clause at a, then MP with a ∈ w." },
                Ex { title: "a + (b ∪ {b}) = (a + b) ∪ {a + b}", level: Medium, premises: &["@adds", "a ∈ w", "b ∈ w"],
                    conclusion: "p(a, b ∪ {b}) = p(a, b) ∪ {p(a, b)}",
                    hint: "∀E twice on the successor clause, Conj for the two hypotheses, MP." },
                Ex { title: "∅ + a = a", level: Hard,
                    premises: &["@add0", "@adds", "@nat", "p(∅, ∅) = ∅ . ∀x((x ∈ w . p(∅, x) = x) ⊃ p(∅, x ∪ {x}) = x ∪ {x}) ⊃ ∀a(a ∈ w ⊃ p(∅, a) = a)", "a ∈ w"],
                    conclusion: "p(∅, a) = a",
                    hint: "Assumed: the induction instance (premise 4, Peano induction for w, §14). Prove its base p(∅,∅)=∅ with the base clause, then its step with the successor clause and =E; MP with the instance." },
            ]),
        chapter(14, "Order",
            "A relation r is transitive when ⟨x, y⟩ ∈ r and ⟨y, z⟩ ∈ r give ⟨x, z⟩ ∈ r, and antisymmetric when ⟨x, y⟩ ∈ r and ⟨y, x⟩ ∈ r give x = y. Def unfolds Trans(r) and Antisym(r) into their quantified clauses.",
            &[
                Ex { title: "Transitivity chains two steps", level: Easy,
                    premises: &["Trans(r)", "⟨a, b⟩ ∈ r", "⟨b, c⟩ ∈ r"], conclusion: "⟨a, c⟩ ∈ r",
                    hint: "Def unfolds Trans(r); ∀E three times with a, b, c; Conj the two pairs; MP." },
                Ex { title: "Antisymmetry on a two-cycle", level: Easy,
                    premises: &["Antisym(r)", "⟨a, b⟩ ∈ r", "⟨b, a⟩ ∈ r"], conclusion: "a = b",
                    hint: "Def unfolds Antisym(r); ∀E twice with a and b; Conj the two pairs; MP." },
                Ex { title: "A three-cycle collapses in a partial order", level: Hard,
                    premises: &["Antisym(r)", "Trans(r)", "⟨a, b⟩ ∈ r", "⟨b, c⟩ ∈ r", "⟨c, a⟩ ∈ r"],
                    conclusion: "a = b . b = c",
                    hint: "Use transitivity to get ⟨b, a⟩ ∈ r and ⟨c, b⟩ ∈ r, then antisymmetry on the pairs (a, b), (b, c)." },
            ]),
        chapter(15, "The Axiom of Choice",
            "Choice in its choice-set form: a disjoint family of nonempty sets has a set meeting each member once. Zorn's lemma: a family in which every chain has its union has a maximal member. Chain(c) is an abbreviation unfolded by Def.",
            &[
                Ex { title: "A choice set exists", level: Medium,
                    premises: &["@choice", "∅ ∉ a", "∀y ∀z((y ∈ a . z ∈ a . y ≠ z) ⊃ y ∩ z = ∅)"],
                    conclusion: "∃u ∀y(y ∈ a ⊃ ∃w ∀z(z ∈ y ∩ u ≡ z = w))",
                    hint: "∀E at a, Conj the two hypotheses, MP." },
                Ex { title: "Zorn gives a maximal member", level: Easy,
                    premises: &["@zorn", "∀c((c ⊆ a . Chain(c)) ⊃ ⋃c ∈ a)"],
                    conclusion: "∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y))",
                    hint: "∀E at a on Zorn's lemma, then MP with the chain hypothesis." },
                Ex { title: "Maximal member, implication form", level: Medium,
                    premises: &["@zorn", "∀c((c ⊆ a . Chain(c)) ⊃ ⋃c ∈ a)"],
                    conclusion: "∃m(m ∈ a . ∀y(y ∈ a ⊃ (m ⊆ y ⊃ m = y)))",
                    hint: "Get the maximal member as in 15.2, open ∃E on it, then Exp on the universal clause and ∃I back." },
            ]),
        chapter(16, "Well-Ordering",
            "WellOrd(r, x): r is a linear order on x in which every nonempty subset of x has an r-least member. The well-ordering theorem gives one for every set.",
            &[
                Ex { title: "Well-ordering theorem gives an order", level: Easy, premises: &["@wo"], conclusion: "∃r WellOrd(r, a)",
                    hint: "∀E at a on the well-ordering schema." },
                Ex { title: "A well-order has least members", level: Medium,
                    premises: &["WellOrd(r, a)", "s ⊆ a", "∃t(t ∈ s)"],
                    conclusion: "∃z(z ∈ s . ∀t(t ∈ s ⊃ (t = z ∨ ⟨z, t⟩ ∈ r)))",
                    hint: "Def unfolds WellOrd(r, a) into three conjuncts; take the last one, ∀E at s, then MP with the two premises about s." },
            ]),
        chapter(17, "Ordinal Numbers",
            "Ord(a): a is transitive, linearly ordered by ∈, and every nonempty subset of a has an ∈-least member. Ord is an abbreviation (Def).",
            &[
                Ex { title: "An ordinal is not a member of itself", level: Medium, premises: &["Ord(a)"], conclusion: "a ∉ a",
                    hint: "IP: assume a ∈ a. Def unfolds Ord(a); take the subset {a} of a, which has a least member l; l = a, but a ∈ l is false, so a ∉ a. Use Def for the singleton." },
                Ex { title: "Membership cycle a∈b∈a gives a∈a", level: Medium, premises: &["Ord(a)", "a ∈ b", "b ∈ a"], conclusion: "a ∈ a",
                    hint: "Ord(a) makes a transitive: b ∈ a gives b ⊆ a. Then a ∈ b puts a in a. Unfold Def and use the transitivity clause of Ord(a)." },
            ]),
        chapter(APPENDIX_KEY, "Foundation (appendix, not in Halmos)",
            "Halmos does not use Foundation; ZFC does. With it no set belongs to itself.",
            &[
                Ex { title: "No set belongs to itself", level: Expert, premises: &["@found"], conclusion: "a ∉ a",
                    hint: "Apply Foundation to {a}: its only element a has no element in common with {a}; but a ∈ a would be one." },
            ]),
    ]
}
