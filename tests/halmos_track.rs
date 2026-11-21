//! Every exercise of the Halmos track has a complete, verified proof here, written in a small
//! script language: `FORMULA :: RULE lines`, `CP> F` / `IP> F` / `∃E> F` to open a subproof,
//! `<CP F` / `<IP F` / `<∃E F` to close one.

use logic_core::models::rules::{EquivalenceRule as Eq, InferenceRule as R, ProofTechnique as T};
use logic_core::models::set_theory::halmos_track;
use logic_core::models::{Formula, Justification, Proof};
use logic_core::services::ProofVerifier;
use std::collections::BTreeMap;

fn technique(s: &str) -> T {
    match s {
        "CP" => T::ConditionalProof,
        "IP" => T::IndirectProof,
        "∃E" => T::ExistentialElimination,
        _ => panic!("unknown technique {s}"),
    }
}

fn justification(rule: &str, lines: Vec<usize>) -> Justification {
    let inference = match rule {
        "MP" => Some(R::ModusPonens),
        "MT" => Some(R::ModusTollens),
        "DS" => Some(R::DisjunctiveSyllogism),
        "Simp" => Some(R::Simplification),
        "Conj" => Some(R::Conjunction),
        "HS" => Some(R::HypotheticalSyllogism),
        "Add" => Some(R::Addition),
        "CD" => Some(R::ConstructiveDilemma),
        "NegE" => Some(R::Contradiction),
        "∀E" => Some(R::UniversalElimination),
        "∀I" => Some(R::UniversalIntroduction),
        "∃I" => Some(R::ExistentialIntroduction),
        "=I" => Some(R::IdentityIntroduction),
        "=E" => Some(R::IdentityElimination),
        _ => None,
    };
    if let Some(rule) = inference {
        return Justification::Inference { rule, lines };
    }
    let rule = match rule {
        "DN" => Eq::DoubleNegation,
        "DeM" => Eq::DeMorgan,
        "Comm" => Eq::Commutation,
        "Assoc" => Eq::Association,
        "Dist" => Eq::Distribution,
        "Contra" => Eq::Contraposition,
        "Impl" => Eq::Implication,
        "Exp" => Eq::Exportation,
        "Taut" => Eq::Tautology,
        "Equiv" => Eq::Equivalence,
        "QN" => Eq::QuantifierNegation,
        "Def" => Eq::Definition,
        _ => panic!("unknown rule {rule}"),
    };
    assert_eq!(lines.len(), 1, "{rule:?} cites one line");
    Justification::Equivalence { rule, line: lines[0] }
}

fn run(proof: &mut Proof, script: &[&str]) {
    for (i, step) in script.iter().enumerate() {
        let n = proof.lines.len() + 1;
        let ctx = || format!("step {} (line {n}) `{step}`", i + 1);
        if let Some((tech, formula)) = step.split_once("> ") {
            proof.open_subproof(Formula::parse(formula).unwrap_or_else(|e| panic!("{}: {e}", ctx())), technique(tech));
        } else if let Some(rest) = step.strip_prefix('<') {
            let (tech, formula) = rest.split_once(' ').unwrap();
            let f = Formula::parse(formula).unwrap_or_else(|e| panic!("{}: {e}", ctx()));
            proof.close_subproof(f, technique(tech)).unwrap_or_else(|| panic!("{}: cannot close", ctx()));
        } else {
            let (formula, just) = step.split_once(" :: ").unwrap_or_else(|| panic!("{}: no ::", ctx()));
            let mut parts = just.split_whitespace();
            let rule = parts.next().unwrap();
            let lines: Vec<usize> = parts
                .flat_map(|p| p.split(','))
                .filter(|p| !p.is_empty())
                .map(|p| p.parse().unwrap())
                .collect();
            let f = Formula::parse(formula).unwrap_or_else(|e| panic!("{}: {e}", ctx()));
            proof.add_line(f, justification(rule, lines));
        }
        let last = proof.lines.len() - 1;
        let r = ProofVerifier::verify_line(&proof.lines[last], proof);
        assert!(r.is_valid, "{}: {}", ctx(), r.message.unwrap_or_default());
        proof.lines[last].is_valid = true;
    }
}

fn solutions() -> BTreeMap<&'static str, Vec<&'static str>> {
    let ext_close = |n: usize, l: &'static str, r: &'static str| -> Vec<String> {
        vec![
            format!("∀y(∀z(z ∈ {l} ≡ z ∈ y) ⊃ {l} = y) :: ∀E 1"),
            format!("∀z(z ∈ {l} ≡ z ∈ {r}) ⊃ {l} = {r} :: ∀E {}", n + 1),
            format!("{l} = {r} :: MP {},{}", n + 2, n),
        ]
    };
    let leak = |v: Vec<String>| -> Vec<&'static str> { v.into_iter().map(|s| &*Box::leak(s.into_boxed_str())).collect() };
    let mut m: BTreeMap<&'static str, Vec<&'static str>> = BTreeMap::new();
    // Chapter 0
    m.insert("halmos-0-1", vec!["F(a) ⊃ G(a) :: ∀E 1", "G(a) :: MP 3,2"]);
    m.insert("halmos-0-2", vec!["∃x F(x) :: ∃I 1"]);
    m.insert("halmos-0-3", vec!["F(a) ⊃ G(a) :: ∀E 1", "F(a) :: ∀E 2", "G(a) :: MP 3,4", "∀x G(x) :: ∀I 5"]);
    m.insert("halmos-0-4", vec![
        "∃E> F(a)", "F(a) ⊃ G(a) :: ∀E 2", "G(a) :: MP 4,3", "∃x G(x) :: ∃I 5", "<∃E ∃x G(x)",
    ]);
    m.insert("halmos-0-5", vec!["∀x ~F(x) :: QN 1"]);
    m.insert("halmos-0-6", vec![
        "F(a) . G(a) :: ∀E 1", "F(a) :: Simp 2", "G(a) :: Simp 2", "∀x F(x) :: ∀I 3", "∀x G(x) :: ∀I 4",
        "∀x F(x) . ∀x G(x) :: Conj 5,6",
    ]);
    m.insert("halmos-0-7", vec!["a = a :: =I", "b = a :: =E 1,2"]);
    m.insert("halmos-0-8", vec!["a = c :: =E 2,1"]);
    m.insert("halmos-0-9", vec![
        "∃E> ∀y R(a, y)", "R(a, b) :: ∀E 2", "∃x R(x, b) :: ∃I 3", "∀y ∃x R(x, y) :: ∀I 4", "<∃E ∀y ∃x R(x, y)",
    ]);
    // Chapter 1
    m.insert("halmos-1-1", vec!["CP> b ∈ a", "<CP b ∈ a ⊃ b ∈ a", "∀x(x ∈ a ⊃ x ∈ a) :: ∀I 2", "a ⊆ a :: Def 3"]);
    m.insert("halmos-1-2", vec![
        "∀y(∀z(z ∈ a ≡ z ∈ y) ⊃ a = y) :: ∀E 1", "∀z(z ∈ a ≡ z ∈ b) ⊃ a = b :: ∀E 3", "a = b :: MP 4,2",
    ]);
    m.insert("halmos-1-3", vec![
        "∀x(x ∈ a ⊃ x ∈ b) :: Def 1", "∀x(x ∈ b ⊃ x ∈ c) :: Def 2", "d ∈ a ⊃ d ∈ b :: ∀E 3", "d ∈ b ⊃ d ∈ c :: ∀E 4",
        "d ∈ a ⊃ d ∈ c :: HS 5,6", "∀x(x ∈ a ⊃ x ∈ c) :: ∀I 7", "a ⊆ c :: Def 8",
    ]);
    m.insert("halmos-1-4", vec![
        "CP> c ∈ a", "<CP c ∈ a ⊃ c ∈ a", "∀x(x ∈ a ⊃ x ∈ a) :: ∀I 3", "a ⊆ a :: Def 4", "a ⊆ b :: =E 1,5",
    ]);
    m.insert("halmos-1-5", {
        let mut v = vec![
            "∀x(x ∈ a ⊃ x ∈ b) :: Def 2", "∀x(x ∈ b ⊃ x ∈ a) :: Def 3", "c ∈ a ⊃ c ∈ b :: ∀E 4", "c ∈ b ⊃ c ∈ a :: ∀E 5",
            "(c ∈ a ⊃ c ∈ b) . (c ∈ b ⊃ c ∈ a) :: Conj 6,7", "c ∈ a ≡ c ∈ b :: Equiv 8", "∀z(z ∈ a ≡ z ∈ b) :: ∀I 9",
        ];
        v.extend(leak(ext_close(10, "a", "b")));
        v
    });
    m.insert("halmos-1-6", {
        let mut v = vec![
            "CP> a = b", "CP> c ∈ a", "<CP c ∈ a ⊃ c ∈ a", "∀x(x ∈ a ⊃ x ∈ a) :: ∀I 4", "a ⊆ a :: Def 5",
            "a ⊆ b :: =E 2,6", "b ⊆ a :: =E 2,6", "a ⊆ b . b ⊆ a :: Conj 7,8", "<CP a = b ⊃ (a ⊆ b . b ⊆ a)",
            "CP> a ⊆ b . b ⊆ a", "a ⊆ b :: Simp 11", "b ⊆ a :: Simp 11", "∀x(x ∈ a ⊃ x ∈ b) :: Def 12",
            "∀x(x ∈ b ⊃ x ∈ a) :: Def 13", "d ∈ a ⊃ d ∈ b :: ∀E 14", "d ∈ b ⊃ d ∈ a :: ∀E 15",
            "(d ∈ a ⊃ d ∈ b) . (d ∈ b ⊃ d ∈ a) :: Conj 16,17", "d ∈ a ≡ d ∈ b :: Equiv 18",
            "∀z(z ∈ a ≡ z ∈ b) :: ∀I 19",
        ];
        v.extend(leak(ext_close(20, "a", "b")));
        v.extend([
            "<CP (a ⊆ b . b ⊆ a) ⊃ a = b",
            "[a = b ⊃ (a ⊆ b . b ⊆ a)] . [(a ⊆ b . b ⊆ a) ⊃ a = b] :: Conj 10,24",
            "a = b ≡ (a ⊆ b . b ⊆ a) :: Equiv 25",
        ]);
        v
    });
    // Chapter 2
    m.insert("halmos-2-1", vec!["IP> b ∈ ∅", "⊥ :: Def 1", "<IP b ∉ ∅", "∀x(x ∉ ∅) :: ∀I 3"]);
    m.insert("halmos-2-2", vec![
        "CP> b ∈ ∅", "IP> b ∉ a", "⊥ :: Def 1", "<IP b ∈ a", "<CP b ∈ ∅ ⊃ b ∈ a", "∀x(x ∈ ∅ ⊃ x ∈ a) :: ∀I 5",
        "∅ ⊆ a :: Def 6",
    ]);
    m.insert("halmos-2-3", {
        let mut v = vec![
            "c ∉ a :: ∀E 2", "c ∉ b :: ∀E 3", "c ∉ a ∨ c ∈ b :: Add 4", "c ∈ a ⊃ c ∈ b :: Impl 6",
            "c ∉ b ∨ c ∈ a :: Add 5", "c ∈ b ⊃ c ∈ a :: Impl 8", "(c ∈ a ⊃ c ∈ b) . (c ∈ b ⊃ c ∈ a) :: Conj 7,9",
            "c ∈ a ≡ c ∈ b :: Equiv 10", "∀z(z ∈ a ≡ z ∈ b) :: ∀I 11",
        ];
        v.extend(leak(ext_close(12, "a", "b")));
        v
    });
    m.insert("halmos-2-4", {
        let mut v = vec![
            "∀x(x ∈ a ⊃ x ∈ ∅) :: Def 2", "c ∈ a ⊃ c ∈ ∅ :: ∀E 3", "CP> c ∈ ∅", "IP> c ∉ a", "⊥ :: Def 5",
            "<IP c ∈ a", "<CP c ∈ ∅ ⊃ c ∈ a", "(c ∈ a ⊃ c ∈ ∅) . (c ∈ ∅ ⊃ c ∈ a) :: Conj 4,9",
            "c ∈ a ≡ c ∈ ∅ :: Equiv 10", "∀z(z ∈ a ≡ z ∈ ∅) :: ∀I 11",
        ];
        v.extend(leak(ext_close(12, "a", "∅")));
        v
    });
    m.insert("halmos-2-5", vec![
        "∃E> a = a", "∃y ∀z(z ∈ y ≡ (z ∈ a . z ≠ z)) :: ∀E 2", "∃E> ∀z(z ∈ b ≡ (z ∈ a . z ≠ z))",
        "c ∈ b ≡ (c ∈ a . c ≠ c) :: ∀E 5", "IP> c ∈ b",
        "[c ∈ b ⊃ (c ∈ a . c ≠ c)] . [(c ∈ a . c ≠ c) ⊃ c ∈ b] :: Equiv 6", "c ∈ b ⊃ (c ∈ a . c ≠ c) :: Simp 8",
        "c ∈ a . c ≠ c :: MP 9,7", "c ≠ c :: Simp 10", "c = c :: =I", "⊥ :: NegE 11,12", "<IP c ∉ b",
        "∀z(z ∉ b) :: ∀I 14", "∃y ∀z(z ∉ y) :: ∃I 15", "<∃E ∃y ∀z(z ∉ y)", "<∃E ∃y ∀z(z ∉ y)",
    ]);
    m.insert("halmos-2-6", vec![
        "∃y ∀z(z ∈ y ≡ (z ∈ a . z ∉ z)) :: ∀E 1", "∃E> ∀z(z ∈ b ≡ (z ∈ a . z ∉ z))",
        "b ∈ b ≡ (b ∈ a . b ∉ b) :: ∀E 3", "IP> b ∈ a",
        "[b ∈ b ⊃ (b ∈ a . b ∉ b)] . [(b ∈ a . b ∉ b) ⊃ b ∈ b] :: Equiv 4", "b ∈ b ⊃ (b ∈ a . b ∉ b) :: Simp 6",
        "(b ∈ a . b ∉ b) ⊃ b ∈ b :: Simp 6", "IP> b ∈ b", "b ∈ a . b ∉ b :: MP 7,9", "b ∉ b :: Simp 10",
        "⊥ :: NegE 9,11", "<IP b ∉ b", "b ∈ a . b ∉ b :: Conj 5,13", "b ∈ b :: MP 8,14", "⊥ :: NegE 15,13",
        "<IP b ∉ a", "∃y(y ∉ a) :: ∃I 17", "<∃E ∃y(y ∉ a)", "∀x ∃y(y ∉ x) :: ∀I 19",
    ]);
    // Chapter 3
    m.insert("halmos-3-1", vec!["a = a :: =I", "a ∈ {a} :: Def 1"]);
    m.insert("halmos-3-2", vec!["a = a :: =I", "a = a ∨ a = b :: Add 1", "a ∈ {a, b} :: Def 2"]);
    m.insert("halmos-3-3", vec![
        "∀y ∃w ∀z(z ∈ w ≡ (z = a ∨ z = y)) :: ∀E 1", "∃w ∀z(z ∈ w ≡ (z = a ∨ z = b)) :: ∀E 2",
        "∃E> ∀z(z ∈ c ≡ (z = a ∨ z = b))", "a ∈ c ≡ (a = a ∨ a = b) :: ∀E 4", "b ∈ c ≡ (b = a ∨ b = b) :: ∀E 4",
        "[a ∈ c ⊃ (a = a ∨ a = b)] . [(a = a ∨ a = b) ⊃ a ∈ c] :: Equiv 5", "(a = a ∨ a = b) ⊃ a ∈ c :: Simp 7",
        "a = a :: =I", "a = a ∨ a = b :: Add 9", "a ∈ c :: MP 8,10",
        "[b ∈ c ⊃ (b = a ∨ b = b)] . [(b = a ∨ b = b) ⊃ b ∈ c] :: Equiv 6", "(b = a ∨ b = b) ⊃ b ∈ c :: Simp 12",
        "b = b :: =I", "b = a ∨ b = b :: Add 14", "b ∈ c :: MP 13,15", "a ∈ c . b ∈ c :: Conj 11,16",
        "∃w(a ∈ w . b ∈ w) :: ∃I 17", "<∃E ∃w(a ∈ w . b ∈ w)",
    ]);
    m.insert("halmos-3-4", vec!["a = a :: =I", "a ∈ {a} :: Def 2", "a ∈ {b} :: =E 1,3", "a = b :: Def 4"]);
    m.insert("halmos-3-5", {
        let mut v = vec![
            "CP> c ∈ {a, b}", "c = a ∨ c = b :: Def 2", "c = b ∨ c = a :: Comm 3", "c ∈ {b, a} :: Def 4",
            "<CP c ∈ {a, b} ⊃ c ∈ {b, a}", "CP> c ∈ {b, a}", "c = b ∨ c = a :: Def 7", "c = a ∨ c = b :: Comm 8",
            "c ∈ {a, b} :: Def 9", "<CP c ∈ {b, a} ⊃ c ∈ {a, b}",
            "(c ∈ {a, b} ⊃ c ∈ {b, a}) . (c ∈ {b, a} ⊃ c ∈ {a, b}) :: Conj 6,11",
            "c ∈ {a, b} ≡ c ∈ {b, a} :: Equiv 12", "∀z(z ∈ {a, b} ≡ z ∈ {b, a}) :: ∀I 13",
        ];
        v.extend(leak(ext_close(14, "{a, b}", "{b, a}")));
        v
    });
    m.insert("halmos-3-6", {
        let mut v = vec![
            "CP> c ∈ {a}", "c = a :: Def 2", "c = a ∨ c = a :: Taut 3", "c ∈ {a, a} :: Def 4", "<CP c ∈ {a} ⊃ c ∈ {a, a}",
            "CP> c ∈ {a, a}", "c = a ∨ c = a :: Def 7", "c = a :: Taut 8", "c ∈ {a} :: Def 9",
            "<CP c ∈ {a, a} ⊃ c ∈ {a}", "(c ∈ {a} ⊃ c ∈ {a, a}) . (c ∈ {a, a} ⊃ c ∈ {a}) :: Conj 6,11",
            "c ∈ {a} ≡ c ∈ {a, a} :: Equiv 12", "∀z(z ∈ {a} ≡ z ∈ {a, a}) :: ∀I 13",
        ];
        v.extend(leak(ext_close(14, "{a}", "{a, a}")));
        v
    });
    // Chapter 4
    m.insert("halmos-4-1", vec![
        "CP> c ∈ a", "c ∈ a ∨ c ∈ b :: Add 1", "c ∈ a ∪ b :: Def 2", "<CP c ∈ a ⊃ c ∈ a ∪ b",
        "∀x(x ∈ a ⊃ x ∈ a ∪ b) :: ∀I 4", "a ⊆ a ∪ b :: Def 5",
    ]);
    m.insert("halmos-4-2", vec![
        "CP> c ∈ a ∩ b", "c ∈ a . c ∈ b :: Def 1", "c ∈ a :: Simp 2", "<CP c ∈ a ∩ b ⊃ c ∈ a",
        "∀x(x ∈ a ∩ b ⊃ x ∈ a) :: ∀I 4", "a ∩ b ⊆ a :: Def 5",
    ]);
    for (id, op, conn) in [("halmos-4-3", "∪", "∨"), ("halmos-4-4", "∩", ".")] {
        let lab = format!("a {op} b");
        let lba = format!("b {op} a");
        let mut v = leak(vec![
            format!("CP> c ∈ {lab}"),
            format!("c ∈ a {conn} c ∈ b :: Def 2"),
            format!("c ∈ b {conn} c ∈ a :: Comm 3"),
            format!("c ∈ {lba} :: Def 4"),
            format!("<CP c ∈ {lab} ⊃ c ∈ {lba}"),
            format!("CP> c ∈ {lba}"),
            format!("c ∈ b {conn} c ∈ a :: Def 7"),
            format!("c ∈ a {conn} c ∈ b :: Comm 8"),
            format!("c ∈ {lab} :: Def 9"),
            format!("<CP c ∈ {lba} ⊃ c ∈ {lab}"),
            format!("(c ∈ {lab} ⊃ c ∈ {lba}) . (c ∈ {lba} ⊃ c ∈ {lab}) :: Conj 6,11"),
            format!("c ∈ {lab} ≡ c ∈ {lba} :: Equiv 12"),
            format!("∀z(z ∈ {lab} ≡ z ∈ {lba}) :: ∀I 13"),
        ]);
        v.extend(leak(ext_close(14, Box::leak(lab.into_boxed_str()), Box::leak(lba.into_boxed_str()))));
        m.insert(id, v);
    }
    m.insert("halmos-4-5", {
        let mut v = vec![
            "CP> c ∈ a ∪ ∅", "c ∈ a ∨ c ∈ ∅ :: Def 2", "c ∈ a ∨ ⊥ :: Def 3", "IP> c ∉ a", "⊥ :: DS 4,5",
            "<IP c ∈ a", "<CP c ∈ a ∪ ∅ ⊃ c ∈ a", "CP> c ∈ a", "c ∈ a ∨ c ∈ ∅ :: Add 9", "c ∈ a ∪ ∅ :: Def 10",
            "<CP c ∈ a ⊃ c ∈ a ∪ ∅", "(c ∈ a ∪ ∅ ⊃ c ∈ a) . (c ∈ a ⊃ c ∈ a ∪ ∅) :: Conj 8,12",
            "c ∈ a ∪ ∅ ≡ c ∈ a :: Equiv 13", "∀z(z ∈ a ∪ ∅ ≡ z ∈ a) :: ∀I 14",
        ];
        v.extend(leak(ext_close(15, "a ∪ ∅", "a")));
        v
    });
    m.insert("halmos-4-6", {
        let mut v = vec![
            "CP> c ∈ a ∪ a", "c ∈ a ∨ c ∈ a :: Def 2", "c ∈ a :: Taut 3", "<CP c ∈ a ∪ a ⊃ c ∈ a", "CP> c ∈ a",
            "c ∈ a ∨ c ∈ a :: Taut 6", "c ∈ a ∪ a :: Def 7", "<CP c ∈ a ⊃ c ∈ a ∪ a",
            "(c ∈ a ∪ a ⊃ c ∈ a) . (c ∈ a ⊃ c ∈ a ∪ a) :: Conj 5,9", "c ∈ a ∪ a ≡ c ∈ a :: Equiv 10",
            "∀z(z ∈ a ∪ a ≡ z ∈ a) :: ∀I 11",
        ];
        v.extend(leak(ext_close(12, "a ∪ a", "a")));
        v
    });
    m.insert("halmos-4-7", {
        let mut v = vec![
            "∀x(x ∈ a ⊃ x ∈ b) :: Def 2", "c ∈ a ⊃ c ∈ b :: ∀E 3", "CP> c ∈ a ∪ b", "c ∈ a ∨ c ∈ b :: Def 5",
            "CP> c ∈ b", "<CP c ∈ b ⊃ c ∈ b", "c ∈ b ∨ c ∈ b :: CD 6,4,8", "c ∈ b :: Taut 9", "<CP c ∈ a ∪ b ⊃ c ∈ b",
            "CP> c ∈ b", "c ∈ a ∨ c ∈ b :: Add 12", "c ∈ a ∪ b :: Def 13", "<CP c ∈ b ⊃ c ∈ a ∪ b",
            "(c ∈ a ∪ b ⊃ c ∈ b) . (c ∈ b ⊃ c ∈ a ∪ b) :: Conj 11,15", "c ∈ a ∪ b ≡ c ∈ b :: Equiv 16",
            "∀z(z ∈ a ∪ b ≡ z ∈ b) :: ∀I 17",
        ];
        v.extend(leak(ext_close(18, "a ∪ b", "b")));
        v
    });
    m.insert("halmos-4-8", {
        let mut v = vec![
            "CP> d ∈ a ∩ (b ∪ c)", "d ∈ a . d ∈ b ∪ c :: Def 2", "d ∈ a . (d ∈ b ∨ d ∈ c) :: Def 3",
            "(d ∈ a . d ∈ b) ∨ (d ∈ a . d ∈ c) :: Dist 4", "d ∈ a ∩ b ∨ (d ∈ a . d ∈ c) :: Def 5",
            "d ∈ a ∩ b ∨ d ∈ a ∩ c :: Def 6", "d ∈ (a ∩ b) ∪ (a ∩ c) :: Def 7",
            "<CP d ∈ a ∩ (b ∪ c) ⊃ d ∈ (a ∩ b) ∪ (a ∩ c)",
            "CP> d ∈ (a ∩ b) ∪ (a ∩ c)", "d ∈ a ∩ b ∨ d ∈ a ∩ c :: Def 10", "(d ∈ a . d ∈ b) ∨ d ∈ a ∩ c :: Def 11",
            "(d ∈ a . d ∈ b) ∨ (d ∈ a . d ∈ c) :: Def 12", "d ∈ a . (d ∈ b ∨ d ∈ c) :: Dist 13",
            "d ∈ a . d ∈ b ∪ c :: Def 14", "d ∈ a ∩ (b ∪ c) :: Def 15", "<CP d ∈ (a ∩ b) ∪ (a ∩ c) ⊃ d ∈ a ∩ (b ∪ c)",
            "(d ∈ a ∩ (b ∪ c) ⊃ d ∈ (a ∩ b) ∪ (a ∩ c)) . (d ∈ (a ∩ b) ∪ (a ∩ c) ⊃ d ∈ a ∩ (b ∪ c)) :: Conj 9,17",
            "d ∈ a ∩ (b ∪ c) ≡ d ∈ (a ∩ b) ∪ (a ∩ c) :: Equiv 18",
            "∀z(z ∈ a ∩ (b ∪ c) ≡ z ∈ (a ∩ b) ∪ (a ∩ c)) :: ∀I 19",
        ];
        v.extend(leak(ext_close(20, "a ∩ (b ∪ c)", "(a ∩ b) ∪ (a ∩ c)")));
        v
    });
    // Chapter 5
    m.insert("halmos-5-1", vec![
        "CP> c ∈ a − b", "c ∈ a . c ∉ b :: Def 1", "c ∈ a :: Simp 2", "<CP c ∈ a − b ⊃ c ∈ a",
        "∀x(x ∈ a − b ⊃ x ∈ a) :: ∀I 4", "a − b ⊆ a :: Def 5",
    ]);
    m.insert("halmos-5-2", vec![
        "CP> b ∈ a", "<CP b ∈ a ⊃ b ∈ a", "∀x(x ∈ a ⊃ x ∈ a) :: ∀I 2", "a ⊆ a :: Def 3", "a ∈ ℘(a) :: Def 4",
    ]);
    m.insert("halmos-5-3", vec![
        "CP> b ∈ ∅", "IP> b ∉ a", "⊥ :: Def 1", "<IP b ∈ a", "<CP b ∈ ∅ ⊃ b ∈ a", "∀x(x ∈ ∅ ⊃ x ∈ a) :: ∀I 5",
        "∅ ⊆ a :: Def 6", "∅ ∈ ℘(a) :: Def 7",
    ]);
    m.insert("halmos-5-4", {
        let mut v = vec![
            "CP> d ∈ a − (b ∪ c)", "d ∈ a . d ∉ b ∪ c :: Def 2", "d ∈ a . ~(d ∈ b ∨ d ∈ c) :: Def 3",
            "d ∈ a . (d ∉ b . d ∉ c) :: DeM 4", "d ∈ a :: Simp 5", "d ∉ b . d ∉ c :: Simp 5", "d ∉ b :: Simp 7",
            "d ∉ c :: Simp 7", "d ∈ a . d ∉ b :: Conj 6,8", "d ∈ a . d ∉ c :: Conj 6,9", "d ∈ a − b :: Def 10",
            "d ∈ a − c :: Def 11", "d ∈ a − b . d ∈ a − c :: Conj 12,13", "d ∈ (a − b) ∩ (a − c) :: Def 14",
            "<CP d ∈ a − (b ∪ c) ⊃ d ∈ (a − b) ∩ (a − c)",
            "CP> d ∈ (a − b) ∩ (a − c)", "d ∈ a − b . d ∈ a − c :: Def 17", "d ∈ a − b :: Simp 18",
            "d ∈ a − c :: Simp 18", "d ∈ a . d ∉ b :: Def 19", "d ∈ a . d ∉ c :: Def 20", "d ∈ a :: Simp 21",
            "d ∉ b :: Simp 21", "d ∉ c :: Simp 22", "d ∉ b . d ∉ c :: Conj 24,25", "~(d ∈ b ∨ d ∈ c) :: DeM 26",
            "d ∉ b ∪ c :: Def 27", "d ∈ a . d ∉ b ∪ c :: Conj 23,28", "d ∈ a − (b ∪ c) :: Def 29",
            "<CP d ∈ (a − b) ∩ (a − c) ⊃ d ∈ a − (b ∪ c)",
            "(d ∈ a − (b ∪ c) ⊃ d ∈ (a − b) ∩ (a − c)) . (d ∈ (a − b) ∩ (a − c) ⊃ d ∈ a − (b ∪ c)) :: Conj 16,31",
            "d ∈ a − (b ∪ c) ≡ d ∈ (a − b) ∩ (a − c) :: Equiv 32",
            "∀z(z ∈ a − (b ∪ c) ≡ z ∈ (a − b) ∩ (a − c)) :: ∀I 33",
        ];
        v.extend(leak(ext_close(34, "a − (b ∪ c)", "(a − b) ∩ (a − c)")));
        v
    });
    m.insert("halmos-5-5", {
        let mut v = vec![
            "CP> d ∈ a − (b ∩ c)", "d ∈ a . d ∉ b ∩ c :: Def 2", "d ∈ a . ~(d ∈ b . d ∈ c) :: Def 3",
            "d ∈ a . (d ∉ b ∨ d ∉ c) :: DeM 4", "(d ∈ a . d ∉ b) ∨ (d ∈ a . d ∉ c) :: Dist 5",
            "d ∈ a − b ∨ (d ∈ a . d ∉ c) :: Def 6", "d ∈ a − b ∨ d ∈ a − c :: Def 7", "d ∈ (a − b) ∪ (a − c) :: Def 8",
            "<CP d ∈ a − (b ∩ c) ⊃ d ∈ (a − b) ∪ (a − c)",
            "CP> d ∈ (a − b) ∪ (a − c)", "d ∈ a − b ∨ d ∈ a − c :: Def 11", "(d ∈ a . d ∉ b) ∨ d ∈ a − c :: Def 12",
            "(d ∈ a . d ∉ b) ∨ (d ∈ a . d ∉ c) :: Def 13", "d ∈ a . (d ∉ b ∨ d ∉ c) :: Dist 14",
            "d ∈ a . ~(d ∈ b . d ∈ c) :: DeM 15", "d ∈ a . d ∉ b ∩ c :: Def 16", "d ∈ a − (b ∩ c) :: Def 17",
            "<CP d ∈ (a − b) ∪ (a − c) ⊃ d ∈ a − (b ∩ c)",
            "(d ∈ a − (b ∩ c) ⊃ d ∈ (a − b) ∪ (a − c)) . (d ∈ (a − b) ∪ (a − c) ⊃ d ∈ a − (b ∩ c)) :: Conj 10,19",
            "d ∈ a − (b ∩ c) ≡ d ∈ (a − b) ∪ (a − c) :: Equiv 20",
            "∀z(z ∈ a − (b ∩ c) ≡ z ∈ (a − b) ∪ (a − c)) :: ∀I 21",
        ];
        v.extend(leak(ext_close(22, "a − (b ∩ c)", "(a − b) ∪ (a − c)")));
        v
    });
    m.insert("halmos-5-6", vec![
        "∀x(x ∈ a ⊃ x ∈ b) :: Def 1", "CP> c ∈ ℘(a)", "c ⊆ a :: Def 3", "∀x(x ∈ c ⊃ x ∈ a) :: Def 4",
        "d ∈ c ⊃ d ∈ a :: ∀E 5", "d ∈ a ⊃ d ∈ b :: ∀E 2", "d ∈ c ⊃ d ∈ b :: HS 6,7", "∀x(x ∈ c ⊃ x ∈ b) :: ∀I 8",
        "c ⊆ b :: Def 9", "c ∈ ℘(b) :: Def 10", "<CP c ∈ ℘(a) ⊃ c ∈ ℘(b)", "∀x(x ∈ ℘(a) ⊃ x ∈ ℘(b)) :: ∀I 12",
        "℘(a) ⊆ ℘(b) :: Def 13",
    ]);
    // Chapter 6
    m.insert("halmos-6-1", vec![
        "{a} = {a} :: =I", "{a} = {a} ∨ {a} = {a, b} :: Add 1", "{a} ∈ {{a}, {a, b}} :: Def 2", "{a} ∈ ⟨a, b⟩ :: Def 3",
    ]);
    m.insert("halmos-6-2", vec![
        "{a} = {a} :: =I", "{a} = {a} ∨ {a} = {a, b} :: Add 2", "{a} ∈ {{a}, {a, b}} :: Def 3", "{a} ∈ ⟨a, b⟩ :: Def 4",
        "{a} ∈ ⟨c, d⟩ :: =E 1,5", "{a} ∈ {{c}, {c, d}} :: Def 6", "{a} = {c} ∨ {a} = {c, d} :: Def 7",
        "CP> {a} = {c}", "a = a :: =I", "a ∈ {a} :: Def 10", "a ∈ {c} :: =E 9,11", "a = c :: Def 12",
        "<CP {a} = {c} ⊃ a = c", "CP> {a} = {c, d}", "c = c :: =I", "c = c ∨ c = d :: Add 16", "c ∈ {c, d} :: Def 17",
        "c ∈ {a} :: =E 15,18", "c = a :: Def 19", "a = a :: =I", "a = c :: =E 20,21", "<CP {a} = {c, d} ⊃ a = c",
        "a = c ∨ a = c :: CD 8,14,23", "a = c :: Taut 24",
    ]);
    // Chapter 7
    m.insert("halmos-7-1", vec![
        "∀y(⟨a, y⟩ ∈ r ⊃ ⟨y, a⟩ ∈ r) :: ∀E 1", "⟨a, b⟩ ∈ r ⊃ ⟨b, a⟩ ∈ r :: ∀E 4", "⟨b, a⟩ ∈ r :: MP 5,3",
        "∀y ∀z((⟨a, y⟩ ∈ r . ⟨y, z⟩ ∈ r) ⊃ ⟨a, z⟩ ∈ r) :: ∀E 2",
        "∀z((⟨a, b⟩ ∈ r . ⟨b, z⟩ ∈ r) ⊃ ⟨a, z⟩ ∈ r) :: ∀E 7", "(⟨a, b⟩ ∈ r . ⟨b, a⟩ ∈ r) ⊃ ⟨a, a⟩ ∈ r :: ∀E 8",
        "⟨a, b⟩ ∈ r . ⟨b, a⟩ ∈ r :: Conj 3,6", "⟨a, a⟩ ∈ r :: MP 9,10",
    ]);
    m.insert("halmos-7-2", vec![
        "⟨c, a⟩ ∈ r :: Simp 3", "⟨c, b⟩ ∈ r :: Simp 3", "∀y(⟨c, y⟩ ∈ r ⊃ ⟨y, c⟩ ∈ r) :: ∀E 1",
        "⟨c, a⟩ ∈ r ⊃ ⟨a, c⟩ ∈ r :: ∀E 6", "⟨a, c⟩ ∈ r :: MP 7,4", "CP> ⟨d, a⟩ ∈ r",
        "∀y ∀z((⟨d, y⟩ ∈ r . ⟨y, z⟩ ∈ r) ⊃ ⟨d, z⟩ ∈ r) :: ∀E 2",
        "∀z((⟨d, a⟩ ∈ r . ⟨a, z⟩ ∈ r) ⊃ ⟨d, z⟩ ∈ r) :: ∀E 10", "(⟨d, a⟩ ∈ r . ⟨a, c⟩ ∈ r) ⊃ ⟨d, c⟩ ∈ r :: ∀E 11",
        "⟨d, a⟩ ∈ r . ⟨a, c⟩ ∈ r :: Conj 9,8", "⟨d, c⟩ ∈ r :: MP 12,13",
        "∀z((⟨d, c⟩ ∈ r . ⟨c, z⟩ ∈ r) ⊃ ⟨d, z⟩ ∈ r) :: ∀E 10", "(⟨d, c⟩ ∈ r . ⟨c, b⟩ ∈ r) ⊃ ⟨d, b⟩ ∈ r :: ∀E 15",
        "⟨d, c⟩ ∈ r . ⟨c, b⟩ ∈ r :: Conj 14,5", "⟨d, b⟩ ∈ r :: MP 16,17", "<CP ⟨d, a⟩ ∈ r ⊃ ⟨d, b⟩ ∈ r",
        "∀x(⟨x, a⟩ ∈ r ⊃ ⟨x, b⟩ ∈ r) :: ∀I 19",
    ]);
    // Chapter 11
    m.insert("halmos-11-1", vec!["a = a :: =I", "a ∈ {a} :: Def 1", "a ∈ a ∨ a ∈ {a} :: Add 2", "a ∈ a ∪ {a} :: Def 3"]);
    m.insert("halmos-11-2", vec![
        "∃E> ∅ ∈ a . ∀y(y ∈ a ⊃ y ∪ {y} ∈ a)", "∅ ∈ a :: Simp 2", "∀y(y ∈ a ⊃ y ∪ {y} ∈ a) :: Simp 2",
        "∅ ∈ a ⊃ ∅ ∪ {∅} ∈ a :: ∀E 4", "∅ ∪ {∅} ∈ a :: MP 5,3", "∃x(∅ ∪ {∅} ∈ x) :: ∃I 6", "<∃E ∃x(∅ ∪ {∅} ∈ x)",
    ]);
    // Chapter 15
    m.insert("halmos-15-1", vec![
        "(∅ ∉ a . ∀y ∀z((y ∈ a . z ∈ a . y ≠ z) ⊃ y ∩ z = ∅)) ⊃ ∃u ∀y(y ∈ a ⊃ ∃w ∀z(z ∈ y ∩ u ≡ z = w)) :: ∀E 1",
        "∅ ∉ a . ∀y ∀z((y ∈ a . z ∈ a . y ≠ z) ⊃ y ∩ z = ∅) :: Conj 2,3",
        "∃u ∀y(y ∈ a ⊃ ∃w ∀z(z ∈ y ∩ u ≡ z = w)) :: MP 4,5",
    ]);
    // Chapter 19
    m.insert("halmos-19-1", vec![
        "∃y(y ∈ {a}) ⊃ ∃y(y ∈ {a} . ~∃z(z ∈ y . z ∈ {a})) :: ∀E 1", "a = a :: =I", "a ∈ {a} :: Def 3",
        "∃y(y ∈ {a}) :: ∃I 4", "∃y(y ∈ {a} . ~∃z(z ∈ y . z ∈ {a})) :: MP 2,5", "IP> a ∈ a",
        "∃E> b ∈ {a} . ~∃z(z ∈ b . z ∈ {a})", "b ∈ {a} :: Simp 8", "b = a :: Def 9",
        "~∃z(z ∈ b . z ∈ {a}) :: Simp 8", "~∃z(z ∈ a . z ∈ {a}) :: =E 10,11", "a ∈ a . a ∈ {a} :: Conj 7,4",
        "∃z(z ∈ a . z ∈ {a}) :: ∃I 13", "⊥ :: NegE 14,12", "<∃E ⊥", "<IP a ∉ a",
    ]);
    m
}

#[test]
fn every_exercise_has_a_verified_solution() {
    let sols = solutions();
    let mut seen = 0;
    for ch in halmos_track() {
        for ex in &ch.exercises {
            let script = sols.get(ex.id.as_str()).unwrap_or_else(|| panic!("no solution for {}", ex.id));
            let mut p = Proof::new(ex.theorem.clone());
            run(&mut p, script);
            assert!(p.check_complete(), "{} ({}) is not complete", ex.id, ex.title);
            seen += 1;
        }
    }
    assert_eq!(seen, sols.len(), "solutions for exercises that do not exist");
}

#[test]
fn chapters_are_in_halmos_order_and_axioms_appear_once() {
    let track = halmos_track();
    let numbers: Vec<u8> = track.iter().map(|c| c.number).collect();
    let mut sorted = numbers.clone();
    sorted.sort();
    assert_eq!(numbers, sorted);
    let ids: Vec<String> = track.iter().flat_map(|c| c.axioms.iter().map(|a| a.id.clone())).collect();
    assert_eq!(ids.len(), 10);
    for ch in &track {
        for ex in &ch.exercises {
            for ax in &ex.axioms {
                let introduced = track.iter().find(|c| c.axioms.iter().any(|a| &a.id == ax)).unwrap();
                assert!(introduced.number <= ch.number, "{} uses {} before it is introduced", ex.id, ax);
            }
        }
    }
}
