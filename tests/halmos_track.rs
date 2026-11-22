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
    // Chapter 8
    m.insert("halmos-8-1", vec![
        "f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Def 1", "f ⊆ a × b :: Simp 2",
    ]);
    m.insert("halmos-8-2", vec![
        "f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Def 1",
        "∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Simp 3",
        "c ∈ a ⊃ ∃y(⟨c, y⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = y)) :: ∀E 4",
        "∃y(⟨c, y⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = y)) :: MP 5,2",
        "∃E> ⟨c, d⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = d)",
        "⟨c, d⟩ ∈ f :: Simp 7",
        "∃y(⟨c, y⟩ ∈ f) :: ∃I 8",
        "<∃E ∃y(⟨c, y⟩ ∈ f)",
    ]);
    m.insert("halmos-8-3", vec![
        "f ⊆ a × b . ∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Def 1",
        "∀x(x ∈ a ⊃ ∃y(⟨x, y⟩ ∈ f . ∀z(⟨x, z⟩ ∈ f ⊃ z = y))) :: Simp 5",
        "c ∈ a ⊃ ∃y(⟨c, y⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = y)) :: ∀E 6",
        "∃y(⟨c, y⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = y)) :: MP 7,2",
        "∃E> ⟨c, g⟩ ∈ f . ∀z(⟨c, z⟩ ∈ f ⊃ z = g)",
        "⟨c, g⟩ ∈ f :: Simp 9",
        "∀z(⟨c, z⟩ ∈ f ⊃ z = g) :: Simp 9",
        "⟨c, d⟩ ∈ f ⊃ d = g :: ∀E 11",
        "d = g :: MP 12,3",
        "⟨c, e⟩ ∈ f ⊃ e = g :: ∀E 11",
        "e = g :: MP 14,4",
        "e = e :: =I",
        "g = e :: =E 15,16",
        "d = e :: =E 17,13",
        "<∃E d = e",
    ]);
    m.insert("halmos-8-4", vec![
        "c ∈ a . d ∈ b :: Conj 1,2",
        "⟨c, d⟩ = ⟨c, d⟩ :: =I",
        "c ∈ a . d ∈ b . ⟨c, d⟩ = ⟨c, d⟩ :: Conj 3,4",
        "∃y(c ∈ a . y ∈ b . ⟨c, d⟩ = ⟨c, y⟩) :: ∃I 5",
        "∃x ∃y(x ∈ a . y ∈ b . ⟨c, d⟩ = ⟨x, y⟩) :: ∃I 6",
        "⟨c, d⟩ ∈ a × b :: Def 7",
    ]);
    // Chapter 9
    m.insert("halmos-9-1", {
        let mut v = vec![
            "CP> c ∈ ⋃{a}", "∃x(x ∈ {a} . c ∈ x) :: Def 2", "∃E> d ∈ {a} . c ∈ d", "d ∈ {a} :: Simp 4", "d = a :: Def 5",
            "c ∈ d :: Simp 4", "c ∈ a :: =E 6,7", "<∃E c ∈ a", "<CP c ∈ ⋃{a} ⊃ c ∈ a", "CP> c ∈ a", "a = a :: =I",
            "a ∈ {a} :: Def 12", "a ∈ {a} . c ∈ a :: Conj 13,11", "∃x(x ∈ {a} . c ∈ x) :: ∃I 14", "c ∈ ⋃{a} :: Def 15",
            "<CP c ∈ a ⊃ c ∈ ⋃{a}", "(c ∈ ⋃{a} ⊃ c ∈ a) . (c ∈ a ⊃ c ∈ ⋃{a}) :: Conj 10,17", "c ∈ ⋃{a} ≡ c ∈ a :: Equiv 18",
            "∀z(z ∈ ⋃{a} ≡ z ∈ a) :: ∀I 19",
        ];
        v.extend(leak(ext_close(20, "⋃{a}", "a")));
        v
    });
    m.insert("halmos-9-2", {
        let mut v = vec![
            "CP> c ∈ ⋃{a, b}", "∃x(x ∈ {a, b} . c ∈ x) :: Def 2", "∃E> d ∈ {a, b} . c ∈ d", "d ∈ {a, b} :: Simp 4",
            "d = a ∨ d = b :: Def 5", "c ∈ d :: Simp 4",
            "CP> d = a", "c ∈ a :: =E 8,7", "c ∈ a ∨ c ∈ b :: Add 9", "c ∈ a ∪ b :: Def 10", "<CP d = a ⊃ c ∈ a ∪ b",
            "CP> d = b", "c ∈ b :: =E 13,7", "c ∈ a ∨ c ∈ b :: Add 14", "c ∈ a ∪ b :: Def 15", "<CP d = b ⊃ c ∈ a ∪ b",
            "c ∈ a ∪ b ∨ c ∈ a ∪ b :: CD 6,12,17", "c ∈ a ∪ b :: Taut 18", "<∃E c ∈ a ∪ b", "<CP c ∈ ⋃{a, b} ⊃ c ∈ a ∪ b",
            "CP> c ∈ a ∪ b", "c ∈ a ∨ c ∈ b :: Def 22", "CP> c ∈ a", "a = a :: =I", "a = a ∨ a = b :: Add 25",
            "a ∈ {a, b} :: Def 26", "a ∈ {a, b} . c ∈ a :: Conj 27,24", "∃x(x ∈ {a, b} . c ∈ x) :: ∃I 28", "c ∈ ⋃{a, b} :: Def 29",
            "<CP c ∈ a ⊃ c ∈ ⋃{a, b}", "CP> c ∈ b", "b = b :: =I", "b = a ∨ b = b :: Add 33", "b ∈ {a, b} :: Def 34",
            "b ∈ {a, b} . c ∈ b :: Conj 35,32", "∃x(x ∈ {a, b} . c ∈ x) :: ∃I 36", "c ∈ ⋃{a, b} :: Def 37",
            "<CP c ∈ b ⊃ c ∈ ⋃{a, b}", "c ∈ ⋃{a, b} ∨ c ∈ ⋃{a, b} :: CD 23,31,39", "c ∈ ⋃{a, b} :: Taut 40",
            "<CP c ∈ a ∪ b ⊃ c ∈ ⋃{a, b}",
            "(c ∈ ⋃{a, b} ⊃ c ∈ a ∪ b) . (c ∈ a ∪ b ⊃ c ∈ ⋃{a, b}) :: Conj 21,42", "c ∈ ⋃{a, b} ≡ c ∈ a ∪ b :: Equiv 43",
            "∀z(z ∈ ⋃{a, b} ≡ z ∈ a ∪ b) :: ∀I 44",
        ];
        v.extend(leak(ext_close(45, "⋃{a, b}", "a ∪ b")));
        v
    });
    // Chapter 10
    m.insert("halmos-10-1", vec![
        "∀x∀y(⟨x, y⟩ ∈ f ≡ ⟨y, x⟩ ∈ g) :: Def 1", "∀y(⟨a, y⟩ ∈ f ≡ ⟨y, a⟩ ∈ g) :: ∀E 3",
        "⟨a, b⟩ ∈ f ≡ ⟨b, a⟩ ∈ g :: ∀E 4",
        "(⟨a, b⟩ ∈ f ⊃ ⟨b, a⟩ ∈ g) . (⟨b, a⟩ ∈ g ⊃ ⟨a, b⟩ ∈ f) :: Equiv 5",
        "⟨a, b⟩ ∈ f ⊃ ⟨b, a⟩ ∈ g :: Simp 6", "⟨b, a⟩ ∈ g :: MP 7,2",
    ]);
    m.insert("halmos-10-2", vec![
        "∀x∀y(⟨x, y⟩ ∈ f ≡ ⟨y, x⟩ ∈ g) :: Def 1", "∀y(⟨d, y⟩ ∈ f ≡ ⟨y, d⟩ ∈ g) :: ∀E 2",
        "⟨d, c⟩ ∈ f ≡ ⟨c, d⟩ ∈ g :: ∀E 3",
        "(⟨d, c⟩ ∈ f ⊃ ⟨c, d⟩ ∈ g) . (⟨c, d⟩ ∈ g ⊃ ⟨d, c⟩ ∈ f) :: Equiv 4",
        "(⟨c, d⟩ ∈ g ⊃ ⟨d, c⟩ ∈ f) . (⟨d, c⟩ ∈ f ⊃ ⟨c, d⟩ ∈ g) :: Comm 5",
        "⟨c, d⟩ ∈ g ≡ ⟨d, c⟩ ∈ f :: Equiv 6",
        "∀y(⟨c, y⟩ ∈ g ≡ ⟨y, c⟩ ∈ f) :: ∀I 7",
        "∀x∀y(⟨x, y⟩ ∈ g ≡ ⟨y, x⟩ ∈ f) :: ∀I 8",
        "Rev(g, f) :: Def 9",
    ]);
    m.insert("halmos-10-3", vec![
        "∀x∀y(⟨x, y⟩ ∈ h ≡ ∃z(⟨x, z⟩ ∈ f . ⟨z, y⟩ ∈ g)) :: Def 1",
        "∀y(⟨a, y⟩ ∈ h ≡ ∃z(⟨a, z⟩ ∈ f . ⟨z, y⟩ ∈ g)) :: ∀E 4",
        "⟨a, c⟩ ∈ h ≡ ∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g) :: ∀E 5",
        "(⟨a, c⟩ ∈ h ⊃ ∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g)) . (∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g) ⊃ ⟨a, c⟩ ∈ h) :: Equiv 6",
        "∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g) ⊃ ⟨a, c⟩ ∈ h :: Simp 7",
        "⟨a, b⟩ ∈ f . ⟨b, c⟩ ∈ g :: Conj 2,3",
        "∃z(⟨a, z⟩ ∈ f . ⟨z, c⟩ ∈ g) :: ∃I 9",
        "⟨a, c⟩ ∈ h :: MP 8,10",
    ]);
    m.insert("halmos-11-3", vec![
        "CP> c ∈ a", "c ∈ a ∨ c ∈ {a} :: Add 1", "c ∈ a ∪ {a} :: Def 2", "<CP c ∈ a ⊃ c ∈ a ∪ {a}",
        "∀x(x ∈ a ⊃ x ∈ a ∪ {a}) :: ∀I 4", "a ⊆ a ∪ {a} :: Def 5",
    ]);
    m.insert("halmos-11-4", vec![
        "IP> ∅ = a ∪ {a}", "a = a :: =I", "a ∈ {a} :: Def 2", "a ∈ a ∨ a ∈ {a} :: Add 3", "a ∈ a ∪ {a} :: Def 4",
        "a ∈ ∅ :: =E 1,5", "⊥ :: Def 6", "<IP ∅ ≠ a ∪ {a}",
    ]);
    // Chapter 14 (Halmos §16 Order)
    m.insert("halmos-14-1", vec![
        "∀x∀y∀z((⟨x, y⟩ ∈ r . ⟨y, z⟩ ∈ r) ⊃ ⟨x, z⟩ ∈ r) :: Def 1",
        "∀y∀z((⟨a, y⟩ ∈ r . ⟨y, z⟩ ∈ r) ⊃ ⟨a, z⟩ ∈ r) :: ∀E 4",
        "∀z((⟨a, b⟩ ∈ r . ⟨b, z⟩ ∈ r) ⊃ ⟨a, z⟩ ∈ r) :: ∀E 5",
        "(⟨a, b⟩ ∈ r . ⟨b, c⟩ ∈ r) ⊃ ⟨a, c⟩ ∈ r :: ∀E 6",
        "⟨a, b⟩ ∈ r . ⟨b, c⟩ ∈ r :: Conj 2,3",
        "⟨a, c⟩ ∈ r :: MP 7,8",
    ]);
    m.insert("halmos-14-2", vec![
        "∀x∀y((⟨x, y⟩ ∈ r . ⟨y, x⟩ ∈ r) ⊃ x = y) :: Def 1",
        "∀y((⟨a, y⟩ ∈ r . ⟨y, a⟩ ∈ r) ⊃ a = y) :: ∀E 4",
        "(⟨a, b⟩ ∈ r . ⟨b, a⟩ ∈ r) ⊃ a = b :: ∀E 5",
        "⟨a, b⟩ ∈ r . ⟨b, a⟩ ∈ r :: Conj 2,3",
        "a = b :: MP 6,7",
    ]);
    m.insert("halmos-14-3", vec![
        "∀x∀y((⟨x, y⟩ ∈ r . ⟨y, x⟩ ∈ r) ⊃ x = y) :: Def 1",
        "∀x∀y∀z((⟨x, y⟩ ∈ r . ⟨y, z⟩ ∈ r) ⊃ ⟨x, z⟩ ∈ r) :: Def 2",
        "∀y∀z((⟨b, y⟩ ∈ r . ⟨y, z⟩ ∈ r) ⊃ ⟨b, z⟩ ∈ r) :: ∀E 7",
        "∀z((⟨b, c⟩ ∈ r . ⟨c, z⟩ ∈ r) ⊃ ⟨b, z⟩ ∈ r) :: ∀E 8",
        "(⟨b, c⟩ ∈ r . ⟨c, a⟩ ∈ r) ⊃ ⟨b, a⟩ ∈ r :: ∀E 9",
        "⟨b, c⟩ ∈ r . ⟨c, a⟩ ∈ r :: Conj 4,5",
        "⟨b, a⟩ ∈ r :: MP 10,11",
        "∀y((⟨a, y⟩ ∈ r . ⟨y, a⟩ ∈ r) ⊃ a = y) :: ∀E 6",
        "(⟨a, b⟩ ∈ r . ⟨b, a⟩ ∈ r) ⊃ a = b :: ∀E 13",
        "⟨a, b⟩ ∈ r . ⟨b, a⟩ ∈ r :: Conj 3,12",
        "a = b :: MP 14,15",
        "∀y∀z((⟨c, y⟩ ∈ r . ⟨y, z⟩ ∈ r) ⊃ ⟨c, z⟩ ∈ r) :: ∀E 7",
        "∀z((⟨c, a⟩ ∈ r . ⟨a, z⟩ ∈ r) ⊃ ⟨c, z⟩ ∈ r) :: ∀E 17",
        "(⟨c, a⟩ ∈ r . ⟨a, b⟩ ∈ r) ⊃ ⟨c, b⟩ ∈ r :: ∀E 18",
        "⟨c, a⟩ ∈ r . ⟨a, b⟩ ∈ r :: Conj 5,3",
        "⟨c, b⟩ ∈ r :: MP 19,20",
        "∀y((⟨b, y⟩ ∈ r . ⟨y, b⟩ ∈ r) ⊃ b = y) :: ∀E 6",
        "(⟨b, c⟩ ∈ r . ⟨c, b⟩ ∈ r) ⊃ b = c :: ∀E 22",
        "⟨b, c⟩ ∈ r . ⟨c, b⟩ ∈ r :: Conj 4,21",
        "b = c :: MP 23,24",
        "a = b . b = c :: Conj 16,25",
    ]);
    // Chapter 13 (Halmos §15 Arithmetic)
    m.insert("halmos-13-1", vec!["a ∈ w ⊃ p(a, ∅) = a :: ∀E 1", "p(a, ∅) = a :: MP 3,2"]);
    m.insert("halmos-13-2", vec![
        "∀y((a ∈ w . y ∈ w) ⊃ p(a, y ∪ {y}) = p(a, y) ∪ {p(a, y)}) :: ∀E 1",
        "(a ∈ w . b ∈ w) ⊃ p(a, b ∪ {b}) = p(a, b) ∪ {p(a, b)} :: ∀E 4",
        "a ∈ w . b ∈ w :: Conj 2,3",
        "p(a, b ∪ {b}) = p(a, b) ∪ {p(a, b)} :: MP 5,6",
    ]);
    m.insert("halmos-13-3", vec![
        "Ind(w) :: Simp 3",
        "∅ ∈ w . ∀x(x ∈ w ⊃ x ∪ {x} ∈ w) :: Def 6",
        "∅ ∈ w :: Simp 7",
        "∅ ∈ w ⊃ p(∅, ∅) = ∅ :: ∀E 1",
        "p(∅, ∅) = ∅ :: MP 9,8",
        "∀y((∅ ∈ w . y ∈ w) ⊃ p(∅, y ∪ {y}) = p(∅, y) ∪ {p(∅, y)}) :: ∀E 2",
        "CP> x ∈ w . p(∅, x) = x",
        "x ∈ w :: Simp 12",
        "p(∅, x) = x :: Simp 12",
        "∅ ∈ w . x ∈ w :: Conj 8,13",
        "(∅ ∈ w . x ∈ w) ⊃ p(∅, x ∪ {x}) = p(∅, x) ∪ {p(∅, x)} :: ∀E 11",
        "p(∅, x ∪ {x}) = p(∅, x) ∪ {p(∅, x)} :: MP 16,15",
        "p(∅, x ∪ {x}) = x ∪ {x} :: =E 14,17",
        "<CP x ∈ w . p(∅, x) = x ⊃ p(∅, x ∪ {x}) = x ∪ {x}",
        "∀x((x ∈ w . p(∅, x) = x) ⊃ p(∅, x ∪ {x}) = x ∪ {x}) :: ∀I 19",
        "p(∅, ∅) = ∅ . ∀x((x ∈ w . p(∅, x) = x) ⊃ p(∅, x ∪ {x}) = x ∪ {x}) :: Conj 10,20",
        "∀a(a ∈ w ⊃ p(∅, a) = a) :: MP 4,21",
        "a ∈ w ⊃ p(∅, a) = a :: ∀E 22",
        "p(∅, a) = a :: MP 23,5",
    ]);
    // Chapter 12
    m.insert("halmos-12-1", vec!["∅ ∈ s . ∀x(x ∈ s ⊃ x ∪ {x} ∈ s) :: Def 1", "∅ ∈ s :: Simp 2"]);
    m.insert("halmos-12-2", vec![
        "∅ ∈ s . ∀x(x ∈ s ⊃ x ∪ {x} ∈ s) :: Def 1", "∅ ∈ s :: Simp 3", "∀x(x ∈ s ⊃ x ∪ {x} ∈ s) :: Simp 3",
        "c ∈ s ⊃ c ∪ {c} ∈ s :: ∀E 5", "c ∪ {c} ∈ s :: MP 6,2",
    ]);
    m.insert("halmos-12-3", vec![
        "∅ ∈ s . ∀x(x ∈ s ⊃ x ∪ {x} ∈ s) :: Def 1", "∅ ∈ s :: Simp 2", "∀x(x ∈ s ⊃ x ∪ {x} ∈ s) :: Simp 2",
        "∅ ∈ s ⊃ ∅ ∪ {∅} ∈ s :: ∀E 4", "∅ ∪ {∅} ∈ s :: MP 5,3",
    ]);
    m.insert("halmos-12-4", vec![
        "∅ ∈ s . ∀x(x ∈ s ⊃ x ∪ {x} ∈ s) :: Def 1", "∅ ∈ t . ∀x(x ∈ t ⊃ x ∪ {x} ∈ t) :: Def 2",
        "∅ ∈ s :: Simp 3", "∀x(x ∈ s ⊃ x ∪ {x} ∈ s) :: Simp 3", "∅ ∈ t :: Simp 4", "∀x(x ∈ t ⊃ x ∪ {x} ∈ t) :: Simp 4",
        "∅ ∈ s . ∅ ∈ t :: Conj 5,7", "∅ ∈ s ∩ t :: Def 9",
        "CP> c ∈ s ∩ t", "c ∈ s . c ∈ t :: Def 11", "c ∈ s :: Simp 12", "c ∈ t :: Simp 12",
        "c ∈ s ⊃ c ∪ {c} ∈ s :: ∀E 6", "c ∪ {c} ∈ s :: MP 15,13", "c ∈ t ⊃ c ∪ {c} ∈ t :: ∀E 8",
        "c ∪ {c} ∈ t :: MP 17,14", "c ∪ {c} ∈ s . c ∪ {c} ∈ t :: Conj 16,18", "c ∪ {c} ∈ s ∩ t :: Def 19",
        "<CP c ∈ s ∩ t ⊃ c ∪ {c} ∈ s ∩ t", "∀x(x ∈ s ∩ t ⊃ x ∪ {x} ∈ s ∩ t) :: ∀I 21",
        "∅ ∈ s ∩ t . ∀x(x ∈ s ∩ t ⊃ x ∪ {x} ∈ s ∩ t) :: Conj 10,22", "Ind(s ∩ t) :: Def 23",
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
    m.insert("halmos-15-2", vec![
        "(∀c((c ⊆ a . Chain(c)) ⊃ ⋃c ∈ a)) ⊃ ∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y)) :: ∀E 1",
        "∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y)) :: MP 3,2",
    ]);
    m.insert("halmos-15-3", vec![
        "(∀c((c ⊆ a . Chain(c)) ⊃ ⋃c ∈ a)) ⊃ ∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y)) :: ∀E 1",
        "∃m(m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y)) :: MP 3,2",
        "∃E> m ∈ a . ∀y((y ∈ a . m ⊆ y) ⊃ m = y)",
        "m ∈ a :: Simp 5",
        "∀y((y ∈ a . m ⊆ y) ⊃ m = y) :: Simp 5",
        "((d ∈ a . m ⊆ d) ⊃ m = d) :: ∀E 7",
        "d ∈ a ⊃ (m ⊆ d ⊃ m = d) :: Exp 8",
        "∀y(y ∈ a ⊃ (m ⊆ y ⊃ m = y)) :: ∀I 9",
        "m ∈ a . ∀y(y ∈ a ⊃ (m ⊆ y ⊃ m = y)) :: Conj 6,10",
        "∃m(m ∈ a . ∀y(y ∈ a ⊃ (m ⊆ y ⊃ m = y))) :: ∃I 11",
        "<∃E ∃m(m ∈ a . ∀y(y ∈ a ⊃ (m ⊆ y ⊃ m = y)))",
    ]);
    m.insert("halmos-16-1", vec!["∃r WellOrd(r, a) :: ∀E 1"]);
    m.insert("halmos-16-2", vec![
        "r ⊆ a × a . ∀u∀v((u ∈ a . v ∈ a) ⊃ (⟨u, v⟩ ∈ r ∨ u = v ∨ ⟨v, u⟩ ∈ r)) . ∀k((k ⊆ a . ∃t(t ∈ k)) ⊃ ∃z(z ∈ k . ∀t(t ∈ k ⊃ (t = z ∨ ⟨z, t⟩ ∈ r)))) :: Def 1",
        "∀k((k ⊆ a . ∃t(t ∈ k)) ⊃ ∃z(z ∈ k . ∀t(t ∈ k ⊃ (t = z ∨ ⟨z, t⟩ ∈ r)))) :: Simp 4",
        "(s ⊆ a . ∃t(t ∈ s)) ⊃ ∃z(z ∈ s . ∀t(t ∈ s ⊃ (t = z ∨ ⟨z, t⟩ ∈ r))) :: ∀E 5",
        "s ⊆ a . ∃t(t ∈ s) :: Conj 2,3",
        "∃z(z ∈ s . ∀t(t ∈ s ⊃ (t = z ∨ ⟨z, t⟩ ∈ r))) :: MP 6,7",
    ]);
    m.insert("halmos-17-1", vec![
        "IP> a ∈ a",
        "∀x(x ∈ a ⊃ x ⊆ a) . ∀u∀v((u ∈ a . v ∈ a) ⊃ (u ∈ v ∨ u = v ∨ v ∈ u)) . ∀s((s ⊆ a . ∃t(t ∈ s)) ⊃ ∃l(l ∈ s . ∀t(t ∈ s ⊃ ~(t ∈ l)))) :: Def 1",
        "∀s((s ⊆ a . ∃t(t ∈ s)) ⊃ ∃l(l ∈ s . ∀t(t ∈ s ⊃ ~(t ∈ l)))) :: Simp 3",
        "({a} ⊆ a . ∃t(t ∈ {a})) ⊃ ∃l(l ∈ {a} . ∀t(t ∈ {a} ⊃ ~(t ∈ l))) :: ∀E 4",
        "CP> d ∈ {a}",
        "d = a :: Def 6",
        "d = d :: =I",
        "a = d :: =E 7,8",
        "d ∈ a :: =E 9,2",
        "<CP d ∈ {a} ⊃ d ∈ a",
        "∀x(x ∈ {a} ⊃ x ∈ a) :: ∀I 11",
        "{a} ⊆ a :: Def 12",
        "a = a :: =I",
        "a ∈ {a} :: Def 14",
        "∃t(t ∈ {a}) :: ∃I 15",
        "{a} ⊆ a . ∃t(t ∈ {a}) :: Conj 13,16",
        "∃l(l ∈ {a} . ∀t(t ∈ {a} ⊃ ~(t ∈ l))) :: MP 5,17",
        "∃E> l ∈ {a} . ∀t(t ∈ {a} ⊃ ~(t ∈ l))",
        "l ∈ {a} :: Simp 19",
        "∀t(t ∈ {a} ⊃ ~(t ∈ l)) :: Simp 19",
        "a ∈ {a} ⊃ ~(a ∈ l) :: ∀E 21",
        "~(a ∈ l) :: MP 22,15",
        "l = a :: Def 20",
        "~(a ∈ a) :: =E 24,23",
        "⊥ :: NegE 2,25",
        "<∃E ⊥",
        "<IP a ∉ a",
    ]);
    // Chapter 19
    m.insert("halmos-18-1", vec![
        "CP> (Ord(a) . ∀x(x ∈ a ⊃ ~(x ∈ x)))",
        "∀x(x ∈ a ⊃ ~(x ∈ x)) :: Simp 2",
        "IP> a ∈ a",
        "a ∈ a ⊃ ~(a ∈ a) :: ∀E 3",
        "~(a ∈ a) :: MP 5,4",
        "⊥ :: NegE 4,6",
        "<IP ~(a ∈ a)",
        "<CP (Ord(a) . ∀x(x ∈ a ⊃ ~(x ∈ x))) ⊃ ~(a ∈ a)",
        "∀a((Ord(a) . ∀x(x ∈ a ⊃ ~(x ∈ x))) ⊃ ~(a ∈ a)) :: ∀I 9",
        "∀a(Ord(a) ⊃ ~(a ∈ a)) :: MP 1,10",
    ]);
    m.insert("halmos-17-2", vec![
        "∀x(x ∈ a ⊃ x ⊆ a) . ∀u∀v((u ∈ a . v ∈ a) ⊃ (u ∈ v ∨ u = v ∨ v ∈ u)) . ∀s((s ⊆ a . ∃t(t ∈ s)) ⊃ ∃l(l ∈ s . ∀t(t ∈ s ⊃ ~(t ∈ l)))) :: Def 1",
        "∀x(x ∈ a ⊃ x ⊆ a) . ∀u∀v((u ∈ a . v ∈ a) ⊃ (u ∈ v ∨ u = v ∨ v ∈ u)) :: Simp 4",
        "∀x(x ∈ a ⊃ x ⊆ a) :: Simp 5",
        "b ∈ a ⊃ b ⊆ a :: ∀E 6",
        "b ⊆ a :: MP 7,3",
        "∀x(x ∈ b ⊃ x ∈ a) :: Def 8",
        "a ∈ b ⊃ a ∈ a :: ∀E 9",
        "a ∈ a :: MP 10,2",
    ]);
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
    let numbers: Vec<Option<u8>> = track.iter().map(|c| c.number).collect();
    let mut sorted = numbers.clone();
    sorted.sort_by_key(|n| n.unwrap_or(u8::MAX));
    assert_eq!(numbers, sorted, "sections ascend, the appendix (None) last");
    assert!(numbers.iter().flatten().all(|n| *n <= 21), "every section is one Halmos section (1–21)");
    let ids: Vec<String> = track.iter().flat_map(|c| c.axioms.iter().map(|a| a.id.clone())).collect();
    assert_eq!(ids.len(), 15);
    for ch in &track {
        for ex in &ch.exercises {
            for ax in &ex.axioms {
                let introduced = track.iter().find(|c| c.axioms.iter().any(|a| &a.id == ax)).unwrap();
                assert!(introduced.number <= ch.number || ch.number.is_none(), "{} uses {} before it is introduced", ex.id, ax);
            }
        }
    }
}
