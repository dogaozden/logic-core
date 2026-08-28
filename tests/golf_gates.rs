use logic_core::models::rules::InferenceRule;
use logic_core::models::{Difficulty, Formula, Justification, Proof, Theorem};
use logic_core::services::{golf_gate, plant, GateConfig, GateReject, PlantSpec, PlantedCandidate};

fn f(s: &str) -> Formula {
    Formula::parse(s).unwrap()
}

fn theorem(premises: Vec<Formula>, conclusion: Formula) -> Theorem {
    Theorem::new(premises, conclusion, Difficulty::Medium, None, None)
}

/// Build a hand-crafted `PlantedCandidate`, bypassing `plant` entirely.
/// `lines` are appended on top of the theorem's auto-seeded premise lines
/// via `Proof::add_line` (flat, top-level only — no gate exercised below
/// needs a subproof). `golf_gate`'s early stages (size, cheese) only ever
/// inspect `theorem.premises`/`theorem.conclusion`, so `lines` is `vec![]`
/// for every test here except the greedy one, which needs a real body for
/// `c.par` to mean anything.
fn hand_built(premises: Vec<Formula>, conclusion: Formula, lines: Vec<(Formula, Justification)>) -> PlantedCandidate {
    let th = theorem(premises, conclusion);
    let mut proof = Proof::new(th.clone());
    for (formula, justification) in lines {
        proof.add_line(formula, justification);
    }
    let par = proof.lines.len() - th.premises.len();
    PlantedCandidate { theorem: th, proof, par, seed: 0 }
}

#[test]
fn mp_only_two_liner_is_greedy_provable() {
    // P, P>Q, Q>R |- R via two Modus Ponens steps: exactly the grind a
    // diligent-but-strategically-blind philosopher solves unaided.
    let premises = vec![f("P"), f("P > Q"), f("Q > R")];
    let conclusion = f("R");
    let lines = vec![
        (f("Q"), Justification::Inference { rule: InferenceRule::ModusPonens, lines: vec![1, 2] }),
        (f("R"), Justification::Inference { rule: InferenceRule::ModusPonens, lines: vec![3, 4] }),
    ];
    let c = hand_built(premises, conclusion, lines);
    assert_eq!(c.par, 2);

    match golf_gate(&c, &GateConfig::default()) {
        Err(GateReject::GreedyProvable { lines }) => {
            assert_eq!(lines, 2, "philosopher should solve this in exactly 2 MP steps");
        }
        other => panic!("expected GreedyProvable, got {other:?}"),
    }
}

#[test]
fn tautologous_disjunct_conclusion_is_cheese() {
    // "P > P" is independently a tautology, so the whole disjunction is
    // provable via Add without ever touching "Q" — decoration, not content.
    let conclusion = f("Q v (P > P)");
    let c = hand_built(vec![], conclusion, vec![]);

    match golf_gate(&c, &GateConfig::default()) {
        Err(GateReject::Cheese(msg)) => {
            assert!(msg.contains("tautologous disjunct"), "unexpected message: {msg}");
        }
        other => panic!("expected Cheese(tautologous disjunct), got {other:?}"),
    }
}

#[test]
fn disguised_identity_conclusion_is_cheese() {
    // "(P . Q) > (Q . P)": the antecedent rewrites to the consequent in one
    // Commutation step — "prove A > B" is secretly "restate A".
    let conclusion = f("(P . Q) > (Q . P)");
    let c = hand_built(vec![], conclusion, vec![]);

    match golf_gate(&c, &GateConfig::default()) {
        Err(GateReject::Cheese(msg)) => {
            assert!(msg.contains("disguised identity"), "unexpected message: {msg}");
        }
        other => panic!("expected Cheese(disguised identity), got {other:?}"),
    }
}

#[test]
fn over_length_conclusion_is_too_big() {
    // Right-nested Or chain over 25 distinct atoms, built via direct AST
    // construction (not the string parser) so its length is guaranteed
    // regardless of parser/bracketing formatting quirks.
    let long = (0..25).rev().fold(Formula::Atom("Z".to_string()), |acc, i| {
        Formula::Or(Box::new(Formula::Atom(format!("A{i}"))), Box::new(acc))
    });
    let cfg = GateConfig::default();
    assert!(
        long.ascii_string_bracketed().chars().count() > cfg.max_formula_len,
        "test formula must actually exceed max_formula_len to be a meaningful TooBig witness"
    );

    let c = hand_built(vec![], long, vec![]);
    assert_eq!(golf_gate(&c, &cfg), Err(GateReject::TooBig));
}

/// Small, rule-only (no subproofs) spec whose par-6 output sits well within
/// the lawyer probe's default reach (12 lines / 200k nodes / 64 equiv).
fn probe_reach_spec() -> PlantSpec {
    PlantSpec {
        atoms: 3,
        par_min: 6,
        par_max: 6,
        max_premises: 4,
        max_formula_len: 90,
        subproofs: 0,
        obfuscation_passes: 0,
    }
}

#[test]
fn plant_generated_par_6_is_cracked_by_lawyer_probe() {
    let spec = probe_reach_spec();
    // Pinned by seed search (see task-6-report.md): seed 1 under
    // `probe_reach_spec()` plants an exact par-6 candidate whose real
    // minimal proof is only 4 lines — well within the lawyer probe's
    // default reach (12 lines / 200k nodes / 64 equiv) — so the probe finds
    // it and `golf_gate` rejects, proving the probe genuinely bites rather
    // than rubber-stamping every par-6 candidate. Determinism (`plant` is a
    // pure function of seed + spec) makes this reproducible forever.
    let seed = 1u64;
    let c = plant(&spec, seed).unwrap_or_else(|e| panic!("pinned seed {seed} must plant: {e:?}"));
    assert_eq!(c.par, 6, "pinned seed must be an exact par-6 candidate");

    match golf_gate(&c, &GateConfig::default()) {
        Err(GateReject::LawyerProbeCracked { lines }) => {
            assert_eq!(lines, 4, "pinned seed's minimal proof is 4 lines — confirms determinism, not just the reject variant");
            assert!(lines <= GateConfig::default().probe.max_lines);
        }
        other => panic!("expected LawyerProbeCracked for pinned seed {seed}, got {other:?}"),
    }
}
