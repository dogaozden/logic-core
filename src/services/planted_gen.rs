//! Forward proof construction ("planting"): build a proof premises → conclusion
//! by growing a derivation tree with real inference/equivalence rule
//! applications, then extract the theorem whose witness proof is exactly that
//! derivation's dependency cone.
//!
//! Every `PlantedCandidate` carries a proof that is natively valid and
//! complete by construction (rule-only in this task; Tasks 4-6 layer subproof
//! planting, obfuscation, and gate checks on top of this same scratch/cone
//! machinery).

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::models::{Difficulty, Formula, Justification, Proof, Theorem};
use crate::models::rules::{EquivalenceRule, InferenceRule};
use crate::services::obfuscate_gen::build_atom_pool;
use crate::services::verifier::ProofVerifier;

/// Low weight given to equivalence steps vs. inference steps during growth.
const EQUIVALENCE_STEP_WEIGHT: f64 = 0.15;

/// Configuration for a single forward-planted candidate.
#[derive(Debug, Clone)]
pub struct PlantSpec {
    /// Atom pool size, 3..=6 (pool via `build_atom_pool`).
    pub atoms: u8,
    pub par_min: usize,
    pub par_max: usize,
    /// Premises are sampled 2..=max_premises (default 5).
    pub max_premises: usize,
    /// `ascii_string_bracketed` char cap for any formula produced (default 90).
    pub max_formula_len: usize,
    /// 0 for this task; Task 4 activates 1..=2.
    pub subproofs: u8,
    /// 0 for this task; Task 5 activates.
    pub obfuscation_passes: u8,
}

/// A forward-planted candidate: a theorem paired with a witness proof that is
/// valid and complete by construction.
#[derive(Debug, Clone)]
pub struct PlantedCandidate {
    /// Premises = cone leaves, conclusion = cone root.
    pub theorem: Theorem,
    /// The planted proof, natively valid & complete.
    pub proof: Proof,
    /// `proof.lines.len() - theorem.premises.len()`.
    pub par: usize,
    pub seed: u64,
}

/// Construction failed for this seed; the caller resamples with the next seed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlantError {
    /// Growth could not produce a single derived line.
    Stuck,
    /// Growth succeeded, but the largest cone found falls outside `[par_min, par_max]`.
    OutOfBand,
}

/// Build a proof forward (premises → rules → conclusion) and extract the
/// theorem whose witness proof is exactly the resulting derivation's
/// dependency cone.
///
/// Pure function of `(spec, seed)`: the only randomness is a `StdRng` seeded
/// right here, so the same seed + spec always produces byte-identical output.
pub fn plant(spec: &PlantSpec, seed: u64) -> Result<PlantedCandidate, PlantError> {
    let mut rng = StdRng::seed_from_u64(seed);
    let atoms = build_atom_pool(spec.atoms);

    // Step 2: sample premises.
    let premises = sample_premises(&mut rng, &atoms, spec);
    let n_premises = premises.len();

    // Scratch derivation list: premises first, 1-based line numbers matching
    // eventual proof line numbers if nothing were ever pruned.
    let mut scratch: Vec<(Formula, Justification)> = premises
        .into_iter()
        .map(|f| (f, Justification::Premise))
        .collect();
    // consumed[i] = how many times scratch line (i+1) has been cited so far.
    let mut consumed: Vec<usize> = vec![0; n_premises];

    // Step 3: grow the derivation until the band is plausibly reachable.
    let derived_target = spec.par_max.saturating_mul(2).max(8);
    let max_attempts = (derived_target * 20).max(120);
    let mut derived_count = 0usize;
    let mut attempts = 0usize;
    while derived_count < derived_target && attempts < max_attempts {
        attempts += 1;
        let grew = if rng.gen::<f64>() < EQUIVALENCE_STEP_WEIGHT {
            try_equivalence_step(&mut scratch, &mut consumed, &mut rng, spec)
        } else {
            try_inference_step(&mut scratch, &mut consumed, &mut rng, spec, &atoms)
        };
        if grew {
            derived_count += 1;
        }
    }

    if derived_count == 0 {
        return Err(PlantError::Stuck);
    }

    // Step 4: pick the conclusion = derived line with the largest dependency cone.
    let mut best: Option<(usize, Vec<usize>, usize)> = None; // (line, cone, derived_in_cone)
    for pos in (n_premises + 1)..=scratch.len() {
        let cone = compute_cone(&scratch, pos);
        let derived_in_cone = cone.iter().filter(|&&i| i > n_premises).count();
        let is_better = match &best {
            None => true,
            Some((_, _, best_derived)) => derived_in_cone > *best_derived,
        };
        if is_better {
            best = Some((pos, cone, derived_in_cone));
        }
    }
    let (conclusion_pos, cone, par_from_cone) =
        best.expect("derived_count > 0 implies at least one candidate line");

    if par_from_cone < spec.par_min || par_from_cone > spec.par_max {
        return Err(PlantError::OutOfBand);
    }

    // Step 5: rebuild a fresh proof containing only the cone, renumbered.
    let (theorem, mut proof) = rebuild_proof(&scratch, &cone, n_premises, conclusion_pos);

    // Step 6: sanity. A failure here is a construction bug, not a resample-worthy outcome.
    ProofVerifier::verify_proof(&mut proof);
    let all_valid = proof.lines.iter().all(|l| l.is_valid);
    let complete = proof.check_complete();
    if !all_valid || !complete {
        panic!(
            "plant: rebuilt proof failed verification for seed {seed} (spec={:?}); all_valid={all_valid} complete={complete}",
            spec
        );
    }

    let par = proof.lines.len() - theorem.premises.len();
    debug_assert_eq!(par, par_from_cone, "cone-derived par must match rebuilt proof par");

    Ok(PlantedCandidate { theorem, proof, par, seed })
}

/// Sample 2..=max_premises small, distinct premise formulas (literals,
/// negated literals, or a binary connective of two literals — depth <= 2).
fn sample_premises(rng: &mut StdRng, atoms: &[String], spec: &PlantSpec) -> Vec<Formula> {
    let n = rng.gen_range(2..=spec.max_premises);
    let mut premises: Vec<Formula> = Vec::with_capacity(n);
    while premises.len() < n {
        let candidate = sample_small_formula(rng, atoms);
        if !premises.contains(&candidate) {
            premises.push(candidate);
        }
    }
    premises
}

fn sample_literal(rng: &mut StdRng, atoms: &[String]) -> Formula {
    let atom = Formula::Atom(atoms[rng.gen_range(0..atoms.len())].clone());
    if rng.gen_bool(0.5) {
        Formula::Not(Box::new(atom))
    } else {
        atom
    }
}

fn sample_small_formula(rng: &mut StdRng, atoms: &[String]) -> Formula {
    if rng.gen_bool(0.5) {
        sample_literal(rng, atoms)
    } else {
        let left = sample_literal(rng, atoms);
        let right = sample_literal(rng, atoms);
        random_connective(rng, left, right)
    }
}

fn random_connective(rng: &mut StdRng, left: Formula, right: Formula) -> Formula {
    match rng.gen_range(0..4) {
        0 => Formula::And(Box::new(left), Box::new(right)),
        1 => Formula::Or(Box::new(left), Box::new(right)),
        2 => Formula::Implies(Box::new(left), Box::new(right)),
        _ => Formula::Biconditional(Box::new(left), Box::new(right)),
    }
}

fn is_duplicate(scratch: &[(Formula, Justification)], formula: &Formula) -> bool {
    scratch.iter().any(|(f, _)| f == formula)
}

fn within_len(formula: &Formula, spec: &PlantSpec) -> bool {
    formula.ascii_string_bracketed().chars().count() <= spec.max_formula_len
}

/// A line's attractiveness as a growth operand: recent and not-yet-consumed
/// lines score higher, so new steps tend to chain onto the growing frontier
/// instead of fanning out from the same few popular lines.
fn line_weight(pos: usize, total: usize, consumed: &[usize]) -> f64 {
    let recency = pos as f64 / total as f64;
    let freshness = 1.0 / (1.0 + consumed[pos - 1] as f64);
    0.1 + recency * freshness
}

fn weighted_pick_line(total: usize, consumed: &[usize], rng: &mut StdRng) -> usize {
    let weights: Vec<f64> = (1..=total).map(|pos| line_weight(pos, total, consumed)).collect();
    weighted_pick_index(&weights, rng) + 1
}

/// Pick an index into `weights` proportional to weight; returns the last
/// index on floating-point roundoff (never fails to return something).
fn weighted_pick_index(weights: &[f64], rng: &mut StdRng) -> usize {
    let total: f64 = weights.iter().sum();
    let mut roll = rng.gen::<f64>() * total;
    for (i, &w) in weights.iter().enumerate() {
        roll -= w;
        if roll <= 0.0 {
            return i;
        }
    }
    weights.len() - 1
}

fn weighted_pick_rule(rng: &mut StdRng) -> InferenceRule {
    use InferenceRule::*;
    let rules = InferenceRule::all();
    let weights: Vec<f64> = rules
        .iter()
        .map(|r| match r {
            Conjunction | Addition | Simplification | ModusPonens => 1.5,
            ModusTollens | DisjunctiveSyllogism | HypotheticalSyllogism => 1.0,
            ConstructiveDilemma | Contradiction => 0.4,
        })
        .collect();
    rules[weighted_pick_index(&weights, rng)]
}

/// All k-combinations of `{1, ..., n}`, ascending within each combo.
fn combinations(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    if k == 0 || k > n {
        return out;
    }
    let mut current = Vec::with_capacity(k);
    combinations_go(1, n, k, &mut current, &mut out);
    out
}

fn combinations_go(start: usize, n: usize, k: usize, current: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    if current.len() == k {
        out.push(current.clone());
        return;
    }
    for i in start..=n {
        current.push(i);
        combinations_go(i + 1, n, k, current, out);
        current.pop();
    }
}

struct Candidate {
    combo: Vec<usize>,
    conclusion: Formula,
}

fn combo_weight(combo: &[usize], total: usize, consumed: &[usize]) -> f64 {
    combo.iter().map(|&pos| line_weight(pos, total, consumed)).sum()
}

/// Try one inference-rule growth step: pick a weighted-random rule, enumerate
/// applicable operand tuples from the current scratch lines, and (weighted
/// toward recent, not-yet-consumed operands) commit one non-duplicate,
/// in-length-bound conclusion.
fn try_inference_step(
    scratch: &mut Vec<(Formula, Justification)>,
    consumed: &mut Vec<usize>,
    rng: &mut StdRng,
    spec: &PlantSpec,
    atoms: &[String],
) -> bool {
    let rule = weighted_pick_rule(rng);
    let k = rule.premise_count();
    let n = scratch.len();
    if k > n {
        return false;
    }

    let mut candidates: Vec<Candidate> = Vec::new();

    if rule == InferenceRule::Addition {
        for pos in 1..=n {
            let adjunct = sample_literal(rng, atoms);
            let operand = &scratch[pos - 1].0;
            for concl in rule.all_conclusions(&[operand], Some(&adjunct)) {
                if !is_duplicate(scratch, &concl) && within_len(&concl, spec) {
                    candidates.push(Candidate { combo: vec![pos], conclusion: concl });
                }
            }
        }
    } else {
        for combo in combinations(n, k) {
            let premises: Vec<&Formula> = combo.iter().map(|&p| &scratch[p - 1].0).collect();
            for concl in rule.all_conclusions(&premises, None) {
                if !is_duplicate(scratch, &concl) && within_len(&concl, spec) {
                    candidates.push(Candidate { combo: combo.clone(), conclusion: concl });
                }
            }
        }
    }

    if candidates.is_empty() {
        return false;
    }

    let weights: Vec<f64> = candidates.iter().map(|c| combo_weight(&c.combo, n, consumed)).collect();
    let chosen = weighted_pick_index(&weights, rng);
    let Candidate { combo, conclusion } = candidates.swap_remove(chosen);

    for &p in &combo {
        consumed[p - 1] += 1;
    }
    scratch.push((conclusion, Justification::Inference { rule, lines: combo }));
    consumed.push(0);
    true
}

/// Try one equivalence growth step: pick a weighted-random (recent,
/// not-yet-consumed) line, a random subformula on it, and a random
/// equivalence rule; commit the rewrite if it's non-duplicate and in-bound.
///
/// Uses `EquivalenceRule::replace_subformula` (replace *every* occurrence of
/// the chosen subformula value), matching exactly what
/// `ProofVerifier::verify_equivalence` checks. `Formula::replace_at_path`
/// replaces only the one occurrence at a specific position, which
/// `verify_equivalence` cannot always confirm: when the chosen subformula
/// also occurs elsewhere in the line, positional and structural replacement
/// disagree and the verifier rejects the line. Structural replacement is
/// always consistent with the verifier, so it's used here instead of the
/// path-based API.
fn try_equivalence_step(
    scratch: &mut Vec<(Formula, Justification)>,
    consumed: &mut Vec<usize>,
    rng: &mut StdRng,
    spec: &PlantSpec,
) -> bool {
    let n = scratch.len();
    let line_pos = weighted_pick_line(n, consumed, rng);
    let formula = scratch[line_pos - 1].0.clone();

    let subformulas = formula.subformulas();
    if subformulas.is_empty() {
        return false;
    }
    let sub = &subformulas[rng.gen_range(0..subformulas.len())];

    let rules = EquivalenceRule::all();
    let rule = rules[rng.gen_range(0..rules.len())];
    let forms = rule.equivalent_forms(sub);
    if forms.is_empty() {
        return false;
    }
    let chosen = &forms[rng.gen_range(0..forms.len())];
    let result = EquivalenceRule::replace_subformula(&formula, sub, chosen);

    if is_duplicate(scratch, &result) || !within_len(&result, spec) {
        return false;
    }

    consumed[line_pos - 1] += 1;
    scratch.push((result, Justification::Equivalence { rule, line: line_pos }));
    consumed.push(0);
    true
}

/// Transitive closure of cited lines starting at `target`, including `target`
/// itself. Returned sorted ascending (also a valid rebuild/topological order,
/// since every citation points strictly backward in scratch position).
fn compute_cone(scratch: &[(Formula, Justification)], target: usize) -> Vec<usize> {
    let mut seen = vec![false; scratch.len() + 1];
    let mut stack = vec![target];
    seen[target] = true;
    let mut cone = Vec::new();
    while let Some(idx) = stack.pop() {
        cone.push(idx);
        for r in scratch[idx - 1].1.referenced_lines() {
            if !seen[r] {
                seen[r] = true;
                stack.push(r);
            }
        }
    }
    cone.sort_unstable();
    cone
}

fn remap_justification(j: &Justification, remap: &[Option<usize>]) -> Justification {
    match j {
        Justification::Inference { rule, lines } => Justification::Inference {
            rule: *rule,
            lines: lines
                .iter()
                .map(|&l| remap[l].expect("cited line must already be in the cone's remap"))
                .collect(),
        },
        Justification::Equivalence { rule, line } => Justification::Equivalence {
            rule: *rule,
            line: remap[*line].expect("cited line must already be in the cone's remap"),
        },
        other => other.clone(),
    }
}

/// Rebuild a fresh `Proof` containing only the cone: `Theorem` premises are
/// the cone's premise leaves (a possibly-strict subset of the sampled
/// premises), and each cone step is re-added in original order with
/// citations remapped to the new line numbers.
fn rebuild_proof(
    scratch: &[(Formula, Justification)],
    cone: &[usize],
    n_premises: usize,
    conclusion_pos: usize,
) -> (Theorem, Proof) {
    let cone_premise_positions: Vec<usize> = cone.iter().copied().filter(|&i| i <= n_premises).collect();
    let cone_derived_positions: Vec<usize> = cone.iter().copied().filter(|&i| i > n_premises).collect();

    let theorem_premises: Vec<Formula> =
        cone_premise_positions.iter().map(|&i| scratch[i - 1].0.clone()).collect();
    let conclusion = scratch[conclusion_pos - 1].0.clone();

    let theorem = Theorem::new(theorem_premises, conclusion, Difficulty::Medium, None, None);

    let mut proof = Proof::new(theorem.clone());

    let mut remap: Vec<Option<usize>> = vec![None; scratch.len() + 1];
    for (new_idx, &old_pos) in cone_premise_positions.iter().enumerate() {
        remap[old_pos] = Some(new_idx + 1);
    }
    let mut next_new = cone_premise_positions.len() + 1;
    for &old_pos in &cone_derived_positions {
        remap[old_pos] = Some(next_new);
        next_new += 1;
    }

    for &old_pos in &cone_derived_positions {
        let (formula, justification) = &scratch[old_pos - 1];
        let remapped = remap_justification(justification, &remap);
        proof.add_line(formula.clone(), remapped);
    }

    (theorem, proof)
}
