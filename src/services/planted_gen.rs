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
use crate::models::rules::{EquivalenceRule, InferenceRule, ProofTechnique};
use crate::services::cheese::{cheese_check, is_satisfiable_dynamic};
use crate::services::obfuscate_gen::build_atom_pool;
use crate::services::prover::{greedy_prove, optimal_prove, OptimalConfig, OptimalOutcome};
use crate::services::truth_table::is_tautology_dynamic;
use crate::services::verifier::ProofVerifier;

/// Low weight given to equivalence steps vs. inference steps during growth.
const EQUIVALENCE_STEP_WEIGHT: f64 = 0.15;

/// Weight given to attempting a subproof-planting action (CP or IP) vs. a
/// normal inference/equivalence step, whenever the current scope depth still
/// has room under `spec.subproofs`. Applies uniformly at top level and when
/// growing inside an already-open scope (nesting).
const SUBPROOF_STEP_WEIGHT: f64 = 0.22;

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
    /// Premises = cone leaves, conclusion = cone root — or, when
    /// `obfuscation_passes > 0`, their costumed forms (see `apply_costume_pass`).
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

/// One scratch-space scope (subproof): a contiguous run of scratch positions
/// `[start, end]`, `end` being the last inner line's position (the discharge
/// line itself sits at `end + 1`, outside the scope). `end == None` while the
/// scope is still open.
#[derive(Debug, Clone, Copy)]
struct ScratchScope {
    start: usize,
    end: Option<usize>,
}

impl ScratchScope {
    fn contains(&self, pos: usize) -> bool {
        match self.end {
            Some(end) => pos >= self.start && pos <= end,
            None => pos >= self.start,
        }
    }
}

/// Local mirror of `ScopeManager`'s accessibility rule, tracked directly over
/// scratch positions during growth (before any real `Proof`/`ScopeManager`
/// exists). Unlike the engine's `ScopeManager`, this supports `truncate_to`,
/// so a failed subproof attempt can roll back cleanly — including forgetting
/// scopes that were opened *and* closed during the abandoned attempt.
///
/// The final rebuilt `Proof`'s own `ScopeManager` is what the verifier
/// actually checks against (built via `open_subproof`/`close_subproof`
/// replay in `rebuild_proof`); this struct only needs to be accurate enough
/// that growth never proposes a citation the replayed proof would reject.
#[derive(Debug, Clone, Default)]
struct ScratchScopes {
    scopes: Vec<ScratchScope>,
}

impl ScratchScopes {
    fn open(&mut self, start: usize) {
        self.scopes.push(ScratchScope { start, end: None });
    }

    /// Close the innermost open scope.
    fn close(&mut self, end: usize) {
        if let Some(scope) = self.scopes.iter_mut().rev().find(|s| s.end.is_none()) {
            scope.end = Some(end);
        }
    }

    /// Number of currently-open scopes.
    fn depth(&self) -> usize {
        self.scopes.iter().filter(|s| s.end.is_none()).count()
    }

    /// Number of scopes (open or closed) containing `pos` — matches
    /// `ScopeManager::depth_at_line`.
    fn depth_at(&self, pos: usize) -> usize {
        self.scopes.iter().filter(|s| s.contains(pos)).count()
    }

    /// Mirrors `ScopeManager::is_accessible`: can a new line about to be
    /// added at position `from` cite the line at `to`? `to` must be earlier,
    /// and every scope containing `to` must also contain `from` (i.e. `to`
    /// is not sealed inside a scope that closed before `from`).
    fn is_accessible(&self, from: usize, to: usize) -> bool {
        if to >= from {
            return false;
        }
        self.scopes.iter().all(|s| !s.contains(to) || s.contains(from))
    }

    /// Forget every scope (open or closed) opened at or after `pos` —
    /// used to roll back a failed subproof attempt to a prior checkpoint.
    fn truncate_to(&mut self, pos: usize) {
        self.scopes.retain(|s| s.start <= pos);
    }
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
    // Scope/depth tracking for scratch positions (Task 4). Stays empty and
    // inert when `spec.subproofs == 0`, in which case every helper below
    // that consults it degenerates to Task 3's original flat behavior.
    let mut scopes = ScratchScopes::default();

    // Step 3: grow the derivation until the band is plausibly reachable. A
    // single subproof action already contributes several lines at once (an
    // assumption, 2+ inner steps, and a discharge, all atomically kept or
    // dropped together at cone time), so with subproofs enabled the target
    // is trimmed to stay near `par_max` instead of doubling it — otherwise
    // growth keeps piling on top-level lines around an already-hefty
    // subproof until the largest cone routinely overshoots the band. The
    // `spec.subproofs == 0` path is untouched (byte-identical to Task 3).
    let derived_target = if spec.subproofs >= 1 {
        spec.par_max.saturating_add(3).max(8)
    } else {
        spec.par_max.saturating_mul(2).max(8)
    };
    let max_attempts = (derived_target * 20).max(120);
    let mut derived_count = 0usize;
    let mut attempts = 0usize;
    while derived_count < derived_target && attempts < max_attempts {
        attempts += 1;
        derived_count += grow_one_step(&mut scratch, &mut consumed, &mut scopes, &mut rng, spec, &atoms);
    }

    if derived_count == 0 {
        return Err(PlantError::Stuck);
    }

    // Step 4: pick the conclusion = derived line with the largest dependency
    // cone, restricted to positions that sit at depth 0 (a theorem's
    // conclusion can never be an assumption or an inner/nested subproof line
    // — only a plain top-level step or a first-level subproof's discharge).
    let mut best: Option<(usize, Vec<usize>, usize)> = None; // (line, cone, derived_in_cone)
    for pos in (n_premises + 1)..=scratch.len() {
        if scopes.depth_at(pos) != 0 {
            continue;
        }
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

    // Step 7: costume pass (Task 5). Layers a prologue (un-rewriting each
    // obfuscated premise) and epilogue (rewriting the conclusion forward) of
    // structural equivalence steps around the same body — see
    // `apply_costume_pass`. Inert at `obfuscation_passes == 0`: `theorem`
    // and `proof` pass through untouched, byte-identical to Tasks 3-4.
    let (theorem, proof) = if spec.obfuscation_passes > 0 {
        let (costumed_theorem, mut costumed_proof) = apply_costume_pass(&theorem, &proof, spec, &mut rng);
        ProofVerifier::verify_proof(&mut costumed_proof);
        let all_valid = costumed_proof.lines.iter().all(|l| l.is_valid);
        let complete = costumed_proof.check_complete();
        if !all_valid || !complete {
            panic!(
                "plant: costumed proof failed verification for seed {seed} (spec={:?}); all_valid={all_valid} complete={complete}",
                spec
            );
        }
        (costumed_theorem, costumed_proof)
    } else {
        (theorem, proof)
    };

    let par = proof.lines.len() - theorem.premises.len();
    if spec.obfuscation_passes == 0 {
        debug_assert_eq!(par, par_from_cone, "cone-derived par must match rebuilt proof par");
    }

    Ok(PlantedCandidate { theorem, proof, par, seed })
}

/// Sample 2..=max_premises small, distinct premise formulas (literals,
/// negated literals, or a binary connective of two literals — depth <= 2).
///
/// Yield optimization (Ruling F / Critical 1): a candidate is also rejected
/// when adding it would make the premise set-so-far jointly unsatisfiable
/// (e.g. `P` alongside `~P`, or `Q v Q` alongside `~Q`) — a truth-table
/// check on the raw, pre-costume premises. This doesn't change what the
/// gate ultimately guarantees (`golf_gate`'s semantic stage still checks
/// the final, possibly-costumed theorem — costume preserves equivalence,
/// so satisfiability of the raw premises is preserved too), it just stops
/// growth from wasting a whole seed on a premise set that gate would reject
/// anyway.
fn sample_premises(rng: &mut StdRng, atoms: &[String], spec: &PlantSpec) -> Vec<Formula> {
    let n = rng.gen_range(2..=spec.max_premises);
    let mut premises: Vec<Formula> = Vec::with_capacity(n);
    while premises.len() < n {
        let candidate = sample_small_formula(rng, atoms);
        if premises.contains(&candidate) {
            continue;
        }
        premises.push(candidate);
        if !is_satisfiable_dynamic(&premises) {
            premises.pop();
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

/// Whether `formula` is byte-equal (`Formula` equality, `==`) to the formula
/// at some position in `pool`. Originally named for its one use (rejecting
/// a subproof whose DISCHARGE merely reproduces a formula already
/// accessible before the scope opened — Ruling A, Task 8b; unconditional
/// for both CP and IP as of Ruling E, Task 8c, see `grow_ip_subproof`'s doc
/// comment); as of Ruling F (Task 13, Important 3 mechanism (iv)) also used
/// to reject a subproof's freshly-sampled ASSUMPTION on the same grounds —
/// an assumption that merely reproduces an already-accessible formula is
/// just as much a free re-citation shave as a discharge that does.
fn formula_duplicates_pool(scratch: &[(Formula, Justification)], pool: &[usize], formula: &Formula) -> bool {
    pool.iter().any(|&p| scratch[p - 1].0 == *formula)
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

/// Weighted-pick one position out of an explicit candidate set (as opposed
/// to the full `1..=total` range), so callers can restrict the pool to
/// scope-accessible positions. `total` remains the full scratch length, so
/// recency weighting (`line_weight`) still scores against the true frontier.
fn weighted_pick_line(positions: &[usize], total: usize, consumed: &[usize], rng: &mut StdRng) -> usize {
    let weights: Vec<f64> = positions.iter().map(|&pos| line_weight(pos, total, consumed)).collect();
    positions[weighted_pick_index(&weights, rng)]
}

/// Scratch positions `1..=n` that a new line at position `n + 1` may cite,
/// per the same scope-accessibility rule the verifier enforces. With no open
/// or closed scopes (`spec.subproofs == 0`), every position `1..=n` is
/// accessible — an exact, behavior-preserving generalization of Task 3's
/// original unrestricted `1..=n`.
fn accessible_positions(scopes: &ScratchScopes, n: usize) -> Vec<usize> {
    (1..=n).filter(|&p| scopes.is_accessible(n + 1, p)).collect()
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
///
/// Operands are drawn only from scope-accessible positions (`eligible`), so
/// this same function works unchanged for top-level growth, growth inside an
/// open subproof, and growth after a sibling subproof has already closed.
fn try_inference_step(
    scratch: &mut Vec<(Formula, Justification)>,
    consumed: &mut Vec<usize>,
    scopes: &ScratchScopes,
    rng: &mut StdRng,
    spec: &PlantSpec,
    atoms: &[String],
) -> bool {
    let rule = weighted_pick_rule(rng);
    let k = rule.premise_count();
    let n = scratch.len();
    let eligible = accessible_positions(scopes, n);
    if k > eligible.len() {
        return false;
    }

    let mut candidates: Vec<Candidate> = Vec::new();

    if rule == InferenceRule::Addition {
        for &pos in &eligible {
            let adjunct = sample_literal(rng, atoms);
            let operand = &scratch[pos - 1].0;
            for concl in rule.all_conclusions(&[operand], Some(&adjunct)) {
                if !is_duplicate(scratch, &concl) && within_len(&concl, spec) {
                    candidates.push(Candidate { combo: vec![pos], conclusion: concl });
                }
            }
        }
    } else {
        for combo_idx in combinations(eligible.len(), k) {
            let combo: Vec<usize> = combo_idx.iter().map(|&i| eligible[i - 1]).collect();
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
    scopes: &ScratchScopes,
    rng: &mut StdRng,
    spec: &PlantSpec,
) -> bool {
    let n = scratch.len();
    let eligible = accessible_positions(scopes, n);
    if eligible.is_empty() {
        return false;
    }
    let line_pos = weighted_pick_line(&eligible, n, consumed, rng);
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

/// One structural equivalence rewrite recorded while obfuscating a single
/// theorem-slot formula (a premise or the conclusion): replace-all `before`
/// -> `after` via `rule`. Kept private — nothing outside this file needs to
/// see individual steps, only the obfuscated formula `obfuscate_with_trace`
/// returns and the prologue/epilogue proof lines built from the trace.
///
/// Stores the rewritten subformula pair rather than a path into the parent
/// formula (Task 5's binding ruling): `ProofVerifier::verify_equivalence`
/// only accepts structural replace-all rewrites (`check_subformula_equivalence`
/// picks a subformula and replaces *every* occurrence — see verifier.rs), so
/// a step's meaning is fully captured by the (before, after) pair it
/// replaces everywhere, not by a single positional site.
#[derive(Debug, Clone)]
struct RewriteStep {
    rule: EquivalenceRule,
    before: Formula,
    after: Formula,
}

/// Enumerate every admissible one-step structural rewrite of `current`: for
/// each subformula and each rule, each of the rule's equivalent forms of
/// that subformula is a candidate, paired with the whole-formula result of
/// replacing every occurrence (`EquivalenceRule::replace_subformula` — the
/// same replace-all semantics the verifier checks).
///
/// A candidate is admissible only when all of:
/// - it's a genuine change (`form != sub`; a same-formula "rewrite" would be
///   a no-op step that wastes a par line for nothing),
/// - the result fits `spec.max_formula_len`,
/// - the result doesn't collide with `avoid` (another theorem slot's
///   formula — obfuscating a premise into equaling another premise or the
///   conclusion is degenerate),
/// - the rule accepts the reverse direction too (`sub` is itself one of
///   `rule.equivalent_forms(&form)`) — true of every rule variant on every
///   formula sampled in manual testing, but checked directly rather than
///   assumed, since it's a fact about hand-written per-rule code, and
/// - it round-trips: replacing `after` back to `before` (replace-all) on the
///   result reproduces `current` exactly.
///
/// Both of the last two conditions are needed, and neither implies the
/// other: the reverse-rule check is about whether `rule.equivalent_forms`
/// *recognizes* `before` as a valid image of `after`; the round-trip check
/// is a separate, purely structural fact about `replace_subformula`, and
/// catches the case where `after` already occurred somewhere in `current`
/// outside the rewrite site — replacing every occurrence of `after` back to
/// `before` would then also overwrite that unrelated occurrence, landing on
/// some other formula instead of exactly `current`. Together they guarantee
/// `ProofVerifier::verify_equivalence`'s `check_subformula_equivalence`
/// (which brute-forces over `source.subformulas()` and
/// `rule.equivalent_forms`) finds this exact (after, before) pair as a
/// witness — which is what makes the prologue (un-rewriting a premise back
/// to its original form) and epilogue (rewriting the conclusion forward)
/// verify.
fn admissible_rewrite_steps(
    current: &Formula,
    spec: &PlantSpec,
    avoid: &[Formula],
) -> Vec<(RewriteStep, Formula)> {
    let mut out = Vec::new();
    let rules = EquivalenceRule::all();
    for sub in current.subformulas() {
        for &rule in &rules {
            for form in rule.equivalent_forms(&sub) {
                if form == sub {
                    continue;
                }
                let next = EquivalenceRule::replace_subformula(current, &sub, &form);
                if !within_len(&next, spec) || avoid.contains(&next) {
                    continue;
                }
                if !rule.equivalent_forms(&form).contains(&sub) {
                    continue;
                }
                let back = EquivalenceRule::replace_subformula(&next, &form, &sub);
                if back != *current {
                    continue;
                }
                out.push((RewriteStep { rule, before: sub.clone(), after: form }, next));
            }
        }
    }
    out
}

/// Costume a single formula with `1..=passes` chained structural rewrites,
/// each admissible per `admissible_rewrite_steps` (uniformly chosen among
/// that step's candidates) and applied to the *result* of the previous one.
/// A sampled pass that finds no admissible candidate for the formula's
/// current stage contributes nothing and is silently skipped — so the
/// returned trace can be shorter than the sampled pass count, empty in the
/// limit (never an error: an un-costumed formula is a valid, if
/// unobfuscated, outcome — see the "empty trace" case in `apply_costume_pass`).
///
/// Requires `passes >= 1` (guaranteed by `apply_costume_pass`'s caller,
/// which only invokes this path when `spec.obfuscation_passes > 0`).
///
/// Returns the whole-formula stage this call passed through, in order,
/// starting with `f` itself and ending with the returned formula (so the
/// caller can fold every stage — not just the final one — into a later
/// slot's `avoid` list; see `apply_costume_pass`'s mechanism-(i) fix).
///
/// No costume undo (Important 3, mechanism (ii)): each pass's `avoid` list
/// is the caller-supplied `avoid` plus every whole-formula stage this same
/// call has already produced (starting with `f`), so a later pass can
/// never rewrite back to the original formula or to any stage already
/// passed through — `admissible_rewrite_steps` already rejects any
/// candidate landing in `avoid`, this just grows that list across passes
/// instead of holding it fixed.
fn obfuscate_with_trace(
    f: &Formula,
    passes: u8,
    rng: &mut StdRng,
    spec: &PlantSpec,
    avoid: &[Formula],
) -> (Formula, Vec<RewriteStep>, Vec<Formula>) {
    let n_passes = rng.gen_range(1..=passes);
    let mut current = f.clone();
    let mut trace = Vec::new();
    let mut own_stages: Vec<Formula> = vec![f.clone()];
    for _ in 0..n_passes {
        let mut local_avoid = avoid.to_vec();
        local_avoid.extend(own_stages.iter().cloned());
        let candidates = admissible_rewrite_steps(&current, spec, &local_avoid);
        if candidates.is_empty() {
            continue;
        }
        let chosen = rng.gen_range(0..candidates.len());
        let (step, next) = candidates.into_iter().nth(chosen).expect("chosen index is in bounds");
        own_stages.push(next.clone());
        trace.push(step);
        current = next;
    }
    (current, trace, own_stages)
}

/// One growth attempt at the current scope depth: with room to open a new
/// subproof under `spec.subproofs` (`ScratchScopes::depth() < spec.subproofs`
/// covers every case — top level opening the first scope, and nesting a
/// second one inside it, since `subproofs` is exactly the max allowed
/// depth), maybe plant one (CP or IP); otherwise a normal weighted
/// inference/equivalence step. Returns the number of scratch lines added.
///
/// Shared by the top-level growth loop in `plant` and by subproof inner
/// growth (`grow_cp_subproof`/`grow_ip_subproof`), so growth after a
/// subproof closes and growth inside one follow exactly the same rules —
/// scope-accessibility is the only thing that tells them apart, via
/// `ScratchScopes` threaded through to `try_inference_step`/`try_equivalence_step`.
///
/// For `spec.subproofs == 0`, `scopes.depth() < 0` is never true (usize), so
/// the subproof branch's random roll is never even evaluated (short-circuit)
/// — this degenerates to Task 3's exact original dispatch and rng-call
/// sequence: one `rng.gen::<f64>()` per attempt, compared against
/// `EQUIVALENCE_STEP_WEIGHT` exactly as before.
fn grow_one_step(
    scratch: &mut Vec<(Formula, Justification)>,
    consumed: &mut Vec<usize>,
    scopes: &mut ScratchScopes,
    rng: &mut StdRng,
    spec: &PlantSpec,
    atoms: &[String],
) -> usize {
    if scopes.depth() < spec.subproofs as usize && rng.gen::<f64>() < SUBPROOF_STEP_WEIGHT {
        try_subproof_step(scratch, consumed, scopes, rng, spec, atoms)
    } else if rng.gen::<f64>() < EQUIVALENCE_STEP_WEIGHT {
        usize::from(try_equivalence_step(scratch, consumed, scopes, rng, spec))
    } else {
        usize::from(try_inference_step(scratch, consumed, scopes, rng, spec, atoms))
    }
}

/// Attempt to plant one subproof (CP or IP, chosen with equal probability)
/// at the current scope depth. Returns the number of scratch lines added (0
/// on failure, in which case `scratch`/`consumed`/`scopes` are restored to
/// exactly their pre-call state — see `grow_cp_subproof`/`grow_ip_subproof`).
fn try_subproof_step(
    scratch: &mut Vec<(Formula, Justification)>,
    consumed: &mut Vec<usize>,
    scopes: &mut ScratchScopes,
    rng: &mut StdRng,
    spec: &PlantSpec,
    atoms: &[String],
) -> usize {
    let before = scratch.len();
    let ok = if rng.gen_bool(0.5) {
        grow_cp_subproof(scratch, consumed, scopes, rng, spec, atoms)
    } else {
        grow_ip_subproof(scratch, consumed, scopes, rng, spec, atoms)
    };
    if ok {
        scratch.len() - before
    } else {
        0
    }
}

/// Snapshot of `scratch`/`consumed`, for rolling back a failed subproof
/// attempt. Restoring `consumed` in full (not just truncating) matters:
/// partially-successful inner growth may have incremented the consumed-count
/// of *pre-existing* (outer) lines it cited as operands, and a plain
/// truncate would leave that bias in place even though the lines that
/// caused it are gone.
struct GrowthCheckpoint {
    scratch_len: usize,
    consumed: Vec<usize>,
}

fn checkpoint(scratch: &[(Formula, Justification)], consumed: &[usize]) -> GrowthCheckpoint {
    GrowthCheckpoint { scratch_len: scratch.len(), consumed: consumed.to_vec() }
}

fn restore(
    cp: GrowthCheckpoint,
    scratch: &mut Vec<(Formula, Justification)>,
    consumed: &mut Vec<usize>,
    scopes: &mut ScratchScopes,
) {
    scratch.truncate(cp.scratch_len);
    *consumed = cp.consumed;
    scopes.truncate_to(cp.scratch_len);
}

/// Plant a Conditional Proof subproof: assume `A`, grow 2–5 inner steps
/// (which may cite outer lines and `A`, and — when nesting room remains — a
/// subproof of their own), then discharge `A > X` where `X` is the last
/// inner line's formula. Rejects up front (no mutation yet, so a plain
/// `false` return suffices) if the assumption itself duplicates a formula
/// already accessible before the scope opens (Ruling F, Task 13, Important
/// 3 mechanism (iv) — an assumption that merely re-derives an existing
/// accessible formula is a free re-citation shave, exactly like a discharge
/// that does, see `formula_duplicates_pool`) or is too long. Aborts
/// (rolling back to exactly the pre-call state) if fewer than 2 inner steps
/// can be grown within budget, or if the discharge formula duplicates a
/// formula already accessible before the scope opened (Ruling A, Task 8b)
/// or is too long.
fn grow_cp_subproof(
    scratch: &mut Vec<(Formula, Justification)>,
    consumed: &mut Vec<usize>,
    scopes: &mut ScratchScopes,
    rng: &mut StdRng,
    spec: &PlantSpec,
    atoms: &[String],
) -> bool {
    let assumption = sample_small_formula(rng, atoms);
    if !within_len(&assumption, spec) {
        return false;
    }

    let outer_pool = accessible_positions(scopes, scratch.len());
    if formula_duplicates_pool(scratch, &outer_pool, &assumption) {
        return false;
    }

    let cp = checkpoint(scratch, consumed);
    let assumption_pos = scratch.len() + 1;
    scopes.open(assumption_pos);
    scratch.push((assumption.clone(), Justification::Assumption { technique: ProofTechnique::ConditionalProof }));
    consumed.push(0);

    let n_inner = rng.gen_range(2..=5);
    let mut grown_inner = 0usize;
    let budget = (n_inner * 15).max(40);
    let mut inner_attempts = 0usize;
    while grown_inner < n_inner && inner_attempts < budget {
        inner_attempts += 1;
        if grow_one_step(scratch, consumed, scopes, rng, spec, atoms) > 0 {
            grown_inner += 1;
        }
    }

    if grown_inner < 2 {
        restore(cp, scratch, consumed, scopes);
        return false;
    }

    let last_inner_pos = scratch.len();
    let last_inner_formula = scratch[last_inner_pos - 1].0.clone();
    let conclusion = Formula::Implies(Box::new(assumption), Box::new(last_inner_formula));

    if formula_duplicates_pool(scratch, &outer_pool, &conclusion) || !within_len(&conclusion, spec) {
        restore(cp, scratch, consumed, scopes);
        return false;
    }

    scopes.close(last_inner_pos);
    consumed[assumption_pos - 1] += 1;
    consumed[last_inner_pos - 1] += 1;
    scratch.push((
        conclusion,
        Justification::SubproofConclusion {
            technique: ProofTechnique::ConditionalProof,
            subproof_start: assumption_pos,
            subproof_end: last_inner_pos,
        },
    ));
    consumed.push(0);
    true
}

/// `ConjNegElim` template (Ruling E, Task 8c): `G = ~(B . ~A)`, for pool
/// anchor formula `A` and freshly sampled literal `B`. Returns `(peel_rule,
/// assumption, step_a, step_b, discharge)` — `assumption = ~G`, `step_a` is
/// what `peel_rule` (DoubleNegation) rewrites `assumption` to (`B . ~A`),
/// and `step_b` is what Simplification extracts from `step_a` (`~A`, the
/// right conjunct) — the formula `grow_ip_subproof` then contradicts
/// against the anchor's own `A` via NegE.
fn conj_neg_elim_template(a: &Formula, b: Formula) -> (EquivalenceRule, Formula, Formula, Formula, Formula) {
    let not_a = Formula::Not(Box::new(a.clone()));
    let step_a = Formula::And(Box::new(b), Box::new(not_a.clone())); // B . ~A
    let discharge = Formula::Not(Box::new(step_a.clone())); // ~(B . ~A)
    let assumption = Formula::Not(Box::new(discharge.clone())); // ~~(B . ~A)
    (EquivalenceRule::DoubleNegation, assumption, step_a, not_a, discharge)
}

/// `DisjNegElim` template (Ruling E, Task 8c): `G = A ∨ B`, for pool anchor
/// formula `A` and freshly sampled literal `B`. Returns the same
/// `(peel_rule, assumption, step_a, step_b, discharge)` shape as
/// `conj_neg_elim_template`, but peels via De Morgan instead of Double
/// Negation: `assumption = ~(A∨B)` --DeMorgan--> `~A . ~B` (`step_a`)
/// --Simp--> `~A` (`step_b`, the left conjunct this time).
fn disj_neg_elim_template(a: &Formula, b: Formula) -> (EquivalenceRule, Formula, Formula, Formula, Formula) {
    let not_a = Formula::Not(Box::new(a.clone()));
    let not_b = Formula::Not(Box::new(b.clone()));
    let discharge = Formula::Or(Box::new(a.clone()), Box::new(b)); // A ∨ B
    let assumption = Formula::Not(Box::new(discharge.clone())); // ~(A ∨ B)
    let step_a = Formula::And(Box::new(not_a.clone()), Box::new(not_b)); // ~A . ~B
    (EquivalenceRule::DeMorgan, assumption, step_a, not_a, discharge)
}

/// Plant an Indirect Proof subproof from a small refutation template
/// (Ruling E, Task 8c). Seeds on an existing accessible outer line `Y`
/// (formula `A`) and a freshly sampled literal `B`, then samples one of two
/// template shapes (`conj_neg_elim_template`/`disj_neg_elim_template`, equal
/// probability) giving a *fresh* discharge `G` together with the exact
/// assumption `~G` and the 2 real inner steps (an equivalence peel, then
/// Simplification) that derive `~A` from it — closed by a NegE citing `[Y,
/// that ~A line]`. Unlike the pre-Task-8c version, `G` is a novel compound
/// formula, never byte-equal to `Y` or anything else: shaving the scope now
/// requires finding an alternative derivation of `G`, not just re-citing an
/// outer line.
///
/// Both template formulas (`assumption`, `step_a`, `step_b`, and `G` itself)
/// are computed up front, before any scratch/scope mutation — `G` doesn't
/// depend on grown content the way CP's discharge does, so an over-length
/// formula or a `G` that collides with the outer pool (frozen as `eligible`,
/// computed before the scope opens — Task 8b's "open-time-frozen pool") can
/// be rejected by simply not committing anything, no checkpoint/rollback
/// needed for those checks (contrast `grow_cp_subproof`, whose discharge is
/// only known after inner growth completes).
///
/// A checkpoint IS taken before the scope opens, though (Important 3,
/// mechanism (iii)): the fixed derivation's contradiction line is always
/// `Formula::Contradiction` — one canonical value, so ANY two accessible
/// occurrences of it are automatically byte-equal — and unlike every other
/// push in this function, that one previously committed with no duplicate
/// check at all. Optional filler growth (below) runs inside this same
/// still-open scope and can itself derive `Formula::Contradiction` first
/// (via ordinary `try_inference_step`, which already checks `is_duplicate`
/// before committing); when that happens, the fixed derivation's own
/// contradiction push would create a second, mutually accessible occurrence
/// — a free re-citation shave — so it's rejected and the whole attempt
/// rolled back instead.
fn grow_ip_subproof(
    scratch: &mut Vec<(Formula, Justification)>,
    consumed: &mut Vec<usize>,
    scopes: &mut ScratchScopes,
    rng: &mut StdRng,
    spec: &PlantSpec,
    atoms: &[String],
) -> bool {
    let n = scratch.len();
    let eligible = accessible_positions(scopes, n);
    if eligible.is_empty() {
        return false;
    }
    let seed_pos = weighted_pick_line(&eligible, n, consumed, rng);
    let seed_formula = scratch[seed_pos - 1].0.clone();
    let b = sample_literal(rng, atoms);

    let (peel_rule, assumption, step_a, step_b, discharge) = if rng.gen_bool(0.5) {
        conj_neg_elim_template(&seed_formula, b)
    } else {
        disj_neg_elim_template(&seed_formula, b)
    };

    if !within_len(&assumption, spec)
        || !within_len(&step_a, spec)
        || !within_len(&step_b, spec)
        || !within_len(&discharge, spec)
        || formula_duplicates_pool(scratch, &eligible, &assumption)
        || formula_duplicates_pool(scratch, &eligible, &discharge)
    {
        return false;
    }

    let cp = checkpoint(scratch, consumed);
    let assumption_pos = scratch.len() + 1;
    scopes.open(assumption_pos);
    scratch.push((assumption, Justification::Assumption { technique: ProofTechnique::IndirectProof }));
    consumed.push(0);

    // Optional filler growth before the fixed derivation (0..=3 steps);
    // purely cosmetic variety, like the old code's — v0.3.1 scope-internal
    // pruning (`compute_cone`) drops anything the contradiction doesn't
    // transitively need, so filler can never leave a dead line in a kept
    // scope, and can itself nest a subproof when `spec.subproofs` allows.
    let n_extra = rng.gen_range(0..=3);
    let mut grown = 0usize;
    let budget = (n_extra * 15).max(20);
    let mut attempts = 0usize;
    while grown < n_extra && attempts < budget {
        attempts += 1;
        if grow_one_step(scratch, consumed, scopes, rng, spec, atoms) > 0 {
            grown += 1;
        }
    }

    consumed[assumption_pos - 1] += 1;
    scratch.push((step_a, Justification::Equivalence { rule: peel_rule, line: assumption_pos }));
    consumed.push(0);
    let step_a_pos = scratch.len();

    consumed[step_a_pos - 1] += 1;
    scratch.push((
        step_b,
        Justification::Inference { rule: InferenceRule::Simplification, lines: vec![step_a_pos] },
    ));
    consumed.push(0);
    let step_b_pos = scratch.len();

    // Same duplicate-line check ordinary growth steps already apply
    // (Important 3, mechanism (iii)) — see this function's doc comment.
    if is_duplicate(scratch, &Formula::Contradiction) {
        restore(cp, scratch, consumed, scopes);
        return false;
    }

    consumed[seed_pos - 1] += 1;
    consumed[step_b_pos - 1] += 1;
    scratch.push((
        Formula::Contradiction,
        Justification::Inference { rule: InferenceRule::Contradiction, lines: vec![seed_pos, step_b_pos] },
    ));
    consumed.push(0);
    let contradiction_pos = scratch.len();

    scopes.close(contradiction_pos);

    consumed[assumption_pos - 1] += 1;
    consumed[contradiction_pos - 1] += 1;
    scratch.push((
        discharge,
        Justification::SubproofConclusion {
            technique: ProofTechnique::IndirectProof,
            subproof_start: assumption_pos,
            subproof_end: contradiction_pos,
        },
    ));
    consumed.push(0);

    true
}

/// Transitive closure of cited lines starting at `target`, including `target`
/// itself. Returned sorted ascending (also a valid rebuild/topological order,
/// since every citation points strictly backward in scratch position).
///
/// Scope-pruned, not scope-atomic (Ruling A, Task 8b): reaching a
/// `SubproofConclusion` (discharge) line no longer pulls in the entire closed
/// scope. `Justification::referenced_lines()` already names exactly
/// `[subproof_start, subproof_end]` for a discharge — the assumption
/// (`subproof_start`) unconditionally, and the scope's anchor
/// (`subproof_end`: IP's contradiction line, or CP's discharged consequent —
/// the line the discharge's validity actually hinges on) — so the ordinary
/// walk below, with no extra handling, pulls in the assumption plus exactly
/// what the anchor transitively requires: a within-scope citation recurses
/// through this same walk (including into any nested scope's own discharge,
/// pruned by the same rule), while a citation pointing outside the scope
/// becomes an ordinary cone edge, exactly as it always did. Anything inside
/// the scope the anchor's chain never reaches (filler growth in
/// `grow_ip_subproof`, or an inner CP step nothing downstream cites) is
/// simply never pushed, so it never enters the cone.
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
/// premises), and each cone step is replayed in original (scope) order with
/// citations remapped to the new line numbers.
///
/// Replay, not line-copying: `Assumption` lines go through
/// `open_subproof` and `SubproofConclusion` lines go through
/// `close_subproof`, so the rebuilt `Proof`'s own `ScopeManager` is built up
/// exactly as a human writing the proof top-to-bottom would build it — depth,
/// scope ids, and (via `close_subproof`'s internal bookkeeping) the discharge
/// line's own `subproof_start`/`subproof_end` are all derived fresh from
/// *this* replay, not copied from scratch-space numbering. Everything else
/// (`Inference`/`Equivalence`) still goes through `add_line` with citations
/// remapped via `remap_justification`, exactly as in Task 3.
///
/// This only produces well-formed scope nesting because a scope's assumption
/// and discharge are always both in `cone_derived_positions` or both absent
/// (see `compute_cone`: a discharge's `referenced_lines()` always names both
/// `subproof_start` and `subproof_end`, so pulling in the discharge always
/// pulls in the assumption too, and nothing outside the scope can ever reach
/// the assumption any other way), so every `open_subproof` replayed here has
/// a matching `close_subproof` later in the same loop, in the same relative
/// order.
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
        match justification {
            Justification::Assumption { technique } => {
                proof.open_subproof(formula.clone(), *technique);
            }
            Justification::SubproofConclusion { technique, .. } => {
                proof.close_subproof(formula.clone(), *technique);
            }
            _ => {
                let remapped = remap_justification(justification, &remap);
                proof.add_line(formula.clone(), remapped);
            }
        }
    }

    (theorem, proof)
}

/// Layer a costume pass on top of an already valid & complete `(theorem,
/// proof)` pair (Task 5): obfuscate each premise and the conclusion
/// independently, then rebuild the proof a second time with the obfuscated
/// premises/conclusion as the new theorem, replaying the original body
/// between a prologue (un-rewriting each obfuscated premise back to the
/// form the body actually cites) and an epilogue (rewriting the body's
/// conclusion forward to the obfuscated conclusion).
///
/// Only called when `spec.obfuscation_passes > 0`; `proof` must already be
/// natively valid and complete (the caller verifies this before calling).
fn apply_costume_pass(theorem: &Theorem, proof: &Proof, spec: &PlantSpec, rng: &mut StdRng) -> (Theorem, Proof) {
    let n_premises = theorem.premises.len();

    // Every derived (post-premise) line of the ORIGINAL, un-costumed proof —
    // these persist unchanged into the costumed proof's body, so no
    // premise/conclusion costume rewrite may ever land on one of them
    // (Important 3, mechanism (i)): previously `avoid` only ever compared
    // against other theorem slots, never the body, so a prologue/epilogue
    // stage could silently collide with a body line.
    let body_lines: Vec<Formula> = proof.lines[n_premises..].iter().map(|l| l.formula.clone()).collect();

    // Costume premises left to right. Each one's avoid-list is: every
    // not-yet-processed premise's original form, the conclusion's original
    // form, EVERY stage (not just the final one) that every already-
    // processed premise's own costume passed through — a later premise's
    // rewrite landing on an earlier premise's intermediate stage is just as
    // much a collision as landing on its final form — and every body line.
    let mut final_premises: Vec<Formula> = Vec::with_capacity(n_premises);
    let mut premise_traces: Vec<Vec<RewriteStep>> = Vec::with_capacity(n_premises);
    let mut produced_stages: Vec<Formula> = Vec::new();
    for i in 0..n_premises {
        let avoid: Vec<Formula> = (i + 1..n_premises)
            .map(|j| theorem.premises[j].clone())
            .chain(std::iter::once(theorem.conclusion.clone()))
            .chain(produced_stages.iter().cloned())
            .chain(body_lines.iter().cloned())
            .collect();
        let (p_prime, trace, own_stages) =
            obfuscate_with_trace(&theorem.premises[i], spec.obfuscation_passes, rng, spec, &avoid);
        produced_stages.extend(own_stages);
        final_premises.push(p_prime);
        premise_traces.push(trace);
    }

    // Conclusion: avoid every premise's full trace (every stage, not just
    // final) plus every body line.
    let avoid_conclusion: Vec<Formula> =
        produced_stages.iter().cloned().chain(body_lines.iter().cloned()).collect();
    let (conclusion_prime, trace_c, _) =
        obfuscate_with_trace(&theorem.conclusion, spec.obfuscation_passes, rng, spec, &avoid_conclusion);

    let new_theorem = Theorem::new(
        final_premises.clone(),
        conclusion_prime.clone(),
        theorem.difficulty,
        theorem.theme.clone(),
        theorem.name.clone(),
    );
    let mut new_proof = Proof::new(new_theorem.clone());

    // Prologue: un-rewrite each obfuscated premise back to the form the
    // body cites, one Equivalence line per trace step, applied in reverse
    // (the last costume step undone first) and each citing the line the
    // previous un-rewrite step just produced (the first cites the premise
    // line itself). An empty trace (every sampled pass skipped) contributes
    // no lines — the body's citations then point straight at the premise.
    let mut premise_final_lines: Vec<usize> = Vec::with_capacity(n_premises);
    for i in 0..n_premises {
        let mut cur_formula = final_premises[i].clone();
        let mut cur_line = i + 1;
        for step in premise_traces[i].iter().rev() {
            cur_formula = EquivalenceRule::replace_subformula(&cur_formula, &step.after, &step.before);
            new_proof.add_line(cur_formula.clone(), Justification::Equivalence { rule: step.rule, line: cur_line });
            cur_line = new_proof.lines.len();
        }
        debug_assert_eq!(
            cur_formula, theorem.premises[i],
            "prologue must un-rewrite premise {i} back to the exact formula the body was derived from"
        );
        premise_final_lines.push(cur_line);
    }

    // Body: replay the original proof's derived lines (everything after its
    // premises) exactly as `rebuild_proof` does above — Assumption/
    // SubproofConclusion lines go through open_subproof/close_subproof
    // (which derive scope bookkeeping fresh from this replay, so nested
    // subproofs' own citations never need remapping), everything else
    // through add_line with citations remapped from old line numbers
    // (premises shift to wherever their prologue landed; later derived
    // lines shift by the prologue's total length).
    let mut remap: Vec<Option<usize>> = vec![None; proof.lines.len() + 1];
    for i in 1..=n_premises {
        remap[i] = Some(premise_final_lines[i - 1]);
    }
    let body_start_new = new_proof.lines.len() + 1;
    for (offset, old_pos) in ((n_premises + 1)..=proof.lines.len()).enumerate() {
        remap[old_pos] = Some(body_start_new + offset);
    }

    for old_pos in (n_premises + 1)..=proof.lines.len() {
        let line = &proof.lines[old_pos - 1];
        match &line.justification {
            Justification::Assumption { technique } => {
                new_proof.open_subproof(line.formula.clone(), *technique);
            }
            Justification::SubproofConclusion { technique, .. } => {
                new_proof.close_subproof(line.formula.clone(), *technique);
            }
            other => {
                let remapped = remap_justification(other, &remap);
                new_proof.add_line(line.formula.clone(), remapped);
            }
        }
    }

    // Epilogue: rewrite the body's conclusion forward to the obfuscated
    // conclusion, one Equivalence line per trace step, each citing the
    // previous epilogue line (the first cites the body's own conclusion
    // line — always the original proof's last line, replayed above).
    let body_conclusion_new_line =
        remap[proof.lines.len()].expect("the body's last (conclusion) line must be in the remap");
    let mut cur_formula = theorem.conclusion.clone();
    let mut cur_line = body_conclusion_new_line;
    for step in &trace_c {
        cur_formula = EquivalenceRule::replace_subformula(&cur_formula, &step.before, &step.after);
        new_proof.add_line(cur_formula.clone(), Justification::Equivalence { rule: step.rule, line: cur_line });
        cur_line = new_proof.lines.len();
    }
    debug_assert_eq!(
        cur_formula, conclusion_prime,
        "epilogue must rewrite the conclusion forward to the exact obfuscated conclusion"
    );

    (new_theorem, new_proof)
}

// ─── Golf gate pipeline (Task 6) ────────────────────────────────────────────
//
// Reject-filter deciding which planted candidates are benchmark-worthy:
// cheap syntactic checks first, expensive prover calls last, first failure
// wins. Consumes the cheese/greedy/lawyer services already in this crate.
// Notarization (replaying the proof through the validator) is deliberately
// NOT here — it's propbench's job, since the replay format lives there.

/// Configuration for the golf-worthiness gate pipeline (`golf_gate`).
#[derive(Debug, Clone)]
pub struct GateConfig {
    /// `ascii_string_bracketed` char cap for every premise and the
    /// conclusion (default 90, matching `PlantSpec::max_formula_len`).
    pub max_formula_len: usize,
    /// Max equivalence-rewrite BFS depth for the disguised-identity cheese
    /// check (default 3, matching `ServeConfig::default`).
    pub cheese_max_distance: usize,
    /// Line budget for the greedy ("philosopher") gate (default 40).
    pub greedy_max_lines: usize,
    /// Every candidate must survive a lawyer search at this budget (default
    /// `OptimalConfig::default()`).
    pub probe: OptimalConfig,
    /// Optional stricter lawyer budget for finalists only. `None` (the
    /// default) skips this stage entirely — probe-only gating. The ruled
    /// freeze budget is `max_lines: c.par, max_nodes: 1_000_000,
    /// equiv_moves_per_state: 128` (Ruling B); the canonical config lives in
    /// propbench (`golf.rs`'s freeze-branch construction), not here — this
    /// stage just runs whatever `GateConfig` it's handed.
    pub freeze: Option<OptimalConfig>,
}

impl Default for GateConfig {
    fn default() -> Self {
        GateConfig {
            max_formula_len: 90,
            cheese_max_distance: 3,
            greedy_max_lines: 40,
            probe: OptimalConfig::default(),
            freeze: None,
        }
    }
}

/// Why `golf_gate` rejected a candidate, cheapest check first — the
/// pipeline stops at the first failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GateReject {
    /// A premise or the conclusion exceeds `cfg.max_formula_len`.
    TooBig,
    /// No assignment satisfies every premise (Ruling F / Critical 1): the
    /// premise set is jointly unsatisfiable, so any conclusion follows by a
    /// short indirect proof — vacuous truth, not a real theorem.
    InconsistentPremises,
    /// No assignment falsifies the conclusion (Ruling F / Critical 1): it's
    /// a tautology, provable premise-free.
    TautologousConclusion,
    /// Vetoed by `cheese_check` (tautologous disjunct, subformula decoy, or
    /// disguised identity); the string names which one and its detail.
    Cheese(String),
    /// The greedy philosopher found a proof unaided — too easy.
    GreedyProvable { lines: usize },
    /// The bounded-optimal lawyer cracked it at probe (default) budgets.
    LawyerProbeCracked { lines: usize },
    /// The bounded-optimal lawyer cracked it at freeze (finalist) budgets.
    LawyerFreezeCracked { lines: usize },
    /// A HARD backstop (Ruling F / Important 3), independent of whatever
    /// the growth-time fixes elsewhere in this file did or didn't catch: a
    /// derived line's formula byte-equals an earlier line accessible at
    /// that position (same scope or any enclosing open scope; premises
    /// count as accessible — exactly `Proof::is_line_accessible`'s rule,
    /// the same one the verifier enforces) — a free re-citation shave.
    DuplicateLine { line: usize, duplicates: usize },
}

/// Reject-filter deciding whether `c` is benchmark-worthy: size → cheese →
/// greedy → lawyer probe → optional lawyer freeze, cheapest first, first
/// failure wins. `Ok(())` means `c` survived every configured stage.
pub fn golf_gate(c: &PlantedCandidate, cfg: &GateConfig) -> Result<(), GateReject> {
    // 1. Size: pure string length, cheapest possible check.
    let too_big = c
        .theorem
        .premises
        .iter()
        .chain(std::iter::once(&c.theorem.conclusion))
        .any(|f| f.ascii_string_bracketed().chars().count() > cfg.max_formula_len);
    if too_big {
        return Err(GateReject::TooBig);
    }

    // 2. Semantic (Ruling F / Critical 1): one truth-table sweep each,
    // atoms <= 6 so <= 64 rows — cheaper than cheese. Premises checked
    // first (binding order). Strict-subset-entailment (some proper subset
    // of the premises already entails the conclusion) is deliberately NOT
    // checked here — controller ruling: an unused premise shortens no
    // proof; it's measured, not gated, in the harness that calls this.
    if !is_satisfiable_dynamic(&c.theorem.premises) {
        return Err(GateReject::InconsistentPremises);
    }
    if is_tautology_dynamic(&c.theorem.conclusion) {
        return Err(GateReject::TautologousConclusion);
    }

    // 3. Cheese: cheap syntactic/truth-table checks. Field precedence
    // mirrors `serve_filter::analyze_for_serving`'s ordering of the same
    // three `CheeseReport` fields.
    let cheese = cheese_check(&c.theorem.premises, &c.theorem.conclusion, cfg.cheese_max_distance);
    if let Some(disjunct) = &cheese.tautologous_disjunct {
        return Err(GateReject::Cheese(format!(
            "tautologous disjunct: {}",
            disjunct.ascii_string_bracketed()
        )));
    }
    if let Some(decoy) = &cheese.subformula_decoy {
        return Err(GateReject::Cheese(format!("subformula decoy: {}", decoy.ascii_string_bracketed())));
    }
    if let Some(distance) = cheese.identity_rewrite_distance {
        return Err(GateReject::Cheese(format!("disguised identity at distance {distance}")));
    }

    // 4. Greedy: the philosopher must fail to prove it unaided.
    let greedy = greedy_prove(&c.theorem.premises, &c.theorem.conclusion, cfg.greedy_max_lines);
    if let Some(proof) = greedy.proof {
        return Err(GateReject::GreedyProvable { lines: proof.line_count });
    }

    // 5. Lawyer probe: default-budget bounded-optimal search must not crack
    // it. `Proved` in ANY form (certified minimal or not) is a reject;
    // `NotProvedWithinBounds`/`Exhausted` both pass.
    if let OptimalOutcome::Proved { proof, .. } =
        optimal_prove(&c.theorem.premises, &c.theorem.conclusion, &cfg.probe)
    {
        return Err(GateReject::LawyerProbeCracked { lines: proof.line_count });
    }

    // 6. Lawyer freeze: finalists only, caller-configured budget.
    if let Some(freeze_cfg) = &cfg.freeze {
        if let OptimalOutcome::Proved { proof, .. } =
            optimal_prove(&c.theorem.premises, &c.theorem.conclusion, freeze_cfg)
        {
            return Err(GateReject::LawyerFreezeCracked { lines: proof.line_count });
        }
    }

    // 7. Duplicate line (Ruling F / Important 3): a HARD backstop over the
    // truly finished (post-costume) candidate, on the witness proof itself
    // rather than the theorem — placed last since it's cheap enough that
    // ordering doesn't matter for cost, and it's the definitive check on
    // this specific defect regardless of what the growth-time fixes did.
    // Premises count as accessible (they carry no scope, so
    // `is_line_accessible` trivially clears them); a duplicate is checked
    // against every STRICTLY EARLIER line, so the first occurrence of a
    // formula never rejects itself.
    for line in &c.proof.lines {
        if matches!(line.justification, Justification::Premise) {
            continue;
        }
        if let Some(earlier) = c.proof.lines.iter().find(|other| {
            other.line_number < line.line_number
                && other.formula == line.formula
                && c.proof.is_line_accessible(line.line_number, other.line_number)
        }) {
            return Err(GateReject::DuplicateLine { line: line.line_number, duplicates: earlier.line_number });
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Unit test (Ruling F / Critical 1, Part 3): `sample_premises`'s yield
    /// optimization must never hand back a jointly-unsatisfiable set —
    /// checked directly against the private function, over enough seeds and
    /// atom-pool sizes to exercise the rejection path repeatedly (not just
    /// happen to never trigger it).
    #[test]
    fn sample_premises_never_unsatisfiable() {
        let mut checked = 0usize;
        for atom_count in 3..=6u8 {
            let atoms = build_atom_pool(atom_count);
            let spec = PlantSpec {
                atoms: atom_count,
                par_min: 6,
                par_max: 12,
                max_premises: 5,
                max_formula_len: 90,
                subproofs: 0,
                obfuscation_passes: 0,
            };
            for seed in 0..500u64 {
                let mut rng = StdRng::seed_from_u64(seed);
                let premises = sample_premises(&mut rng, &atoms, &spec);
                checked += 1;
                assert!(
                    is_satisfiable_dynamic(&premises),
                    "atoms={atom_count} seed {seed}: sample_premises produced an unsatisfiable set: {premises:?}"
                );
            }
        }
        assert!(checked > 0, "no seeds were checked");
    }
}
