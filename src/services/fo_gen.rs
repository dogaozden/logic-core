//! Forward proof generator for monadic first-order exercises, after `planted_gen`: sample
//! premises (one-place predicates over one variable or one name), grow a derivation forward
//! with ∀E, ∀I, ∃I, ∃E, MP, MT, HS, Simp, Conj and CP, pick a top-level line as the
//! conclusion, and keep exactly that line's dependency cone as the witness proof.
//!
//! Every theorem returned here comes with its own proof, replayed into a real `Proof` and
//! accepted by `ProofVerifier`. Difficulty is the proof's length plus its quantifier steps,
//! an ∃E subproof counting twice.

use std::collections::BTreeSet;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::models::rules::first_order::instance_of;
use crate::models::rules::{InferenceRule, ProofTechnique};
use crate::models::{Difficulty, Formula, Justification, Proof, Term, Theorem};
use crate::services::verifier::ProofVerifier;

const NAMES: [&str; 5] = ["a", "b", "c", "d", "e"];
const PREDICATES: [&str; 5] = ["F", "G", "H", "J", "K"];
const VAR: &str = "x";
const ID_PREFIX: &str = "fo-gen-";
/// Seeds tried per `generate_first_order` call before giving up.
const SEED_ATTEMPTS: u64 = 400;
/// Cap on the atomic formulas in any derived formula.
const MAX_ATOMS: usize = 4;

/// Shape of one generation run.
#[derive(Debug, Clone)]
pub struct FoSpec {
    /// One-place predicates in use (taken from F, G, H, J).
    pub predicates: usize,
    pub min_premises: usize,
    pub max_premises: usize,
    /// Top-level derived lines to grow before picking a conclusion.
    pub steps: usize,
    /// Deepest subproof nesting (0: no ∃E or CP).
    pub max_depth: usize,
    pub exists_weight: f64,
    pub cp_weight: f64,
    /// May two derived quantified sentences be conjoined (∃x F(x) . ∀x G(x))?
    pub sentence_conjunction: bool,
    /// Inclusive range of lines grown inside each subproof.
    pub inner: (usize, usize),
    /// Chance of a second existential premise (a second ∃E).
    pub second_exists: f64,
    /// Inclusive score band the conclusion's proof must fall in.
    pub band: (usize, usize),
}

impl FoSpec {
    pub fn for_difficulty(difficulty: Difficulty) -> FoSpec {
        match difficulty {
            Difficulty::Easy => FoSpec { predicates: 3, min_premises: 2, max_premises: 2, steps: 4, max_depth: 0, exists_weight: 0.0, cp_weight: 0.0, sentence_conjunction: false, inner: (2, 3), second_exists: 0.0, band: (3, 6) },
            Difficulty::Medium => FoSpec { predicates: 3, min_premises: 2, max_premises: 3, steps: 6, max_depth: 1, exists_weight: 1.2, cp_weight: 0.3, sentence_conjunction: false, inner: (2, 4), second_exists: 0.0, band: (7, 10) },
            Difficulty::Hard => FoSpec { predicates: 4, min_premises: 3, max_premises: 4, steps: 8, max_depth: 1, exists_weight: 1.5, cp_weight: 0.5, sentence_conjunction: false, inner: (4, 8), second_exists: 0.35, band: (11, 15) },
            Difficulty::Expert => FoSpec { predicates: 5, min_premises: 3, max_premises: 5, steps: 11, max_depth: 2, exists_weight: 1.5, cp_weight: 0.5, sentence_conjunction: true, inner: (3, 8), second_exists: 0.5, band: (16, 32) },
        }
    }
}

/// The difficulty measure: derived lines + quantifier steps (∃E counts 2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoScore {
    pub lines: usize,
    pub quantifier_steps: usize,
}

impl FoScore {
    pub fn total(&self) -> usize {
        self.lines + self.quantifier_steps
    }

    pub fn difficulty(&self) -> Option<Difficulty> {
        [Difficulty::Easy, Difficulty::Medium, Difficulty::Hard, Difficulty::Expert]
            .into_iter()
            .find(|d| {
                let (lo, hi) = FoSpec::for_difficulty(*d).band;
                (lo..=hi).contains(&self.total())
            })
    }
}

/// A generated theorem with the proof it was grown from.
#[derive(Debug, Clone)]
pub struct FoCandidate {
    pub theorem: Theorem,
    pub proof: Proof,
    pub score: FoScore,
    pub seed: u64,
}

impl FoCandidate {
    /// A hint naming the rules of the generator's own proof, without its formulas.
    pub fn hint(&self) -> String {
        let mut counts: Vec<(String, usize)> = Vec::new();
        for line in &self.proof.lines {
            let name = match &line.justification {
                Justification::Inference { rule, .. } => rule.abbreviation().to_string(),
                Justification::ExistentialElimination { .. } => "∃E (with a new name)".to_string(),
                Justification::SubproofConclusion { technique, .. } => technique.abbreviation().to_string(),
                _ => continue,
            };
            match counts.iter_mut().find(|(n, _)| *n == name) {
                Some((_, c)) => *c += 1,
                None => counts.push((name, 1)),
            }
        }
        let rules: Vec<String> = counts
            .into_iter()
            .map(|(n, c)| if c > 1 { format!("{n} ×{c}") } else { n })
            .collect();
        format!(
            "There is a {}-line proof using {}.",
            self.proof.lines.len() - self.theorem.premises.len(),
            rules.join(", ")
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FoGenError {
    /// Growth produced no usable conclusion in the requested band.
    NoConclusion,
    /// The chosen premises have no model (an exercise from inconsistent premises).
    Unsatisfiable,
    /// No seed in the attempt window gave a theorem.
    Exhausted { first_seed: u64, attempts: u64 },
    /// Construction defect: the replayed proof did not verify.
    InvalidProof { seed: u64, line: usize, message: String },
    /// An id not made by `generate_first_order`.
    UnknownId(String),
}

/// Generate a theorem of the given difficulty, trying seeds `seed, seed+1, …`.
pub fn generate_first_order(difficulty: Difficulty, seed: u64) -> Result<FoCandidate, FoGenError> {
    let spec = FoSpec::for_difficulty(difficulty);
    for s in seed..seed.saturating_add(SEED_ATTEMPTS) {
        match plant_first_order(&spec, s) {
            Ok(mut c) => {
                c.theorem.id = format!("{ID_PREFIX}{}-{s}", difficulty_key(difficulty));
                c.proof.theorem.id = c.theorem.id.clone();
                c.theorem.difficulty = difficulty;
                c.proof.theorem.difficulty = difficulty;
                return Ok(c);
            }
            Err(FoGenError::NoConclusion) | Err(FoGenError::Unsatisfiable) => continue,
            Err(e) => return Err(e),
        }
    }
    Err(FoGenError::Exhausted { first_seed: seed, attempts: SEED_ATTEMPTS })
}

/// Rebuild the generated theorem (and its proof) from the id `generate_first_order` gave it.
pub fn regenerate_first_order(id: &str) -> Result<FoCandidate, FoGenError> {
    let unknown = || FoGenError::UnknownId(id.to_string());
    let rest = id.strip_prefix(ID_PREFIX).ok_or_else(unknown)?;
    let (key, seed) = rest.split_once('-').ok_or_else(unknown)?;
    let difficulty = [Difficulty::Easy, Difficulty::Medium, Difficulty::Hard, Difficulty::Expert]
        .into_iter()
        .find(|d| difficulty_key(*d) == key)
        .ok_or_else(unknown)?;
    let seed: u64 = seed.parse().map_err(|_| unknown())?;
    let c = generate_first_order(difficulty, seed)?;
    if c.theorem.id == id {
        Ok(c)
    } else {
        Err(unknown())
    }
}

pub fn is_generated_first_order_id(id: &str) -> bool {
    id.starts_with(ID_PREFIX)
}

fn difficulty_key(d: Difficulty) -> &'static str {
    match d {
        Difficulty::Easy => "easy",
        Difficulty::Medium => "medium",
        Difficulty::Hard => "hard",
        Difficulty::Expert => "expert",
    }
}

/// One seed: grow, choose a conclusion in `spec.band`, rebuild and verify its cone.
pub fn plant_first_order(spec: &FoSpec, seed: u64) -> Result<FoCandidate, FoGenError> {
    let mut rng = StdRng::seed_from_u64(seed);
    let premises = sample_premises(&mut rng, spec);
    let mut s = Scratch::new(premises);
    let mut attempts = 0;
    while s.derived_at_top() < spec.steps && attempts < spec.steps * 6 {
        attempts += 1;
        s.step(&mut rng, spec, None);
    }

    let mut best: Option<(usize, usize, Vec<usize>)> = None; // (score, pos, cone)
    for pos in (s.n_premises + 1)..=s.lines.len() {
        if s.depth_at(pos) != 0 {
            continue;
        }
        let cone = s.cone(pos);
        let score = s.score(&cone);
        let total = score.total();
        if total < spec.band.0 || total > spec.band.1 || score.lines < 2 {
            continue;
        }
        if !s.acceptable_conclusion(pos, &cone) {
            continue;
        }
        if best.as_ref().map_or(true, |(b, _, _)| total >= *b) {
            best = Some((total, pos, cone));
        }
    }
    let (_, pos, cone) = best.ok_or(FoGenError::NoConclusion)?;
    let premises: Vec<Formula> = cone.iter().filter(|&&i| i <= s.n_premises).map(|&i| s.lines[i - 1].0.clone()).collect();
    if !monadic_satisfiable(&premises) {
        return Err(FoGenError::Unsatisfiable);
    }
    let score = s.score(&cone);
    let (theorem, proof) = s.rebuild(&cone, pos, score, seed)?;
    Ok(FoCandidate { theorem, proof, score, seed })
}

// ───────────────────────────── premises ─────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Lit {
    pred: usize,
    neg: bool,
}

impl Lit {
    fn at(&self, name: &str) -> Formula {
        let p = Formula::Predicate(PREDICATES[self.pred].to_string(), vec![Term::Name(name.to_string())]);
        if self.neg {
            Formula::Not(Box::new(p))
        } else {
            p
        }
    }
}

fn and(l: Formula, r: Formula) -> Formula {
    Formula::And(Box::new(l), Box::new(r))
}

fn implies(l: Formula, r: Formula) -> Formula {
    Formula::Implies(Box::new(l), Box::new(r))
}

fn random_lit(rng: &mut StdRng, spec: &FoSpec, avoid: &[usize]) -> Option<Lit> {
    let free: Vec<usize> = (0..spec.predicates).filter(|p| !avoid.contains(p)).collect();
    if free.is_empty() {
        return None;
    }
    Some(Lit { pred: free[rng.gen_range(0..free.len())], neg: rng.gen_bool(0.18) })
}

/// Premises with a common thread: an entry fact (ground, existential, universal or none)
/// and universal conditionals whose antecedents reuse literals already reachable.
fn sample_premises(rng: &mut StdRng, spec: &FoSpec) -> Vec<Formula> {
    let n = rng.gen_range(spec.min_premises..=spec.max_premises);
    let mut out: Vec<Formula> = Vec::new();
    let mut reachable: Vec<Lit> = Vec::new();
    let first = Lit { pred: rng.gen_range(0..spec.predicates), neg: false };
    reachable.push(first);
    let x = VAR;

    let entry = rng.gen_range(0..10);
    if spec.max_depth > 0 && entry < 4 {
        if rng.gen_bool(0.4) {
            if let Some(m) = random_lit(rng, spec, &[first.pred]) {
                out.push(Formula::Exists(x.into(), Box::new(and(first.at(x), m.at(x)))));
                reachable.push(m);
            }
        }
        if out.is_empty() {
            out.push(Formula::Exists(x.into(), Box::new(first.at(x))));
        }
    } else if entry < 7 {
        out.push(first.at("a"));
    } else if entry < 8 {
        out.push(Formula::ForAll(x.into(), Box::new(first.at(x))));
    }
    // A second existential entry on the hardest spec: two ∃E subproofs.
    if spec.second_exists > 0.0 && rng.gen_bool(spec.second_exists) {
        if let Some(m) = random_lit(rng, spec, &reachable.iter().map(|l| l.pred).collect::<Vec<_>>()) {
            out.push(Formula::Exists(x.into(), Box::new(m.at(x))));
            reachable.push(m);
        }
    }
    // A second, ground entry fact on harder specs.
    if spec.max_premises >= 4 && rng.gen_bool(0.25) {
        if let Some(m) = random_lit(rng, spec, &[first.pred]) {
            out.push(m.at(if out.iter().any(|f| f.has_free_name("a")) { "b" } else { "a" }));
            reachable.push(m);
        }
    }

    let mut guard = 0;
    while out.len() < n && guard < 40 {
        guard += 1;
        // Extend the chain from its newest literal more often than from older ones.
        let a = if rng.gen_bool(0.6) { reachable[reachable.len() - 1] } else { reachable[rng.gen_range(0..reachable.len())] };
        let reached: Vec<usize> = reachable.iter().map(|l| l.pred).collect();
        let mut consequent = |rng: &mut StdRng, avoid: &[usize]| {
            let mut fresh_avoid: Vec<usize> = avoid.to_vec();
            fresh_avoid.extend(reached.iter().copied());
            if rng.gen_bool(0.75) {
                if let Some(l) = random_lit(rng, spec, &fresh_avoid) {
                    return Some(l);
                }
            }
            random_lit(rng, spec, avoid)
        };
        let body = match rng.gen_range(0..6) {
            0 if reachable.iter().any(|l| l.pred != a.pred) => {
                let others: Vec<Lit> = reachable.iter().copied().filter(|l| l.pred != a.pred).collect();
                let c = others[rng.gen_range(0..others.len())];
                let Some(b) = consequent(rng, &[a.pred, c.pred]) else { continue };
                reachable.push(b);
                implies(and(a.at(x), c.at(x)), b.at(x))
            }
            1 => {
                let Some(b) = consequent(rng, &[a.pred]) else { continue };
                let Some(c) = random_lit(rng, spec, &[a.pred, b.pred]) else { continue };
                reachable.push(b);
                reachable.push(c);
                implies(a.at(x), and(b.at(x), c.at(x)))
            }
            _ => {
                let Some(b) = consequent(rng, &[a.pred]) else { continue };
                reachable.push(b);
                implies(a.at(x), b.at(x))
            }
        };
        let f = Formula::ForAll(x.into(), Box::new(body));
        if !out.contains(&f) {
            out.push(f);
        }
    }
    out
}

// ───────────────────────────── growth ─────────────────────────────

#[derive(Debug, Clone, Copy)]
struct Scope {
    start: usize,
    end: Option<usize>,
}

impl Scope {
    fn contains(&self, pos: usize) -> bool {
        pos >= self.start && self.end.map_or(true, |e| pos <= e)
    }
}

/// The derivation being grown; positions are 1-based like proof line numbers.
struct Scratch {
    lines: Vec<(Formula, Justification)>,
    scopes: Vec<Scope>,
    n_premises: usize,
    premise_names: BTreeSet<String>,
    /// Free names of each line (index = position - 1), kept beside `lines`.
    names: Vec<BTreeSet<String>>,
}

enum Move {
    Line(Formula, Justification),
    OpenExists { ex: usize },
    OpenCp { assumption: Formula, name: String },
}

/// Does the name occur in the formula? (Generated formulas never bind a name from `NAMES`.)
fn mentions(f: &Formula, name: &str) -> bool {
    match f {
        Formula::Predicate(_, args) => args.iter().any(|t| matches!(t, Term::Name(n) if n == name)),
        Formula::Not(i) | Formula::ForAll(_, i) | Formula::Exists(_, i) => mentions(i, name),
        Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) | Formula::Biconditional(l, r) => mentions(l, name) || mentions(r, name),
        _ => false,
    }
}

fn has_quantifier(f: &Formula) -> bool {
    match f {
        Formula::ForAll(_, _) | Formula::Exists(_, _) => true,
        Formula::Not(i) => has_quantifier(i),
        Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) | Formula::Biconditional(l, r) => {
            has_quantifier(l) || has_quantifier(r)
        }
        _ => false,
    }
}

fn atom_count(f: &Formula) -> usize {
    match f {
        Formula::Not(i) | Formula::ForAll(_, i) | Formula::Exists(_, i) => atom_count(i),
        Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) | Formula::Biconditional(l, r) => atom_count(l) + atom_count(r),
        _ => 1,
    }
}

fn is_literal(f: &Formula) -> bool {
    match f {
        Formula::Predicate(_, _) => true,
        Formula::Not(i) => matches!(i.as_ref(), Formula::Predicate(_, _)),
        _ => false,
    }
}

fn predicate_of(f: &Formula) -> Option<&str> {
    match f {
        Formula::Predicate(p, _) => Some(p),
        Formula::Not(i) => predicate_of(i),
        _ => None,
    }
}

fn abstract_name(f: &Formula, name: &str) -> Formula {
    f.replace_term_everywhere(&Term::Name(name.to_string()), &Term::Name(VAR.to_string()))
}

fn inference(rule: InferenceRule, lines: Vec<usize>) -> Justification {
    Justification::Inference { rule, lines }
}

impl Scratch {
    fn new(premises: Vec<Formula>) -> Scratch {
        let n_premises = premises.len();
        let premise_names = premises.iter().flat_map(|p| p.free_names()).collect();
        let names = premises.iter().map(|p| p.free_names()).collect();
        Scratch { lines: premises.into_iter().map(|f| (f, Justification::Premise)).collect(), scopes: Vec::new(), n_premises, premise_names, names }
    }

    fn push(&mut self, f: Formula, j: Justification) {
        self.names.push(f.free_names());
        self.lines.push((f, j));
    }

    /// The one name a quantifier-free line is about.
    fn single_name_at(&self, pos: usize) -> Option<&String> {
        let names = &self.names[pos - 1];
        if names.len() == 1 && !has_quantifier(&self.lines[pos - 1].0) {
            names.iter().next()
        } else {
            None
        }
    }

    fn depth_at(&self, pos: usize) -> usize {
        self.scopes.iter().filter(|s| s.contains(pos)).count()
    }

    fn open_depth(&self) -> usize {
        self.scopes.iter().filter(|s| s.end.is_none()).count()
    }

    fn derived_at_top(&self) -> usize {
        ((self.n_premises + 1)..=self.lines.len()).filter(|&p| self.depth_at(p) == 0).count()
    }

    fn accessible(&self, from: usize, to: usize) -> bool {
        to < from && self.scopes.iter().all(|s| !s.contains(to) || s.contains(from))
    }

    fn accessible_from(&self, from: usize) -> Vec<usize> {
        (1..from).filter(|&p| self.accessible(from, p)).collect()
    }

    fn known(&self, from: usize, f: &Formula) -> bool {
        self.accessible_from(from).iter().any(|&p| self.lines[p - 1].0.alpha_eq(f))
    }

    fn names_used(&self) -> BTreeSet<&String> {
        self.names.iter().flatten().collect()
    }

    fn fresh_name(&self) -> Option<String> {
        let used = self.names_used();
        NAMES.iter().find(|n| !used.iter().any(|u| u.as_str() == **n)).map(|n| n.to_string())
    }

    /// Can `name` be generalized at `from` (no premise or open assumption mentions it)?
    fn arbitrary(&self, from: usize, name: &str) -> bool {
        let in_premise = self.premise_names.contains(name);
        let in_assumption = self
            .scopes
            .iter()
            .filter(|s| s.contains(from))
            .any(|s| self.names[s.start - 1].contains(name));
        !in_premise && !in_assumption
    }

    /// Simp on a line made by Conj only undoes it.
    fn is_conjunction_step(&self, pos: usize) -> bool {
        matches!(self.lines[pos - 1].1, Justification::Inference { rule: InferenceRule::Conjunction, .. })
    }

    fn citation_counts(&self) -> Vec<usize> {
        let mut counts = vec![0; self.lines.len() + 1];
        for (_, j) in &self.lines {
            for p in j.referenced_lines() {
                counts[p] += 1;
            }
        }
        counts
    }

    fn moves(&self, spec: &FoSpec, focus: Option<&str>) -> Vec<(Move, f64)> {
        let from = self.lines.len() + 1;
        let acc = self.accessible_from(from);
        let fresh = self.fresh_name();
        let in_play: BTreeSet<String> = acc.iter().flat_map(|&p| self.names[p - 1].iter().cloned()).collect();
        let cited = self.citation_counts();
        let mut out: Vec<(Move, f64)> = Vec::new();
        let f = |p: usize| &self.lines[p - 1].0;

        struct Info {
            name: Option<String>,
            literal: bool,
            sentence: bool,
            cp_assumption: bool,
        }
        let info: Vec<Option<Info>> = (0..from)
            .map(|p| {
                (p > 0 && acc.contains(&p)).then(|| {
                    let g = f(p);
                    Info {
                        name: self.single_name_at(p).cloned(),
                        literal: is_literal(g),
                        sentence: p > self.n_premises && has_quantifier(g) && self.names[p - 1].is_empty() && !matches!(g, Formula::And(_, _)),
                        cp_assumption: matches!(self.lines[p - 1].1, Justification::Assumption { technique: ProofTechnique::ConditionalProof }),
                    }
                })
            })
            .collect();
        let inf = |p: usize| info[p].as_ref().expect("accessible line");

        for &i in &acc {
            match f(i) {
                Formula::ForAll(v, body) if i <= self.n_premises => {
                    // Inside a subproof, instantiate for its own name; elsewhere for any name in play.
                    let mut names: Vec<(String, f64)> = in_play
                        .iter()
                        .map(|n| (n.clone(), if focus.map_or(true, |w| w == n) { 1.0 } else { 0.08 }))
                        .collect();
                    if let Some(n) = &fresh {
                        names.push((n.clone(), if in_play.is_empty() { 1.0 } else { 0.5 }));
                    }
                    for (n, w) in names {
                        if let Ok(inst) = body.substitute_free(v, &Term::Name(n)) {
                            out.push((Move::Line(inst, inference(InferenceRule::UniversalElimination, vec![i])), w));
                        }
                    }
                }
                Formula::Exists(_, _) if i <= self.n_premises && self.open_depth() < spec.max_depth && cited[i] == 0 && fresh.is_some() => {
                    out.push((Move::OpenExists { ex: i }, spec.exists_weight));
                }
                Formula::And(l, r) if !self.is_conjunction_step(i) => {
                    out.push((Move::Line((**l).clone(), inference(InferenceRule::Simplification, vec![i])), 1.5));
                    out.push((Move::Line((**r).clone(), inference(InferenceRule::Simplification, vec![i])), 1.5));
                }
                Formula::Implies(a, b) => {
                    for &j in &acc {
                        let g = f(j);
                        if g == a.as_ref() {
                            out.push((Move::Line((**b).clone(), inference(InferenceRule::ModusPonens, vec![i, j])), 3.0));
                        }
                        if let Formula::Not(nb) = g {
                            if nb.as_ref() == b.as_ref() {
                                out.push((Move::Line(Formula::Not(a.clone()), inference(InferenceRule::ModusTollens, vec![i, j])), 2.0));
                            }
                        }
                        if let Formula::Implies(b2, c) = g {
                            if b2.as_ref() == b.as_ref() && c != a && inf(i).name.is_some() {
                                out.push((Move::Line(implies((**a).clone(), (**c).clone()), inference(InferenceRule::HypotheticalSyllogism, vec![i, j])), 1.5));
                            }
                        }
                    }
                }
                _ => {}
            }
            let g = f(i);
            if let Some(n) = &inf(i).name {
                if !matches!(g, Formula::Implies(_, _)) {
                    out.push((Move::Line(Formula::Exists(VAR.into(), Box::new(abstract_name(g, n))), inference(InferenceRule::ExistentialIntroduction, vec![i])), 1.0));
                }
                if self.arbitrary(from, n) {
                    out.push((Move::Line(Formula::ForAll(VAR.into(), Box::new(abstract_name(g, n))), inference(InferenceRule::UniversalIntroduction, vec![i])), 2.0));
                }
                if inf(i).literal && !inf(i).cp_assumption {
                    for &j in &acc {
                        let h = inf(j);
                        if h.literal && !h.cp_assumption && h.name.as_ref() == Some(n) && predicate_of(g) != predicate_of(f(j)) {
                            out.push((Move::Line(and(g.clone(), f(j).clone()), inference(InferenceRule::Conjunction, vec![i, j])), 0.5));
                        }
                    }
                }
            }
            // Two quantified sentences side by side: ∃x F(x) . ∃x G(x).
            if spec.sentence_conjunction && inf(i).sentence {
                for &j in &acc {
                    if j != i && inf(j).sentence {
                        out.push((Move::Line(and(g.clone(), f(j).clone()), inference(InferenceRule::Conjunction, vec![i, j])), 0.4));
                    }
                }
            }
        }
        if self.open_depth() < spec.max_depth && spec.cp_weight > 0.0 {
            if let Some(n) = &fresh {
                for &i in &acc {
                    if let Formula::ForAll(v, body) = f(i) {
                        if let Formula::Implies(a, _) = body.as_ref() {
                            if let Ok(assumption) = a.substitute_free(v, &Term::Name(n.clone())) {
                                out.push((Move::OpenCp { assumption, name: n.clone() }, spec.cp_weight));
                            }
                        }
                    }
                }
            }
        }

        out.retain(|(m, _)| match m {
            Move::Line(g, _) => {
                atom_count(g) <= MAX_ATOMS && !acc.iter().any(|&p| self.lines[p - 1].0 == *g)
            }
            _ => true,
        });
        // Prefer recent, little-used lines, as planted_gen does.
        for (m, w) in out.iter_mut() {
            if let Move::Line(_, j) = m {
                let refs = j.referenced_lines();
                let newest = refs.iter().copied().max().unwrap_or(0) as f64;
                let used: usize = refs.iter().map(|&p| cited[p]).sum();
                *w *= (1.0 + newest / from as f64) / (1.0 + used as f64);
            }
        }
        out
    }

    /// Add one line (or one whole subproof). Returns whether anything was added.
    fn step(&mut self, rng: &mut StdRng, spec: &FoSpec, focus: Option<&str>) -> bool {
        let mut moves = self.moves(spec, focus);
        if let Some(n) = focus {
            for (m, w) in moves.iter_mut() {
                if let Move::Line(g, _) = m {
                    if mentions(g, n) {
                        *w *= 4.0;
                    }
                }
            }
        }
        if moves.is_empty() {
            return false;
        }
        let total: f64 = moves.iter().map(|(_, w)| *w).sum();
        let mut pick = rng.gen_range(0.0..total);
        let mut chosen = moves.len() - 1;
        for (k, (_, w)) in moves.iter().enumerate() {
            if pick < *w {
                chosen = k;
                break;
            }
            pick -= *w;
        }
        match moves.swap_remove(chosen).0 {
            Move::Line(g, j) => {
                self.push(g, j);
                true
            }
            Move::OpenExists { ex } => {
                let Some(w) = self.fresh_name() else { return false };
                let Formula::Exists(v, body) = &self.lines[ex - 1].0 else { return false };
                let Ok(assumption) = body.substitute_free(v, &Term::Name(w.clone())) else { return false };
                self.grow_subproof(rng, spec, ProofTechnique::ExistentialElimination, assumption, &w, Some(ex))
            }
            Move::OpenCp { assumption, name } => {
                self.grow_subproof(rng, spec, ProofTechnique::ConditionalProof, assumption, &name, None)
            }
        }
    }

    fn rollback(&mut self, len: usize) {
        self.lines.truncate(len);
        self.names.truncate(len);
        self.scopes.retain(|s| s.start <= len);
        for s in self.scopes.iter_mut() {
            if s.end.map_or(false, |e| e > len) {
                s.end = None;
            }
        }
    }

    fn grow_subproof(
        &mut self,
        rng: &mut StdRng,
        spec: &FoSpec,
        technique: ProofTechnique,
        assumption: Formula,
        name: &str,
        ex: Option<usize>,
    ) -> bool {
        let before = self.lines.len();
        let start = before + 1;
        self.push(assumption.clone(), Justification::Assumption { technique });
        self.scopes.push(Scope { start, end: None });
        let depth = self.open_depth();
        let inner = rng.gen_range(spec.inner.0..=spec.inner.1);
        let mut added = 0;
        for _ in 0..inner * 3 {
            if added >= inner {
                break;
            }
            if self.step(rng, spec, Some(name)) {
                added += 1;
            }
        }

        // The subproof's last line: the deepest line at this level that uses the assumption.
        let mut target: Option<(usize, usize)> = None;
        for pos in (start + 1)..=self.lines.len() {
            if self.depth_at(pos) != depth {
                continue;
            }
            let g = &self.lines[pos - 1].0;
            let ok = match technique {
                ProofTechnique::ExistentialElimination => {
                    self.single_name_at(pos).map(|n| n.as_str()) == Some(name) && !matches!(g, Formula::Implies(_, _))
                }
                _ => self.names[pos - 1].contains(name),
            };
            let cone = self.cone(pos);
            if ok && cone.contains(&start) && target.map_or(true, |(_, size)| cone.len() >= size) {
                target = Some((pos, cone.len()));
            }
        }
        let Some((end, _)) = target else {
            self.rollback(before);
            return false;
        };
        self.rollback(end);
        let conclusion = match technique {
            ProofTechnique::ExistentialElimination => {
                let g = Formula::Exists(VAR.into(), Box::new(abstract_name(&self.lines[end - 1].0, name)));
                if self.known(self.lines.len() + 1, &g) {
                    self.rollback(before);
                    return false;
                }
                self.push(g.clone(), inference(InferenceRule::ExistentialIntroduction, vec![end]));
                g
            }
            _ => implies(assumption, self.lines[end - 1].0.clone()),
        };
        let last = self.lines.len();
        if let Some(s) = self.scopes.iter_mut().rev().find(|s| s.end.is_none()) {
            s.end = Some(last);
        }
        if self.known(last + 1, &conclusion) {
            self.rollback(before);
            return false;
        }
        let j = match (technique, ex) {
            (ProofTechnique::ExistentialElimination, Some(ex)) => {
                Justification::ExistentialElimination { existential_line: ex, subproof_start: start, subproof_end: last }
            }
            _ => Justification::SubproofConclusion { technique, subproof_start: start, subproof_end: last },
        };
        self.push(conclusion, j);
        true
    }

    // ───────── selection and rebuild ─────────

    fn cone(&self, target: usize) -> Vec<usize> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![target];
        while let Some(p) = stack.pop() {
            if seen.insert(p) {
                stack.extend(self.lines[p - 1].1.referenced_lines());
            }
        }
        seen.into_iter().collect()
    }

    fn score(&self, cone: &[usize]) -> FoScore {
        let mut lines = 0;
        let mut quantifier_steps = 0;
        for &p in cone {
            match &self.lines[p - 1].1 {
                Justification::Premise => continue,
                Justification::Inference { rule, .. } if rule.is_first_order() => quantifier_steps += 1,
                Justification::ExistentialElimination { .. } => quantifier_steps += 2,
                _ => {}
            }
            lines += 1;
        }
        FoScore { lines, quantifier_steps }
    }

    fn acceptable_conclusion(&self, pos: usize, cone: &[usize]) -> bool {
        let c = &self.lines[pos - 1].0;
        let premises: Vec<&Formula> = cone.iter().filter(|&&i| i <= self.n_premises).map(|&i| &self.lines[i - 1].0).collect();
        let premise_names: BTreeSet<&String> = cone.iter().filter(|&&i| i <= self.n_premises).flat_map(|&i| self.names[i - 1].iter()).collect();
        if !self.names[pos - 1].iter().all(|n| premise_names.contains(n)) {
            return false;
        }
        premises.iter().all(|p| {
            !p.alpha_eq(c)
                && match p {
                    Formula::ForAll(v, body) => !matches!(instance_of(v, body, c), Ok(Some(_))),
                    _ => true,
                }
        })
    }

    fn rebuild(&self, cone: &[usize], conclusion: usize, score: FoScore, seed: u64) -> Result<(Theorem, Proof), FoGenError> {
        let mut renumber = vec![0usize; self.lines.len() + 1];
        for (k, &p) in cone.iter().enumerate() {
            renumber[p] = k + 1;
        }
        let premises: Vec<Formula> = cone.iter().filter(|&&p| p <= self.n_premises).map(|&p| self.lines[p - 1].0.clone()).collect();
        let theorem = Theorem::with_difficulty_value(
            premises,
            self.lines[conclusion - 1].0.clone(),
            score.difficulty().unwrap_or(Difficulty::Expert),
            score.total().min(100) as u8,
            None,
            Some("Predicate logic practice".to_string()),
        );
        let mut proof = Proof::new(theorem.clone());
        let invalid = |line: usize, message: String| FoGenError::InvalidProof { seed, line, message };
        for &p in cone.iter().filter(|&&p| p > self.n_premises) {
            let (f, j) = &self.lines[p - 1];
            let r = |n: &usize| renumber[*n];
            match j {
                Justification::Assumption { technique } => {
                    proof.open_subproof(f.clone(), *technique);
                }
                Justification::Inference { rule, lines } => {
                    proof.add_line(f.clone(), inference(*rule, lines.iter().map(r).collect()));
                }
                Justification::SubproofConclusion { technique, subproof_start, subproof_end } => {
                    proof.close_subproof(f.clone(), *technique).ok_or_else(|| invalid(renumber[p], "no open subproof".into()))?;
                    proof.lines.last_mut().expect("closed line").justification = Justification::SubproofConclusion {
                        technique: *technique,
                        subproof_start: r(subproof_start),
                        subproof_end: r(subproof_end),
                    };
                }
                Justification::ExistentialElimination { existential_line, subproof_start, subproof_end } => {
                    proof
                        .close_subproof(f.clone(), ProofTechnique::ExistentialElimination)
                        .ok_or_else(|| invalid(renumber[p], "no open ∃E subproof".into()))?;
                    proof.lines.last_mut().expect("closed line").justification = Justification::ExistentialElimination {
                        existential_line: r(existential_line),
                        subproof_start: r(subproof_start),
                        subproof_end: r(subproof_end),
                    };
                }
                Justification::Premise | Justification::Equivalence { .. } => {
                    return Err(invalid(renumber[p], format!("unexpected justification {}", j.display_string())));
                }
            }
        }
        ProofVerifier::verify_proof(&mut proof);
        if let Some(bad) = proof.lines.iter().find(|l| !l.is_valid) {
            return Err(invalid(bad.line_number, bad.validation_message.clone().unwrap_or_default()));
        }
        if !proof.check_complete() {
            return Err(invalid(proof.lines.len(), "proof does not reach the conclusion".into()));
        }
        Ok((theorem, proof))
    }
}

// ───────────────────────────── consistency ─────────────────────────────

/// Do the premises have a model? Exact for premises of the generator's shapes (∀x φ, ∃x φ and
/// ground φ(n), φ quantifier-free over one-place predicates): the domain can be every type
/// (set of predicates) allowed by all universal premises, one element each.
pub fn monadic_satisfiable(premises: &[Formula]) -> bool {
    let types: Vec<u32> = (0..(1u32 << PREDICATES.len())).collect();
    let eval = |f: &Formula, t: u32| eval_type(f, t);
    let allowed: Vec<u32> = types
        .into_iter()
        .filter(|&t| premises.iter().all(|p| match p {
            Formula::ForAll(_, body) => eval(body, t) == Some(true),
            _ => true,
        }))
        .collect();
    if allowed.is_empty() {
        return false;
    }
    let exists_ok = premises.iter().all(|p| match p {
        Formula::Exists(_, body) => allowed.iter().any(|&t| eval(body, t) == Some(true)),
        _ => true,
    });
    let ground: Vec<&Formula> = premises.iter().filter(|p| !matches!(p, Formula::ForAll(_, _) | Formula::Exists(_, _))).collect();
    let names: BTreeSet<String> = ground.iter().flat_map(|g| g.free_names()).collect();
    let names_ok = names.iter().all(|n| {
        let facts: Vec<&&Formula> = ground.iter().filter(|g| g.has_free_name(n)).collect();
        facts.iter().all(|g| g.free_names().len() == 1)
            && allowed.iter().any(|&t| facts.iter().all(|g| eval(g, t) == Some(true)))
    });
    exists_ok && names_ok
}

/// Truth of a quantifier-free monadic formula at an element of type `t` (bit i: predicate i).
fn eval_type(f: &Formula, t: u32) -> Option<bool> {
    Some(match f {
        Formula::Predicate(p, args) if args.len() == 1 => {
            let i = PREDICATES.iter().position(|q| q == p)?;
            t & (1 << i) != 0
        }
        Formula::Not(i) => !eval_type(i, t)?,
        Formula::And(l, r) => eval_type(l, t)? && eval_type(r, t)?,
        Formula::Or(l, r) => eval_type(l, t)? || eval_type(r, t)?,
        Formula::Implies(l, r) => !eval_type(l, t)? || eval_type(r, t)?,
        Formula::Biconditional(l, r) => eval_type(l, t)? == eval_type(r, t)?,
        _ => return None,
    })
}
