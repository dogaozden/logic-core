//! Two-layer theorem generation with equivalence obfuscation.
//!
//! Strategy:
//! 1. Generate simple valid theorem (base)
//! 2. Wrap as single formula: (P1 ∧ P2 ∧ ...) ⊃ C
//! 3. Apply N random equivalence transformations
//!
//! Key insight: Semantic validity is GUARANTEED because equivalence
//! transformations preserve truth tables.

use rand::Rng;
use crate::models::Formula;
use crate::models::rules::equivalence::EquivalenceRule;
use crate::models::theorem::{BaseComplexity, Difficulty, DifficultySpec, DifficultyTier, Theme, Theorem};
use crate::services::truth_table::{is_tautology, is_tautology_dynamic};

/// Configuration for obfuscation generation
#[derive(Debug, Clone)]
pub struct ObfuscateConfig {
    pub atom_pool: Vec<String>,
    pub transform_count: usize,
    pub difficulty: Difficulty,
    pub difficulty_value: u8,
    /// Depth of formula substitutions (0 = no substitution, 1-2 = complex formulas)
    pub substitution_depth: usize,
    /// Number of bridge atoms that appear in multiple substitution partitions
    pub bridge_atoms: usize,
    /// Whether to force multi-rule transformation chains (gnarly combos)
    pub gnarly_combos: bool,
}

impl ObfuscateConfig {
    /// Create configuration from a difficulty value (1-100)
    pub fn for_difficulty_value(d: u8) -> Self {
        let d_clamped = d.clamp(1, 100) as usize;

        // Scale atom pool based on difficulty
        // 1-40: 2 atoms, 41-60: 3 atoms, 61-80: 4 atoms, 81-100: 5 atoms
        let atom_count = match d_clamped {
            1..=40 => 2,
            41..=60 => 3,
            61..=80 => 4,
            _ => 5,
        };
        let atoms = ["P", "Q", "R", "S", "T"]
            .into_iter()
            .take(atom_count)
            .map(String::from)
            .collect();

        // Scale transform count based on difficulty tiers
        // Easy (1-25): 1-3 transforms
        // Medium (26-45): 3-6 transforms
        // Hard (46-70): 6-11 transforms
        // Expert (71-85): 11-16 transforms
        // Nightmare (86-95): 16-20 transforms
        // Marathon (96-100): 20-24 transforms
        let transform_count = match d_clamped {
            1..=25 => 1 + (d_clamped - 1) * 2 / 24, // 1-3
            26..=45 => 3 + (d_clamped - 26) * 3 / 19, // 3-6
            46..=70 => 6 + (d_clamped - 46) * 5 / 24, // 6-11
            71..=85 => 11 + (d_clamped - 71) * 5 / 14, // 11-16
            86..=95 => 16 + (d_clamped - 86) * 4 / 9, // 16-20
            _ => 20 + (d_clamped - 96) * 4 / 4, // 20-24
        };

        // Layer 3: substitution depth based on difficulty
        // 1-69: 0 (no substitution)
        // 70-84: 1 (simple substitutions like A ∨ B)
        // 85-100: 2 (nested substitutions like (A ∨ B) ⊃ C)
        let substitution_depth = match d_clamped {
            1..=69 => 0,
            70..=84 => 1,
            _ => 2,
        };

        Self {
            atom_pool: atoms,
            transform_count,
            difficulty: Self::preset_for_value(d),
            difficulty_value: d,
            substitution_depth,
            bridge_atoms: 0,
            gnarly_combos: d >= 85,
        }
    }

    fn preset_for_value(value: u8) -> Difficulty {
        match value {
            1..=25 => Difficulty::Easy,
            26..=45 => Difficulty::Medium,
            46..=70 => Difficulty::Hard,
            _ => Difficulty::Expert,
        }
    }

    /// Create configuration from a DifficultySpec.
    pub fn from_spec(spec: &DifficultySpec) -> Self {
        let atoms = build_atom_pool(spec.variables);
        let difficulty_value = Self::difficulty_value_from_spec(spec);
        Self {
            atom_pool: atoms,
            transform_count: spec.transforms_per_pass as usize,
            difficulty: Self::preset_for_value(difficulty_value),
            difficulty_value,
            substitution_depth: spec.substitution_depth as usize,
            bridge_atoms: spec.bridge_atoms.unwrap_or(0) as usize,
            gnarly_combos: spec.gnarly_combos.unwrap_or(difficulty_value >= 85),
        }
    }

    /// Derive a legacy 1-100 difficulty value from a DifficultySpec.
    ///
    /// Uses total effective transforms (`passes * transforms_per_pass`) plus a
    /// bonus for substitution depth so that low-tier specs (Baby, Easy) stay well
    /// below the gnarly-combo threshold (85) while Expert+ tiers exceed it.
    ///
    /// Reference tier mappings:
    ///   Baby/Easy  (1*2=2,  sub 0) -> ~13
    ///   Medium     (1*5=5,  sub 0) -> ~38
    ///   Hard       (1*10=10,sub 0) -> ~62
    ///   Expert     (1*15=15,sub 2) -> ~88  (triggers gnarly combos)
    ///   Nightmare  (2*12=24,sub 3) -> ~95
    ///   Marathon+  (3*15+)         -> 100
    fn difficulty_value_from_spec(spec: &DifficultySpec) -> u8 {
        let total_transforms = (spec.passes as u32) * (spec.transforms_per_pass as u32);
        // Base: map total transforms to difficulty using the same breakpoints
        // as for_difficulty_value (which maps single-pass transform counts).
        let base = match total_transforms {
            0..=3   => 1 + (total_transforms.saturating_sub(1)) * 24 / 2,   // 1-25
            4..=6   => 26 + (total_transforms - 4) * 19 / 2,                // 26-45
            7..=11  => 46 + (total_transforms - 7) * 24 / 4,                // 46-70
            12..=16 => 71 + (total_transforms - 12) * 14 / 4,               // 71-85
            17..=20 => 86 + (total_transforms - 17) * 9 / 3,                // 86-95
            _       => 96 + (total_transforms.saturating_sub(21)).min(4),    // 96-100
        } as u8;

        // Substitution depth bonus: each level adds 3 points,
        // so Expert (sub 2) gets +6, Nightmare (sub 3) gets +9.
        let sub_bonus = (spec.substitution_depth as u16) * 3;

        ((base as u16).saturating_add(sub_bonus).min(100)) as u8
    }
}

/// Safety bounds for formula complexity
const MAX_FORMULA_DEPTH: usize = 100;
const MAX_FORMULA_NODES: usize = 20_000;

/// Build an atom pool of `n` unique atom names.
/// 1-5: P, Q, R, S, T
/// 6+: extend with A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, U, V, W, X, Y, Z
pub fn build_atom_pool(n: u8) -> Vec<String> {
    let base = ["P", "Q", "R", "S", "T"];
    let extended = [
        "A", "B", "C", "D", "E", "F", "G", "H", "I", "J",
        "K", "L", "M", "N", "O", "U", "V", "W", "X", "Y", "Z",
    ];
    let mut pool: Vec<String> = Vec::with_capacity(n as usize);
    for &a in base.iter().take(n as usize) {
        pool.push(a.to_string());
    }
    if (n as usize) > base.len() {
        let remaining = (n as usize) - base.len();
        for &a in extended.iter().take(remaining) {
            pool.push(a.to_string());
        }
    }
    pool
}

/// Count total nodes in a formula tree.
fn node_count(formula: &Formula) -> usize {
    match formula {
        Formula::Atom(_) | Formula::Contradiction => 1,
        Formula::Not(inner) => 1 + node_count(inner),
        Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) | Formula::Biconditional(l, r) => {
            1 + node_count(l) + node_count(r)
        }
    }
}

/// Base argument forms for generating simple valid theorems
#[derive(Debug, Clone, Copy)]
enum BaseForm {
    /// Modus Ponens: P, P ⊃ Q ⊢ Q
    ModusPonens,
    /// Modus Tollens: P ⊃ Q, ~Q ⊢ ~P
    ModusTollens,
    /// Hypothetical Syllogism: P ⊃ Q, Q ⊃ R ⊢ P ⊃ R
    HypotheticalSyllogism,
    /// Disjunctive Syllogism: P ∨ Q, ~P ⊢ Q
    DisjunctiveSyllogism,
    /// Simplification: P ∧ Q ⊢ P
    Simplification,
    /// Conjunction: P, Q ⊢ P ∧ Q
    Conjunction,
    /// Constructive Dilemma: (P ⊃ Q) ∧ (R ⊃ S), P ∨ R ⊢ Q ∨ S
    ConstructiveDilemma,
    // === Complex forms for high difficulty (≥70) ===
    /// Constructive Dilemma Full: P∨Q, P⊃R, Q⊃R ⊢ R (forces case analysis)
    ConstructiveDilemmaFull,
    /// Nested CP: P⊃(Q⊃R), P, Q ⊢ R (nested conditionals)
    NestedCP,
    /// Chain4: P⊃Q, Q⊃R, R⊃S, P ⊢ S (long chain)
    Chain4,
}

impl BaseForm {
    /// Get standard forms (used for lower difficulties)
    fn standard() -> Vec<BaseForm> {
        vec![
            BaseForm::ModusPonens,
            BaseForm::ModusTollens,
            BaseForm::HypotheticalSyllogism,
            BaseForm::DisjunctiveSyllogism,
            BaseForm::Simplification,
            BaseForm::Conjunction,
            BaseForm::ConstructiveDilemma,
        ]
    }

    /// Get complex forms (used only for high difficulty ≥70)
    fn complex() -> Vec<BaseForm> {
        vec![
            BaseForm::ConstructiveDilemmaFull,
            BaseForm::NestedCP,
            BaseForm::Chain4,
        ]
    }

    fn all() -> Vec<BaseForm> {
        let mut forms = Self::standard();
        forms.extend(Self::complex());
        forms
    }

    /// Get forms that can use the given number of atoms and difficulty
    fn for_atom_count_and_difficulty(count: usize, difficulty: u8) -> Vec<BaseForm> {
        let base_forms = match count {
            0..=1 => vec![], // Need at least 2 atoms
            2 => vec![
                BaseForm::ModusPonens,
                BaseForm::ModusTollens,
                BaseForm::DisjunctiveSyllogism,
                BaseForm::Simplification,
                BaseForm::Conjunction,
            ],
            3 => {
                // 3 atoms: standard forms + NestedCP and ConstructiveDilemmaFull
                let mut forms = Self::standard();
                if difficulty >= 70 {
                    forms.push(BaseForm::NestedCP);
                    forms.push(BaseForm::ConstructiveDilemmaFull);
                }
                forms
            }
            _ => {
                // 4+ atoms: all forms including Chain4
                if difficulty >= 70 {
                    Self::all()
                } else {
                    Self::standard()
                }
            }
        };
        base_forms
    }

    /// Legacy method for compatibility
    fn for_atom_count(count: usize) -> Vec<BaseForm> {
        Self::for_atom_count_and_difficulty(count, 50) // default to medium difficulty
    }
}

/// Main generator struct
pub struct ObfuscateGenerator {
    config: ObfuscateConfig,
}

impl ObfuscateGenerator {
    pub fn new(config: ObfuscateConfig) -> Self {
        Self { config }
    }

    /// Generate an obfuscated theorem (tautology format)
    pub fn generate(&self, rng: &mut impl Rng) -> Theorem {
        // Layer 1: Generate simple base theorem
        let (premises, conclusion) = self.generate_base_theorem(rng);

        // Layer 3: Apply atom substitutions for high difficulty
        // This replaces simple atoms (P, Q, R) with complex formulas (A∨~B, C.D, E⊃F)
        // dramatically increasing the "surface area" for equivalence transformations
        let (premises, conclusion) = self.apply_substitutions(premises, conclusion, rng);

        // Layer 2: Wrap as single tautology
        let wrapped = self.wrap_as_conditional(&premises, &conclusion);

        // Verify the wrapped formula is a tautology before transforming
        debug_assert!(is_tautology(&wrapped), "Wrapped formula should be a tautology");

        // Apply random transformations
        let obfuscated = self.apply_transformations(wrapped, rng);

        // Verify the obfuscated formula is still a tautology
        debug_assert!(is_tautology(&obfuscated), "Obfuscated formula should still be a tautology");

        // Return as tautology (no premises)
        Theorem::with_difficulty_value(
            vec![], // No premises - it's a tautology
            obfuscated,
            self.config.difficulty,
            self.config.difficulty_value,
            Some(Theme::Equivalence),
            None,
        )
    }

    /// Generate an obfuscated theorem using a DifficultySpec (multi-pass pipeline).
    pub fn generate_with_spec(spec: &DifficultySpec, rng: &mut impl Rng) -> Theorem {
        let formula = Self::run_spec_pipeline(spec, rng);

        Theorem::with_difficulty_value(
            vec![],
            formula,
            Difficulty::Expert,
            100,
            Some(Theme::Equivalence),
            None,
        )
    }

    /// Generate an obfuscated theorem for a specific DifficultyTier.
    /// Sets the `tier` field on the returned Theorem.
    pub fn generate_with_tier(tier: DifficultyTier, rng: &mut impl Rng) -> Theorem {
        let spec = DifficultySpec::from_tier(tier);
        let formula = Self::run_spec_pipeline(&spec, rng);

        Theorem::from_tier(
            vec![],
            formula,
            tier,
            Some(Theme::Equivalence),
        )
    }

    /// Generate an obfuscated theorem for a specific DifficultyTier using a
    /// (possibly overridden) DifficultySpec. The spec controls the pipeline
    /// parameters while the tier determines the theorem's metadata (difficulty
    /// label and tier field).
    pub fn generate_with_tier_spec(tier: DifficultyTier, spec: &DifficultySpec, rng: &mut impl Rng) -> Theorem {
        let formula = Self::run_spec_pipeline(spec, rng);

        Theorem::from_tier(
            vec![],
            formula,
            tier,
            Some(Theme::Equivalence),
        )
    }

    /// Core spec-based pipeline: generates a tautology formula from a DifficultySpec.
    fn run_spec_pipeline(spec: &DifficultySpec, rng: &mut impl Rng) -> Formula {
        let config = ObfuscateConfig::from_spec(spec);
        let gen = ObfuscateGenerator::new(config);

        // Layer 1: Generate base theorem
        let use_complex = spec.base_complexity == BaseComplexity::Complex;
        let (premises, conclusion) = gen.generate_base_theorem_with_complexity(rng, use_complex);

        // Layer 2: Apply substitutions (once, before multi-pass)
        let (premises, conclusion) = if spec.substitution_depth > 0 {
            gen.apply_substitutions(premises, conclusion, rng)
        } else {
            (premises, conclusion)
        };

        // Wrap as conditional tautology
        let mut formula = gen.wrap_as_conditional(&premises, &conclusion);
        debug_assert!(
            is_tautology_dynamic(&formula),
            "Initial wrapped formula should be a tautology"
        );

        // Multi-pass pipeline
        let max_nodes = spec.max_formula_nodes.unwrap_or(MAX_FORMULA_NODES as u32) as usize;
        for _pass in 0..spec.passes {
            // Safety check: skip if formula too large
            if formula.depth() >= MAX_FORMULA_DEPTH || node_count(&formula) >= max_nodes {
                break;
            }

            // Apply transforms for this pass
            formula = gen.apply_transformations(formula, rng);

            debug_assert!(
                is_tautology_dynamic(&formula),
                "Formula should remain a tautology after pass"
            );
        }

        // Defence-in-depth: verify the final formula is still a tautology.
        // The per-pass check above only fires inside the loop and only in debug
        // builds; this catches any issue introduced by the very last pass
        // (including simplify_negations) regardless of where the loop exited.
        debug_assert!(
            is_tautology_dynamic(&formula),
            "Final formula after all passes must be a tautology"
        );

        formula
    }

    /// Generate base theorem with explicit complexity control.
    fn generate_base_theorem_with_complexity(&self, rng: &mut impl Rng, use_complex: bool) -> (Vec<Formula>, Formula) {
        let atoms = &self.config.atom_pool;
        if atoms.is_empty() {
            let p = Formula::Atom("P".to_string());
            return (vec![], Formula::Implies(Box::new(p.clone()), Box::new(p)));
        }

        let available_forms = if use_complex {
            // Complex mode: use ONLY complex base forms for harder proof structure.
            // Standard forms (Simp, Conj, MP, etc.) produce trivially short proofs
            // underneath the obfuscation, making difficulty uneven within a tier.
            let mut forms = BaseForm::complex();
            // Chain4 requires 4+ atoms; filter it out if we don't have enough
            if atoms.len() < 4 {
                forms.retain(|f| !matches!(f, BaseForm::Chain4));
            }
            // NestedCP and CDFull require 3+ atoms
            if atoms.len() < 3 {
                forms.retain(|f| !matches!(f, BaseForm::NestedCP | BaseForm::ConstructiveDilemmaFull));
            }
            // Fallback: if no complex forms fit (< 3 atoms), use standard
            if forms.is_empty() {
                BaseForm::for_atom_count(atoms.len())
            } else {
                forms
            }
        } else {
            BaseForm::for_atom_count(atoms.len())
        };

        if available_forms.is_empty() {
            let p = Formula::Atom(atoms[0].clone());
            return (vec![], Formula::Implies(Box::new(p.clone()), Box::new(p)));
        }

        let form = available_forms[rng.gen_range(0..available_forms.len())];
        self.instantiate_base_form(form, atoms)
    }

    /// Instantiate a base form with the given atoms (factored out for reuse).
    fn instantiate_base_form(&self, form: BaseForm, atoms: &[String]) -> (Vec<Formula>, Formula) {
        let p = Formula::Atom(atoms[0].clone());
        let q = Formula::Atom(atoms[1 % atoms.len()].clone());
        let r = if atoms.len() > 2 {
            Formula::Atom(atoms[2].clone())
        } else {
            Formula::Atom(atoms[0].clone())
        };
        let s = if atoms.len() > 3 {
            Formula::Atom(atoms[3].clone())
        } else {
            Formula::Atom(atoms[1 % atoms.len()].clone())
        };

        match form {
            BaseForm::ModusPonens => (
                vec![p.clone(), Formula::Implies(Box::new(p), Box::new(q.clone()))],
                q,
            ),
            BaseForm::ModusTollens => (
                vec![Formula::Implies(Box::new(p.clone()), Box::new(q.clone())), Formula::Not(Box::new(q))],
                Formula::Not(Box::new(p)),
            ),
            BaseForm::HypotheticalSyllogism => (
                vec![Formula::Implies(Box::new(p.clone()), Box::new(q.clone())), Formula::Implies(Box::new(q), Box::new(r.clone()))],
                Formula::Implies(Box::new(p), Box::new(r)),
            ),
            BaseForm::DisjunctiveSyllogism => (
                vec![Formula::Or(Box::new(p.clone()), Box::new(q.clone())), Formula::Not(Box::new(p))],
                q,
            ),
            BaseForm::Simplification => (
                vec![Formula::And(Box::new(p.clone()), Box::new(q))],
                p,
            ),
            BaseForm::Conjunction => (
                vec![p.clone(), q.clone()],
                Formula::And(Box::new(p), Box::new(q)),
            ),
            BaseForm::ConstructiveDilemma => (
                vec![
                    Formula::And(
                        Box::new(Formula::Implies(Box::new(p.clone()), Box::new(q.clone()))),
                        Box::new(Formula::Implies(Box::new(r.clone()), Box::new(s.clone()))),
                    ),
                    Formula::Or(Box::new(p), Box::new(r)),
                ],
                Formula::Or(Box::new(q), Box::new(s)),
            ),
            BaseForm::ConstructiveDilemmaFull => (
                vec![
                    Formula::Or(Box::new(p.clone()), Box::new(q.clone())),
                    Formula::Implies(Box::new(p), Box::new(r.clone())),
                    Formula::Implies(Box::new(q), Box::new(r.clone())),
                ],
                r,
            ),
            BaseForm::NestedCP => (
                vec![
                    Formula::Implies(Box::new(p.clone()), Box::new(Formula::Implies(Box::new(q.clone()), Box::new(r.clone())))),
                    p,
                    q,
                ],
                r,
            ),
            BaseForm::Chain4 => (
                vec![
                    Formula::Implies(Box::new(p.clone()), Box::new(q.clone())),
                    Formula::Implies(Box::new(q), Box::new(r.clone())),
                    Formula::Implies(Box::new(r), Box::new(s.clone())),
                    p,
                ],
                s,
            ),
        }
    }

    /// Generate a simple valid argument form
    fn generate_base_theorem(&self, rng: &mut impl Rng) -> (Vec<Formula>, Formula) {
        let atoms = &self.config.atom_pool;

        // Ensure we have at least one atom, fallback to "P" if empty
        if atoms.is_empty() {
            let p = Formula::Atom("P".to_string());
            return (vec![], Formula::Implies(Box::new(p.clone()), Box::new(p)));
        }

        let available_forms = BaseForm::for_atom_count_and_difficulty(atoms.len(), self.config.difficulty_value);

        if available_forms.is_empty() {
            // Fallback to simple tautology P ⊃ P
            let p = Formula::Atom(atoms[0].clone());
            return (vec![], Formula::Implies(Box::new(p.clone()), Box::new(p)));
        }

        let form = available_forms[rng.gen_range(0..available_forms.len())];

        // Get atoms for this form
        let p = Formula::Atom(atoms[0].clone());
        let q = Formula::Atom(atoms[1 % atoms.len()].clone());
        let r = if atoms.len() > 2 {
            Formula::Atom(atoms[2].clone())
        } else {
            Formula::Atom(atoms[0].clone())
        };
        let s = if atoms.len() > 3 {
            Formula::Atom(atoms[3].clone())
        } else {
            Formula::Atom(atoms[1 % atoms.len()].clone())
        };

        match form {
            BaseForm::ModusPonens => {
                // P, P ⊃ Q ⊢ Q
                (
                    vec![
                        p.clone(),
                        Formula::Implies(Box::new(p), Box::new(q.clone())),
                    ],
                    q,
                )
            }
            BaseForm::ModusTollens => {
                // P ⊃ Q, ~Q ⊢ ~P
                (
                    vec![
                        Formula::Implies(Box::new(p.clone()), Box::new(q.clone())),
                        Formula::Not(Box::new(q)),
                    ],
                    Formula::Not(Box::new(p)),
                )
            }
            BaseForm::HypotheticalSyllogism => {
                // P ⊃ Q, Q ⊃ R ⊢ P ⊃ R
                (
                    vec![
                        Formula::Implies(Box::new(p.clone()), Box::new(q.clone())),
                        Formula::Implies(Box::new(q), Box::new(r.clone())),
                    ],
                    Formula::Implies(Box::new(p), Box::new(r)),
                )
            }
            BaseForm::DisjunctiveSyllogism => {
                // P ∨ Q, ~P ⊢ Q
                (
                    vec![
                        Formula::Or(Box::new(p.clone()), Box::new(q.clone())),
                        Formula::Not(Box::new(p)),
                    ],
                    q,
                )
            }
            BaseForm::Simplification => {
                // P ∧ Q ⊢ P
                (
                    vec![Formula::And(Box::new(p.clone()), Box::new(q))],
                    p,
                )
            }
            BaseForm::Conjunction => {
                // P, Q ⊢ P ∧ Q
                (
                    vec![p.clone(), q.clone()],
                    Formula::And(Box::new(p), Box::new(q)),
                )
            }
            BaseForm::ConstructiveDilemma => {
                // (P ⊃ Q) ∧ (R ⊃ S), P ∨ R ⊢ Q ∨ S
                (
                    vec![
                        Formula::And(
                            Box::new(Formula::Implies(Box::new(p.clone()), Box::new(q.clone()))),
                            Box::new(Formula::Implies(Box::new(r.clone()), Box::new(s.clone()))),
                        ),
                        Formula::Or(Box::new(p), Box::new(r)),
                    ],
                    Formula::Or(Box::new(q), Box::new(s)),
                )
            }
            BaseForm::ConstructiveDilemmaFull => {
                // P∨Q, P⊃R, Q⊃R ⊢ R (forces case analysis)
                (
                    vec![
                        Formula::Or(Box::new(p.clone()), Box::new(q.clone())),
                        Formula::Implies(Box::new(p), Box::new(r.clone())),
                        Formula::Implies(Box::new(q), Box::new(r.clone())),
                    ],
                    r,
                )
            }
            BaseForm::NestedCP => {
                // P⊃(Q⊃R), P, Q ⊢ R (nested conditionals)
                (
                    vec![
                        Formula::Implies(
                            Box::new(p.clone()),
                            Box::new(Formula::Implies(Box::new(q.clone()), Box::new(r.clone()))),
                        ),
                        p,
                        q,
                    ],
                    r,
                )
            }
            BaseForm::Chain4 => {
                // P⊃Q, Q⊃R, R⊃S, P ⊢ S (long chain)
                (
                    vec![
                        Formula::Implies(Box::new(p.clone()), Box::new(q.clone())),
                        Formula::Implies(Box::new(q), Box::new(r.clone())),
                        Formula::Implies(Box::new(r), Box::new(s.clone())),
                        p,
                    ],
                    s,
                )
            }
        }
    }

    /// Layer 2: Apply atom substitutions for high difficulty.
    /// Replaces base atoms (P, Q, R) with complex formulas built from the
    /// remaining atoms in the configured pool. This ensures the `variables`
    /// parameter actually controls how many distinct atoms appear in the
    /// final formula.
    fn apply_substitutions(
        &self,
        premises: Vec<Formula>,
        conclusion: Formula,
        rng: &mut impl Rng,
    ) -> (Vec<Formula>, Formula) {
        if self.config.substitution_depth == 0 {
            return (premises, conclusion);
        }

        // Collect all unique atoms from the base theorem
        let mut base_atoms: Vec<String> = vec![];
        for p in &premises {
            for atom in p.atoms() {
                if !base_atoms.contains(&atom) {
                    base_atoms.push(atom);
                }
            }
        }
        for atom in conclusion.atoms() {
            if !base_atoms.contains(&atom) {
                base_atoms.push(atom);
            }
        }

        // Sort for deterministic behavior
        base_atoms.sort();

        // Use remaining atoms from the configured pool for substitutions.
        // The base form uses 3-4 atoms; the rest of the pool becomes the
        // ingredient list for replacement formulas.
        let remaining: Vec<String> = self.config.atom_pool.iter()
            .filter(|a| !base_atoms.contains(a))
            .cloned()
            .collect();

        // Partition remaining atoms evenly among base atoms so each
        // replacement formula uses a distinct set of variables.
        // IMPORTANT: Each group also includes the base atom it replaces,
        // so that the original atom is preserved in the substituted formula.
        // Without this, a 7-variable spec with a 3-atom base form would
        // end up with only 4 atoms (the remaining pool), losing the original 3.
        let sub_atom_groups: Vec<Vec<String>> = if remaining.is_empty() {
            // Fallback: create atoms from A-Z (safety net for tiny pools)
            let sub_atoms: Vec<String> = ('A'..='Z')
                .take(base_atoms.len() * 2)
                .map(|c| c.to_string())
                .collect();
            base_atoms.iter().enumerate().map(|(i, base_atom)| {
                let start = i * 2;
                let end = (start + 2).min(sub_atoms.len());
                let mut group = vec![base_atom.clone()];
                group.extend_from_slice(&sub_atoms[start..end]);
                group
            }).collect()
        } else if remaining.len() < base_atoms.len() {
            // Not enough to partition: give each base atom the full pool + itself
            base_atoms.iter().map(|base_atom| {
                let mut group = vec![base_atom.clone()];
                group.extend(remaining.clone());
                group
            }).collect()
        } else {
            // Separate bridge atoms from remaining pool
            let bridge_count = self.config.bridge_atoms.min(remaining.len());
            let (bridges, non_bridge): (Vec<String>, Vec<String>) = if bridge_count > 0 && base_atoms.len() >= 2 {
                // Shuffle remaining and take first bridge_count as bridges
                let mut shuffled_remaining = remaining.clone();
                for i in (1..shuffled_remaining.len()).rev() {
                    let j = rng.gen_range(0..=i);
                    shuffled_remaining.swap(i, j);
                }
                let bridges: Vec<String> = shuffled_remaining[..bridge_count].to_vec();
                let non_bridge: Vec<String> = shuffled_remaining[bridge_count..].to_vec();
                (bridges, non_bridge)
            } else {
                (vec![], remaining.clone())
            };

            // Partition non_bridge atoms evenly, distributing leftovers to the first groups
            let partition_source = &non_bridge;
            let mut groups = Vec::new();
            if partition_source.is_empty() {
                // All remaining atoms are bridges; each group gets just its base atom
                for i in 0..base_atoms.len() {
                    groups.push(vec![base_atoms[i].clone()]);
                }
            } else if partition_source.len() < base_atoms.len() {
                // Not enough non-bridge atoms to partition: give each base atom the full non-bridge pool + itself
                for i in 0..base_atoms.len() {
                    let mut group = vec![base_atoms[i].clone()];
                    group.extend(partition_source.clone());
                    groups.push(group);
                }
            } else {
                let chunk_size = partition_source.len() / base_atoms.len();
                let leftover = partition_source.len() % base_atoms.len();
                let mut offset = 0;
                for i in 0..base_atoms.len() {
                    let size = chunk_size + if i < leftover { 1 } else { 0 };
                    let mut group = vec![base_atoms[i].clone()];
                    group.extend_from_slice(&partition_source[offset..offset + size]);
                    offset += size;
                    groups.push(group);
                }
            }

            // Add each bridge atom to 2 randomly-chosen distinct groups
            for bridge in &bridges {
                if groups.len() >= 2 {
                    let mut indices: Vec<usize> = (0..groups.len()).collect();
                    // Shuffle and pick first 2
                    for i in (1..indices.len()).rev() {
                        let j = rng.gen_range(0..=i);
                        indices.swap(i, j);
                    }
                    groups[indices[0]].push(bridge.clone());
                    groups[indices[1]].push(bridge.clone());
                }
            }

            groups
        };

        // Build substitution map: each base atom → random formula using its atom group
        let mut substitutions: std::collections::HashMap<String, Formula> = std::collections::HashMap::new();
        for (i, atom) in base_atoms.iter().enumerate() {
            let atom_slice = &sub_atom_groups[i];
            let replacement = self.random_formula(rng, self.config.substitution_depth, atom_slice);
            substitutions.insert(atom.clone(), replacement);
        }

        // Apply substitutions to all premises and conclusion
        let new_premises: Vec<Formula> = premises
            .into_iter()
            .map(|p| self.substitute_all(&p, &substitutions))
            .collect();
        let new_conclusion = self.substitute_all(&conclusion, &substitutions);

        (new_premises, new_conclusion)
    }

    /// Generate a random formula of given depth using the provided atoms.
    /// Guarantees that ALL atoms in the slice appear at least once.
    ///
    /// Strategy:
    /// 1. Shuffle atoms and build a balanced binary tree (seed) using every atom once.
    /// 2. Grow random leaf nodes deeper (controlled by `depth`) to add complexity.
    fn random_formula(&self, rng: &mut impl Rng, depth: usize, atoms: &[String]) -> Formula {
        if atoms.is_empty() {
            return Formula::Atom("X".to_string());
        }
        if atoms.len() == 1 {
            return Formula::Atom(atoms[0].clone());
        }

        // Step 1: Shuffle atoms
        let mut shuffled: Vec<String> = atoms.to_vec();
        for i in (1..shuffled.len()).rev() {
            let j = rng.gen_range(0..=i);
            shuffled.swap(i, j);
        }

        // Step 2: Build seed — pair atoms into a balanced binary tree
        let mut formulas: Vec<Formula> = shuffled.iter()
            .map(|a| Formula::Atom(a.clone()))
            .collect();

        while formulas.len() > 1 {
            let mut next_level = Vec::new();
            let mut i = 0;
            while i + 1 < formulas.len() {
                let left = formulas[i].clone();
                let right = formulas[i + 1].clone();
                let combined = Self::random_binary_connective(rng, left, right);
                next_level.push(combined);
                i += 2;
            }
            if i < formulas.len() {
                next_level.push(formulas[i].clone());
            }
            formulas = next_level;
        }

        let mut seed = formulas.into_iter().next().unwrap();

        // Step 3: Grow random leaves to add depth
        if depth > 0 {
            let growth_passes = depth * 2;
            for _ in 0..growth_passes {
                seed = Self::grow_random_leaf(rng, seed, atoms, depth);
            }
        }

        seed
    }

    fn random_binary_connective(rng: &mut impl Rng, left: Formula, right: Formula) -> Formula {
        match rng.gen_range(0..3) {
            0 => Formula::And(Box::new(left), Box::new(right)),
            1 => Formula::Or(Box::new(left), Box::new(right)),
            _ => Formula::Implies(Box::new(left), Box::new(right)),
        }
    }

    fn grow_random_leaf(rng: &mut impl Rng, formula: Formula, atoms: &[String], max_depth: usize) -> Formula {
        let leaf_paths = Self::collect_leaf_paths(&formula, &[]);
        if leaf_paths.is_empty() {
            return formula;
        }

        let path = &leaf_paths[rng.gen_range(0..leaf_paths.len())];

        if path.len() >= max_depth + 2 {
            return formula;
        }

        let atom = &atoms[rng.gen_range(0..atoms.len())];
        let new_atom = Formula::Atom(atom.clone());
        let current_leaf = Self::formula_at_path(&formula, path);

        // Expand leaf while preserving it (maintains guaranteed coverage)
        let expansion = match rng.gen_range(0..4) {
            0 => Formula::Not(Box::new(current_leaf)),
            1 => Self::random_binary_connective(rng, current_leaf, new_atom),
            2 => Self::random_binary_connective(rng, new_atom, current_leaf),
            _ => Self::random_binary_connective(rng, current_leaf, Formula::Not(Box::new(new_atom))),
        };

        Self::replace_at_growth_path(&formula, path, &expansion)
    }

    fn collect_leaf_paths(formula: &Formula, current_path: &[usize]) -> Vec<Vec<usize>> {
        match formula {
            Formula::Atom(_) | Formula::Contradiction => vec![current_path.to_vec()],
            Formula::Not(inner) => {
                let mut p = current_path.to_vec();
                p.push(0);
                Self::collect_leaf_paths(inner, &p)
            }
            Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) | Formula::Biconditional(l, r) => {
                let mut lp = current_path.to_vec();
                lp.push(1);
                let mut rp = current_path.to_vec();
                rp.push(2);
                let mut paths = Self::collect_leaf_paths(l, &lp);
                paths.extend(Self::collect_leaf_paths(r, &rp));
                paths
            }
        }
    }

    fn formula_at_path(formula: &Formula, path: &[usize]) -> Formula {
        if path.is_empty() {
            return formula.clone();
        }
        match (formula, path[0]) {
            (Formula::Not(inner), 0) => Self::formula_at_path(inner, &path[1..]),
            (Formula::And(l, _), 1) | (Formula::Or(l, _), 1) | (Formula::Implies(l, _), 1) | (Formula::Biconditional(l, _), 1) => {
                Self::formula_at_path(l, &path[1..])
            }
            (Formula::And(_, r), 2) | (Formula::Or(_, r), 2) | (Formula::Implies(_, r), 2) | (Formula::Biconditional(_, r), 2) => {
                Self::formula_at_path(r, &path[1..])
            }
            _ => formula.clone(),
        }
    }

    fn replace_at_growth_path(formula: &Formula, path: &[usize], replacement: &Formula) -> Formula {
        if path.is_empty() {
            return replacement.clone();
        }
        match (formula, path[0]) {
            (Formula::Not(inner), 0) => Formula::Not(Box::new(Self::replace_at_growth_path(inner, &path[1..], replacement))),
            (Formula::And(l, r), 1) => Formula::And(Box::new(Self::replace_at_growth_path(l, &path[1..], replacement)), r.clone()),
            (Formula::And(l, r), 2) => Formula::And(l.clone(), Box::new(Self::replace_at_growth_path(r, &path[1..], replacement))),
            (Formula::Or(l, r), 1) => Formula::Or(Box::new(Self::replace_at_growth_path(l, &path[1..], replacement)), r.clone()),
            (Formula::Or(l, r), 2) => Formula::Or(l.clone(), Box::new(Self::replace_at_growth_path(r, &path[1..], replacement))),
            (Formula::Implies(l, r), 1) => Formula::Implies(Box::new(Self::replace_at_growth_path(l, &path[1..], replacement)), r.clone()),
            (Formula::Implies(l, r), 2) => Formula::Implies(l.clone(), Box::new(Self::replace_at_growth_path(r, &path[1..], replacement))),
            (Formula::Biconditional(l, r), 1) => Formula::Biconditional(Box::new(Self::replace_at_growth_path(l, &path[1..], replacement)), r.clone()),
            (Formula::Biconditional(l, r), 2) => Formula::Biconditional(l.clone(), Box::new(Self::replace_at_growth_path(r, &path[1..], replacement))),
            _ => formula.clone(),
        }
    }

    /// Apply all substitutions from the map to a formula.
    fn substitute_all(&self, formula: &Formula, subs: &std::collections::HashMap<String, Formula>) -> Formula {
        match formula {
            Formula::Atom(name) => {
                subs.get(name).cloned().unwrap_or_else(|| formula.clone())
            }
            Formula::Not(inner) => {
                Formula::Not(Box::new(self.substitute_all(inner, subs)))
            }
            Formula::And(l, r) => {
                Formula::And(
                    Box::new(self.substitute_all(l, subs)),
                    Box::new(self.substitute_all(r, subs)),
                )
            }
            Formula::Or(l, r) => {
                Formula::Or(
                    Box::new(self.substitute_all(l, subs)),
                    Box::new(self.substitute_all(r, subs)),
                )
            }
            Formula::Implies(l, r) => {
                Formula::Implies(
                    Box::new(self.substitute_all(l, subs)),
                    Box::new(self.substitute_all(r, subs)),
                )
            }
            Formula::Biconditional(l, r) => {
                Formula::Biconditional(
                    Box::new(self.substitute_all(l, subs)),
                    Box::new(self.substitute_all(r, subs)),
                )
            }
            Formula::Contradiction => Formula::Contradiction,
        }
    }

    /// Wrap premises and conclusion as a single conditional tautology
    /// (P1 ∧ P2 ∧ ... ∧ Pn) ⊃ C
    fn wrap_as_conditional(&self, premises: &[Formula], conclusion: &Formula) -> Formula {
        if premises.is_empty() {
            // If no premises, the conclusion itself should be a tautology
            // But for consistency, wrap as T ⊃ C where T is the conclusion
            // Actually, just return the conclusion if it's already a tautology
            return conclusion.clone();
        }

        // Combine all premises with conjunction
        let antecedent = premises.iter()
            .cloned()
            .reduce(|acc, p| Formula::And(Box::new(acc), Box::new(p)))
            .unwrap_or_else(|| conclusion.clone());

        Formula::Implies(Box::new(antecedent), Box::new(conclusion.clone()))
    }

    /// Apply random equivalence transformations
    fn apply_transformations(&self, mut formula: Formula, rng: &mut impl Rng) -> Formula {
        // Force gnarly transformation combos when enabled
        if self.config.gnarly_combos {
            formula = self.apply_gnarly_combos(formula, rng);
        }

        let mut successful_transforms = 0;
        let mut attempts = 0;
        let max_attempts = self.config.transform_count * 10;

        while successful_transforms < self.config.transform_count && attempts < max_attempts {
            attempts += 1;
            if let Some(transformed) = self.try_apply_random_equivalence(&formula, rng) {
                formula = transformed;
                successful_transforms += 1;
            }
        }

        // Simplification pass: collapse excessive negations (~~~~P → P)
        simplify_negations(formula)
    }

    /// Apply gnarly transformation combos that create especially difficult proofs.
    /// These force specific hard patterns like:
    /// - Contraposition + De Morgan chains
    /// - Material Implication + Distribution (creates case splits)
    /// - Exportation + double negation
    fn apply_gnarly_combos(&self, mut formula: Formula, rng: &mut impl Rng) -> Formula {
        // Pick 1-3 gnarly combos based on difficulty
        let combo_count = if self.config.difficulty_value >= 96 { 3 } else { 2 };

        let gnarly_rules = [
            // Combo 1: Contraposition + De Morgan chain
            vec![EquivalenceRule::Contraposition, EquivalenceRule::DeMorgan],
            // Combo 2: Implication + Distribution (creates case splits)
            vec![EquivalenceRule::Implication, EquivalenceRule::Distribution],
            // Combo 3: Exportation + Double Negation
            vec![EquivalenceRule::Exportation, EquivalenceRule::DoubleNegation],
            // Combo 4: Equivalence + De Morgan
            vec![EquivalenceRule::Equivalence, EquivalenceRule::DeMorgan],
        ];

        // Shuffle and pick combos
        let mut indices: Vec<usize> = (0..gnarly_rules.len()).collect();
        for i in (1..indices.len()).rev() {
            let j = rng.gen_range(0..=i);
            indices.swap(i, j);
        }

        for i in 0..combo_count.min(indices.len()) {
            let combo = &gnarly_rules[indices[i]];
            for rule in combo {
                if let Some(transformed) = self.try_apply_specific_rule(&formula, *rule, rng) {
                    formula = transformed;
                }
            }
        }

        formula
    }

    /// Check tautology using the appropriate engine based on atom count.
    fn check_tautology(&self, formula: &Formula) -> bool {
        let atoms = formula.atoms();
        let standard = ["P", "Q", "R", "S", "T"];
        if atoms.len() <= 5 && atoms.iter().all(|a| standard.contains(&a.as_str())) {
            is_tautology(formula)
        } else {
            is_tautology_dynamic(formula)
        }
    }

    /// Try to apply a specific equivalence rule to some subformula (positional)
    fn try_apply_specific_rule(&self, formula: &Formula, rule: EquivalenceRule, rng: &mut impl Rng) -> Option<Formula> {
        let subformulas = formula.subformulas_with_paths();
        if subformulas.is_empty() {
            return None;
        }

        // Shuffle subformulas
        let mut indices: Vec<usize> = (0..subformulas.len()).collect();
        for i in (1..indices.len()).rev() {
            let j = rng.gen_range(0..=i);
            indices.swap(i, j);
        }

        for &idx in &indices {
            let (path, subformula) = &subformulas[idx];
            let equivalents = rule.equivalent_forms(subformula);

            if !equivalents.is_empty() {
                let equivalent = &equivalents[rng.gen_range(0..equivalents.len())];
                let result = formula.replace_at_path(path, equivalent);

                if self.check_tautology(&result) {
                    return Some(result);
                }
            }
        }

        None
    }

    /// Try to apply a random equivalence transformation to a single subformula (positional).
    /// Uses path-based replacement so only the selected occurrence is transformed,
    /// allowing structurally identical subtrees to diverge across passes.
    fn try_apply_random_equivalence(&self, formula: &Formula, rng: &mut impl Rng) -> Option<Formula> {
        // Get all subformulas with positional paths
        let subformulas = formula.subformulas_with_paths();
        if subformulas.is_empty() {
            return None;
        }

        // Shuffle the subformulas to try in random order
        let mut indices: Vec<usize> = (0..subformulas.len()).collect();
        for i in (1..indices.len()).rev() {
            let j = rng.gen_range(0..=i);
            indices.swap(i, j);
        }

        // For each subformula, try to find an applicable rule
        for &idx in &indices {
            let (path, subformula) = &subformulas[idx];

            // Get all applicable rules for this subformula
            let applicable = self.find_applicable_rules(subformula);
            if applicable.is_empty() {
                continue;
            }

            // Weighted selection - de-weight size-exploding rules
            // Distribution and Equivalence duplicate entire subtrees, causing exponential growth
            let weights: Vec<f64> = applicable.iter().map(|(rule, _)| {
                match rule {
                    EquivalenceRule::Distribution | EquivalenceRule::Equivalence => 0.2,
                    _ => 1.0,
                }
            }).collect();

            let total_weight: f64 = weights.iter().sum();
            let mut roll = rng.gen::<f64>() * total_weight;
            let mut chosen_idx = 0;
            for (i, &w) in weights.iter().enumerate() {
                roll -= w;
                if roll <= 0.0 {
                    chosen_idx = i;
                    break;
                }
            }

            let (_rule, equivalent) = &applicable[chosen_idx];

            // Apply the transformation at this specific position only
            let result = formula.replace_at_path(path, equivalent);

            // Sanity check: the result should still be a tautology
            if self.check_tautology(&result) {
                return Some(result);
            }
            // If not (shouldn't happen), try another
        }

        None
    }

    /// Find all rules that can be applied to this formula, with their results
    fn find_applicable_rules(&self, formula: &Formula) -> Vec<(EquivalenceRule, Formula)> {
        let mut results = Vec::new();

        for rule in EquivalenceRule::all() {
            // Skip Tautology rule as it can cause infinite growth
            if matches!(rule, EquivalenceRule::Tautology) {
                // Only allow Tautology contraction, not expansion
                if let Formula::And(p, q) = formula {
                    if p == q {
                        results.push((rule, p.as_ref().clone()));
                    }
                }
                if let Formula::Or(p, q) = formula {
                    if p == q {
                        results.push((rule, p.as_ref().clone()));
                    }
                }
                continue;
            }

            // Skip Double Negation introduction if formula already has 2+ leading negations
            if matches!(rule, EquivalenceRule::DoubleNegation) {
                if count_leading_negations(formula) >= 2 {
                    // Only allow DN elimination (~~P → P), not introduction (P → ~~P)
                    if let Formula::Not(inner) = formula {
                        if let Formula::Not(inner2) = inner.as_ref() {
                            results.push((rule, inner2.as_ref().clone()));
                        }
                    }
                    continue;
                }
            }

            let equivalents = rule.equivalent_forms(formula);
            for equiv in equivalents {
                results.push((rule, equiv));
            }
        }

        results
    }
}

/// Count leading negations in a formula (e.g., ~~~P has 3)
fn count_leading_negations(formula: &Formula) -> usize {
    match formula {
        Formula::Not(inner) => 1 + count_leading_negations(inner),
        _ => 0,
    }
}

/// Simplify excessive negations throughout a formula
/// Collapses ~~~~P → ~~P → P (removes pairs of negations)
fn simplify_negations(formula: Formula) -> Formula {
    match formula {
        Formula::Not(inner) => {
            let simplified_inner = simplify_negations(*inner);
            // Check if inner is also a negation - if so, eliminate both
            if let Formula::Not(inner2) = simplified_inner {
                // ~~X → X (after X is simplified)
                simplify_negations(*inner2)
            } else {
                Formula::Not(Box::new(simplified_inner))
            }
        }
        Formula::And(left, right) => Formula::And(
            Box::new(simplify_negations(*left)),
            Box::new(simplify_negations(*right)),
        ),
        Formula::Or(left, right) => Formula::Or(
            Box::new(simplify_negations(*left)),
            Box::new(simplify_negations(*right)),
        ),
        Formula::Implies(left, right) => Formula::Implies(
            Box::new(simplify_negations(*left)),
            Box::new(simplify_negations(*right)),
        ),
        Formula::Biconditional(left, right) => Formula::Biconditional(
            Box::new(simplify_negations(*left)),
            Box::new(simplify_negations(*right)),
        ),
        // Atoms and Contradiction pass through unchanged
        other => other,
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::services::truth_table::{is_tautology, are_equivalent};

    #[test]
    fn test_config_easy() {
        let config = ObfuscateConfig::for_difficulty_value(10);
        assert_eq!(config.difficulty, Difficulty::Easy);
        assert!(config.transform_count <= 3, "Easy should have 1-3 transforms, got {}", config.transform_count);
        assert_eq!(config.atom_pool.len(), 2);
    }

    #[test]
    fn test_config_expert() {
        let config = ObfuscateConfig::for_difficulty_value(80);
        assert_eq!(config.difficulty, Difficulty::Expert);
        assert!(config.transform_count >= 11, "Expert should have 11+ transforms, got {}", config.transform_count);
        assert!(config.atom_pool.len() >= 4, "Expert (80) should have 4 atoms");
    }

    #[test]
    fn test_config_nightmare() {
        let config = ObfuscateConfig::for_difficulty_value(90);
        assert_eq!(config.difficulty, Difficulty::Expert); // Still maps to Expert preset
        assert!(config.transform_count >= 16, "Nightmare should have 16+ transforms, got {}", config.transform_count);
        assert_eq!(config.atom_pool.len(), 5, "Nightmare (90) should have 5 atoms");
    }

    #[test]
    fn test_config_marathon() {
        let config = ObfuscateConfig::for_difficulty_value(98);
        assert_eq!(config.difficulty, Difficulty::Expert); // Still maps to Expert preset
        assert!(config.transform_count >= 20, "Marathon should have 20+ transforms, got {}", config.transform_count);
        assert_eq!(config.atom_pool.len(), 5, "Marathon should have 5 atoms");
    }

    #[test]
    fn test_difficulty_scaling_progression() {
        // Verify transform counts increase with difficulty
        let configs: Vec<_> = [10, 30, 50, 75, 90, 98]
            .iter()
            .map(|&d| (d, ObfuscateConfig::for_difficulty_value(d)))
            .collect();

        for window in configs.windows(2) {
            let (d1, c1) = &window[0];
            let (d2, c2) = &window[1];
            assert!(
                c2.transform_count >= c1.transform_count,
                "Transforms should increase: d={} has {}, d={} has {}",
                d1, c1.transform_count, d2, c2.transform_count
            );
        }
    }

    #[test]
    fn test_wrap_as_conditional() {
        let config = ObfuscateConfig::for_difficulty_value(50);
        let gen = ObfuscateGenerator::new(config);

        let p = Formula::Atom("P".to_string());
        let q = Formula::Atom("Q".to_string());

        // P, P→Q ⊢ Q becomes (P ∧ (P→Q)) → Q
        let premises = vec![
            p.clone(),
            Formula::Implies(Box::new(p.clone()), Box::new(q.clone())),
        ];
        let wrapped = gen.wrap_as_conditional(&premises, &q);

        // The wrapped formula should be a tautology
        assert!(is_tautology(&wrapped));
    }

    #[test]
    fn test_generate_produces_tautology() {
        let config = ObfuscateConfig::for_difficulty_value(30);
        let gen = ObfuscateGenerator::new(config);
        let mut rng = rand::thread_rng();

        // Generate multiple theorems and verify they're all tautologies
        for _ in 0..10 {
            let theorem = gen.generate(&mut rng);
            assert!(theorem.premises.is_empty(), "Should be a tautology with no premises");
            assert!(is_tautology(&theorem.conclusion), "Conclusion should be a tautology");
        }
    }

    #[test]
    fn test_transformations_preserve_validity() {
        let config = ObfuscateConfig::for_difficulty_value(50);
        let gen = ObfuscateGenerator::new(config);
        let mut rng = rand::thread_rng();

        // Test with a simple known tautology
        let p = Formula::Atom("P".to_string());
        let q = Formula::Atom("Q".to_string());

        // MP wrapped: (P ∧ (P→Q)) → Q
        let original = Formula::Implies(
            Box::new(Formula::And(
                Box::new(p.clone()),
                Box::new(Formula::Implies(Box::new(p.clone()), Box::new(q.clone()))),
            )),
            Box::new(q.clone()),
        );

        assert!(is_tautology(&original));

        let transformed = gen.apply_transformations(original.clone(), &mut rng);
        assert!(is_tautology(&transformed));
        assert!(are_equivalent(&original, &transformed));
    }

    #[test]
    fn test_base_forms_produce_valid_theorems() {
        let config = ObfuscateConfig::for_difficulty_value(50);
        let gen = ObfuscateGenerator::new(config);
        let mut rng = rand::thread_rng();

        for _ in 0..20 {
            let (premises, conclusion) = gen.generate_base_theorem(&mut rng);
            let wrapped = gen.wrap_as_conditional(&premises, &conclusion);
            assert!(is_tautology(&wrapped), "Base theorem should wrap to tautology");
        }
    }

    #[test]
    fn test_difficulty_scaling() {
        let mut rng = rand::thread_rng();

        // Easy should have simpler formulas
        let easy_config = ObfuscateConfig::for_difficulty_value(10);
        let easy_gen = ObfuscateGenerator::new(easy_config);
        let easy_theorem = easy_gen.generate(&mut rng);

        // Expert should have more complex formulas
        let expert_config = ObfuscateConfig::for_difficulty_value(90);
        let expert_gen = ObfuscateGenerator::new(expert_config);
        let expert_theorem = expert_gen.generate(&mut rng);

        // Both should be valid tautologies
        assert!(is_tautology(&easy_theorem.conclusion));
        assert!(is_tautology(&expert_theorem.conclusion));

        // Expert should generally be deeper/more complex
        // (not always guaranteed due to randomness, but usually true)
    }

    #[test]
    fn test_simplify_negations() {
        let p = Formula::Atom("P".to_string());

        // ~~P → P
        let double_neg = Formula::Not(Box::new(Formula::Not(Box::new(p.clone()))));
        let simplified = super::simplify_negations(double_neg);
        assert_eq!(simplified, p);

        // ~~~~P → P
        let quad_neg = Formula::Not(Box::new(Formula::Not(Box::new(
            Formula::Not(Box::new(Formula::Not(Box::new(p.clone()))))
        ))));
        let simplified = super::simplify_negations(quad_neg);
        assert_eq!(simplified, p);

        // ~~~P → ~P
        let triple_neg = Formula::Not(Box::new(Formula::Not(Box::new(
            Formula::Not(Box::new(p.clone()))
        ))));
        let simplified = super::simplify_negations(triple_neg);
        assert_eq!(simplified, Formula::Not(Box::new(p.clone())));

        // Nested: ~~(P ∧ ~~Q) → (P ∧ Q)
        let q = Formula::Atom("Q".to_string());
        let nested = Formula::Not(Box::new(Formula::Not(Box::new(
            Formula::And(
                Box::new(p.clone()),
                Box::new(Formula::Not(Box::new(Formula::Not(Box::new(q.clone())))))
            )
        ))));
        let simplified = super::simplify_negations(nested);
        assert_eq!(simplified, Formula::And(Box::new(p), Box::new(q)));
    }

    #[test]
    fn test_count_leading_negations() {
        let p = Formula::Atom("P".to_string());
        assert_eq!(super::count_leading_negations(&p), 0);

        let neg_p = Formula::Not(Box::new(p.clone()));
        assert_eq!(super::count_leading_negations(&neg_p), 1);

        let double_neg = Formula::Not(Box::new(Formula::Not(Box::new(p.clone()))));
        assert_eq!(super::count_leading_negations(&double_neg), 2);

        let triple_neg = Formula::Not(Box::new(Formula::Not(Box::new(
            Formula::Not(Box::new(p.clone()))
        ))));
        assert_eq!(super::count_leading_negations(&triple_neg), 3);
    }

    #[test]
    fn test_substitution_config_scaling() {
        // Low difficulty: no substitution
        let low_config = ObfuscateConfig::for_difficulty_value(50);
        assert_eq!(low_config.substitution_depth, 0, "Low difficulty should have no substitution");

        // Medium-high difficulty: simple substitution
        let mid_config = ObfuscateConfig::for_difficulty_value(75);
        assert_eq!(mid_config.substitution_depth, 1, "Difficulty 75 should have depth 1 substitution");

        // High difficulty: complex substitution
        let high_config = ObfuscateConfig::for_difficulty_value(90);
        assert_eq!(high_config.substitution_depth, 2, "High difficulty should have depth 2 substitution");
    }

    #[test]
    fn test_substitution_increases_complexity() {
        let mut rng = rand::thread_rng();

        // High difficulty: has substitution
        let high_config = ObfuscateConfig::for_difficulty_value(90);
        assert!(high_config.substitution_depth >= 1);

        // The legacy path has a small pool (5 atoms), so after the base form
        // uses 3-4, only 1-2 remain for substitutions. Guaranteed coverage
        // ensures every partition atom appears at least once.
        let gen = ObfuscateGenerator::new(high_config);
        let mut max_depth = 0;
        let mut max_atoms = 0;
        for _ in 0..10 {
            let theorem = gen.generate(&mut rng);
            assert!(is_tautology(&theorem.conclusion), "Generated formula should be a tautology");
            max_depth = max_depth.max(theorem.conclusion.depth());
            max_atoms = max_atoms.max(theorem.conclusion.atoms().len());
        }

        // Over 10 runs, at least one should achieve reasonable complexity
        assert!(max_depth >= 3, "At least one run should produce depth >= 3, got max {}", max_depth);
        assert!(max_atoms >= 2, "At least one run should produce 2+ atoms, got max {}", max_atoms);
    }

    #[test]
    fn test_substitution_preserves_validity() {
        let mut rng = rand::thread_rng();

        // Test multiple times for randomness
        for difficulty in [70, 80, 90, 100] {
            let config = ObfuscateConfig::for_difficulty_value(difficulty);
            let gen = ObfuscateGenerator::new(config);

            for _ in 0..5 {
                let theorem = gen.generate(&mut rng);
                assert!(
                    is_tautology(&theorem.conclusion),
                    "Difficulty {} should produce tautology, got: {}",
                    difficulty,
                    theorem.conclusion.display_string()
                );
            }
        }
    }

    #[test]
    fn test_random_formula_generation() {
        let config = ObfuscateConfig::for_difficulty_value(90);
        let gen = ObfuscateGenerator::new(config);
        let mut rng = rand::thread_rng();

        // Test with 2 atoms — all must appear (guaranteed coverage)
        let atoms2 = vec!["A".to_string(), "B".to_string()];
        for _ in 0..10 {
            let formula = gen.random_formula(&mut rng, 2, &atoms2);
            let formula_atoms = formula.atoms();

            for atom in formula_atoms.iter() {
                assert!(atoms2.contains(atom), "Formula atom {} not in provided atoms {:?}", atom, atoms2);
            }
            for atom in &atoms2 {
                assert!(formula_atoms.contains(atom), "Atom {} missing from formula. Got: {:?}", atom, formula_atoms);
            }
        }

        // Test with 4 atoms — all must appear
        let atoms4 = vec!["A".to_string(), "B".to_string(), "C".to_string(), "D".to_string()];
        for _ in 0..10 {
            let formula = gen.random_formula(&mut rng, 2, &atoms4);
            let formula_atoms = formula.atoms();
            for atom in &atoms4 {
                assert!(formula_atoms.contains(atom), "Atom {} missing from 4-atom formula. Got: {:?}", atom, formula_atoms);
            }
        }

        // Single atom edge case
        let atoms1 = vec!["Z".to_string()];
        let formula = gen.random_formula(&mut rng, 2, &atoms1);
        assert!(formula.atoms().contains(&"Z".to_string()), "Single atom must appear");
    }

    // === DifficultySpec-based generation tests ===

    #[test]
    fn test_build_atom_pool() {
        assert_eq!(super::build_atom_pool(2), vec!["P", "Q"]);
        assert_eq!(super::build_atom_pool(5), vec!["P", "Q", "R", "S", "T"]);
        let pool8 = super::build_atom_pool(8);
        assert_eq!(pool8.len(), 8);
        assert_eq!(&pool8[0..5], &["P", "Q", "R", "S", "T"]);
        assert_eq!(&pool8[5..8], &["A", "B", "C"]);
    }

    #[test]
    fn test_generate_with_spec_easy() {
        use crate::models::theorem::{DifficultySpec, DifficultyTier};

        let spec = DifficultySpec::from_tier(DifficultyTier::Easy);
        let mut rng = rand::thread_rng();
        for _ in 0..5 {
            let theorem = ObfuscateGenerator::generate_with_spec(&spec, &mut rng);
            assert!(
                is_tautology_dynamic(&theorem.conclusion),
                "Easy spec should produce tautology"
            );
        }
    }

    #[test]
    fn test_generate_with_spec_hard() {
        use crate::models::theorem::{DifficultySpec, DifficultyTier};

        let spec = DifficultySpec::from_tier(DifficultyTier::Hard);
        let mut rng = rand::thread_rng();
        for _ in 0..3 {
            let theorem = ObfuscateGenerator::generate_with_spec(&spec, &mut rng);
            assert!(
                is_tautology_dynamic(&theorem.conclusion),
                "Hard spec should produce tautology"
            );
        }
    }

    #[test]
    fn test_generate_with_spec_expert() {
        use crate::models::theorem::{DifficultySpec, DifficultyTier};

        let spec = DifficultySpec::from_tier(DifficultyTier::Expert);
        let mut rng = rand::thread_rng();
        let theorem = ObfuscateGenerator::generate_with_spec(&spec, &mut rng);
        assert!(
            is_tautology_dynamic(&theorem.conclusion),
            "Expert spec should produce tautology"
        );
    }

    #[test]
    fn test_from_difficulty_value_bridge() {
        use crate::models::theorem::DifficultySpec;

        // Verify bridge produces valid specs
        for d in [10, 30, 50, 75, 90, 100] {
            let spec = DifficultySpec::from_difficulty_value(d);
            assert!(spec.variables >= 2 && spec.variables <= 5);
            assert!(spec.passes >= 1);
            assert!(spec.transforms_per_pass >= 1);
        }
    }

    #[test]
    fn test_mind_tier_uses_all_7_variables() {
        use crate::models::theorem::{DifficultySpec, DifficultyTier};

        let spec = DifficultySpec::from_tier(DifficultyTier::Mind);
        assert_eq!(spec.variables, 7);
        assert_eq!(spec.substitution_depth, 4);

        let mut rng = rand::thread_rng();
        let mut max_atoms = 0;

        // Run multiple times due to randomness
        for _ in 0..10 {
            let theorem = ObfuscateGenerator::generate_with_spec(&spec, &mut rng);
            assert!(
                is_tautology_dynamic(&theorem.conclusion),
                "Mind spec should produce tautology"
            );
            let atom_count = theorem.conclusion.atoms().len();
            max_atoms = max_atoms.max(atom_count);
        }

        // Mind tier has 7 variables. The base form uses 3-4 atoms, and
        // substitution should incorporate the remaining atoms while preserving
        // the original ones. We should see at least 5 distinct atoms.
        assert!(
            max_atoms >= 5,
            "Mind tier should use at least 5 of 7 atoms, but max was {}",
            max_atoms
        );
    }

    #[test]
    fn test_cosmic_tier_uses_many_variables() {
        use crate::models::theorem::{DifficultySpec, DifficultyTier};

        let spec = DifficultySpec::from_tier(DifficultyTier::Cosmic);
        assert_eq!(spec.variables, 7);

        let mut rng = rand::thread_rng();
        let mut max_atoms = 0;

        for _ in 0..10 {
            let theorem = ObfuscateGenerator::generate_with_spec(&spec, &mut rng);
            assert!(
                is_tautology_dynamic(&theorem.conclusion),
                "Cosmic spec should produce tautology"
            );
            max_atoms = max_atoms.max(theorem.conclusion.atoms().len());
        }

        assert!(
            max_atoms >= 5,
            "Cosmic tier should use at least 5 of 7 atoms, but max was {}",
            max_atoms
        );
    }

    #[test]
    fn test_substitution_preserves_base_atoms() {
        // Verify that after substitution, the base atoms are still present
        // (not replaced entirely by new atoms).
        let config = ObfuscateConfig::from_spec(&DifficultySpec {
            variables: 7,
            passes: 1,
            transforms_per_pass: 2,
            base_complexity: BaseComplexity::Complex,
            substitution_depth: 2,
            max_formula_nodes: None,
            max_formula_depth: None,
            bridge_atoms: None,
            gnarly_combos: None,
        });
        let gen = ObfuscateGenerator::new(config);
        let mut rng = rand::thread_rng();

        for _ in 0..10 {
            let (premises, conclusion) = gen.generate_base_theorem_with_complexity(&mut rng, true);

            // Collect base atoms
            let mut base_atoms = std::collections::HashSet::new();
            for p in &premises {
                base_atoms.extend(p.atoms());
            }
            base_atoms.extend(conclusion.atoms());

            // Apply substitutions
            let (new_premises, new_conclusion) = gen.apply_substitutions(premises, conclusion, &mut rng);

            // Collect atoms after substitution
            let mut result_atoms = std::collections::HashSet::new();
            for p in &new_premises {
                result_atoms.extend(p.atoms());
            }
            result_atoms.extend(new_conclusion.atoms());

            // The original base atoms should still be present
            for base_atom in &base_atoms {
                assert!(
                    result_atoms.contains(base_atom),
                    "Base atom '{}' missing after substitution. Base: {:?}, Result: {:?}",
                    base_atom, base_atoms, result_atoms
                );
            }

            // We should have more atoms than the base (substitution added new ones)
            assert!(
                result_atoms.len() > base_atoms.len(),
                "Substitution should add new atoms. Base: {:?}, Result: {:?}",
                base_atoms, result_atoms
            );
        }
    }

    #[test]
    fn test_bridge_atoms_create_cross_zone_atoms() {
        use crate::models::theorem::{DifficultySpec, BaseComplexity};

        let spec = DifficultySpec {
            variables: 7,
            passes: 1,
            transforms_per_pass: 2,
            base_complexity: BaseComplexity::Complex,
            substitution_depth: 2,
            max_formula_nodes: None,
            max_formula_depth: None,
            bridge_atoms: Some(2),
            gnarly_combos: None,
        };

        let config = ObfuscateConfig::from_spec(&spec);
        assert_eq!(config.bridge_atoms, 2);

        let mut rng = rand::thread_rng();
        // Generate several theorems and verify they're all valid tautologies
        for _ in 0..10 {
            let theorem = ObfuscateGenerator::generate_with_spec(&spec, &mut rng);
            assert!(
                is_tautology_dynamic(&theorem.conclusion),
                "Bridge atoms should not break tautology preservation"
            );
        }
    }

    #[test]
    fn test_bridge_atoms_zero_matches_no_bridge() {
        use crate::models::theorem::{DifficultySpec, BaseComplexity};

        let spec = DifficultySpec {
            variables: 5,
            passes: 1,
            transforms_per_pass: 5,
            base_complexity: BaseComplexity::Simple,
            substitution_depth: 1,
            max_formula_nodes: None,
            max_formula_depth: None,
            bridge_atoms: Some(0),
            gnarly_combos: None,
        };

        let mut rng = rand::thread_rng();
        for _ in 0..5 {
            let theorem = ObfuscateGenerator::generate_with_spec(&spec, &mut rng);
            assert!(
                is_tautology_dynamic(&theorem.conclusion),
                "Zero bridge atoms should work identically to no bridges"
            );
        }
    }

    #[test]
    fn test_tier_bridge_atom_defaults() {
        use crate::models::theorem::{DifficultySpec, DifficultyTier};

        assert_eq!(DifficultySpec::from_tier(DifficultyTier::Easy).bridge_atoms, Some(0));
        assert_eq!(DifficultySpec::from_tier(DifficultyTier::Expert).bridge_atoms, Some(0));
        assert_eq!(DifficultySpec::from_tier(DifficultyTier::Nightmare).bridge_atoms, Some(1));
        assert_eq!(DifficultySpec::from_tier(DifficultyTier::Marathon).bridge_atoms, Some(1));
        assert_eq!(DifficultySpec::from_tier(DifficultyTier::Cosmic).bridge_atoms, Some(2));
        assert_eq!(DifficultySpec::from_tier(DifficultyTier::Mind).bridge_atoms, Some(2));
    }
}
