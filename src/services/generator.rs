use rand::Rng;
use crate::models::{
    Formula, Theorem,
    theorem::{Difficulty, Theme},
};
use super::tree_gen::{ProofTreeGenerator, TreeGenConfig};
use super::proof_tree::ProofTree;
use super::obfuscate_gen::{ObfuscateConfig, ObfuscateGenerator};

/// Configuration for theorem generation (legacy - kept for compatibility)
#[derive(Debug, Clone)]
pub struct GeneratorConfig {
    pub max_premises: usize,
    pub max_depth: usize,
    pub atom_pool: Vec<String>,
    pub allow_biconditional: bool,
    pub allow_nested_negation: bool,
}

impl Default for GeneratorConfig {
    fn default() -> Self {
        Self {
            max_premises: 3,
            max_depth: 3,
            atom_pool: vec![
                "P".to_string(),
                "Q".to_string(),
                "R".to_string(),
                "S".to_string(),
            ],
            allow_biconditional: true,
            allow_nested_negation: true,
        }
    }
}

impl GeneratorConfig {
    pub fn for_difficulty(difficulty: Difficulty) -> Self {
        match difficulty {
            Difficulty::Easy => Self {
                max_premises: 2,
                max_depth: 2,
                atom_pool: vec!["P".to_string(), "Q".to_string()],
                allow_biconditional: false,
                allow_nested_negation: false,
            },
            Difficulty::Medium => Self {
                max_premises: 3,
                max_depth: 3,
                atom_pool: vec!["P".to_string(), "Q".to_string(), "R".to_string()],
                allow_biconditional: false,
                allow_nested_negation: true,
            },
            Difficulty::Hard => Self {
                max_premises: 3,
                max_depth: 4,
                atom_pool: vec![
                    "P".to_string(),
                    "Q".to_string(),
                    "R".to_string(),
                    "S".to_string(),
                ],
                allow_biconditional: true,
                allow_nested_negation: true,
            },
            Difficulty::Expert => Self {
                max_premises: 4,
                max_depth: 5,
                atom_pool: vec![
                    "P".to_string(),
                    "Q".to_string(),
                    "R".to_string(),
                    "S".to_string(),
                    "T".to_string(),
                ],
                allow_biconditional: true,
                allow_nested_negation: true,
            },
        }
    }
}

use serde::{Deserialize, Serialize};

/// Result of tree-based theorem generation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GeneratedTheorem {
    pub theorem: Theorem,
    pub proof_tree: ProofTree,
}

/// Generates provable theorems
pub struct TheoremGenerator {
    config: GeneratorConfig,
}

impl TheoremGenerator {
    pub fn new(config: GeneratorConfig) -> Self {
        Self { config }
    }

    pub fn with_difficulty(difficulty: Difficulty) -> Self {
        Self::new(GeneratorConfig::for_difficulty(difficulty))
    }

    /// Create generator with a specific difficulty value (1-100)
    pub fn with_difficulty_value(value: u8) -> Self {
        let difficulty = Self::preset_for_value(value);
        Self::new(GeneratorConfig::for_difficulty(difficulty))
    }

    /// Get a random difficulty value within a preset's range
    fn random_difficulty_value(preset: Difficulty) -> u8 {
        let mut rng = rand::thread_rng();
        match preset {
            Difficulty::Easy => rng.gen_range(1..=25),
            Difficulty::Medium => rng.gen_range(26..=45),
            Difficulty::Hard => rng.gen_range(46..=70),
            Difficulty::Expert => rng.gen_range(71..=100),
        }
    }

    /// Map a difficulty value (1-100) to a preset
    fn preset_for_value(value: u8) -> Difficulty {
        match value {
            1..=25 => Difficulty::Easy,
            26..=45 => Difficulty::Medium,
            46..=70 => Difficulty::Hard,
            _ => Difficulty::Expert,
        }
    }

    /// Generate a theorem with a specific difficulty value (1-100)
    pub fn generate_with_value(&self, difficulty_value: u8) -> Theorem {
        let mut rng = rand::thread_rng();
        let difficulty = Self::preset_for_value(difficulty_value);
        match difficulty {
            Difficulty::Easy => self.generate_legacy(difficulty, difficulty_value),
            _ => self.generate_from_obfuscation(difficulty_value, &mut rng),
        }
    }

    /// Generate a random provable theorem using the new proof-tree approach
    /// This generates theorems with guaranteed structural complexity
    pub fn generate(&self, difficulty: Difficulty) -> Theorem {
        // Use obfuscation for Medium, Hard, Expert (tautologies via equivalence transforms)
        // Keep legacy for Easy to ensure simple, predictable theorems
        let mut rng = rand::thread_rng();
        let difficulty_value = Self::random_difficulty_value(difficulty);
        match difficulty {
            Difficulty::Easy => self.generate_legacy(difficulty, difficulty_value),
            _ => self.generate_from_obfuscation(difficulty_value, &mut rng),
        }
    }

    /// Generate theorem using the new proof-tree compositional approach
    /// Returns both the theorem and the proof tree (solution)
    pub fn generate_with_proof(&self, difficulty: Difficulty) -> GeneratedTheorem {
        let difficulty_value = Self::random_difficulty_value(difficulty);
        self.generate_with_proof_and_value(difficulty, difficulty_value)
    }

    /// Generate theorem with a specific difficulty value
    fn generate_with_proof_and_value(&self, difficulty: Difficulty, difficulty_value: u8) -> GeneratedTheorem {
        let config = TreeGenConfig::for_difficulty_value(difficulty_value);
        let mut tree_gen = ProofTreeGenerator::new(config);
        let proof_tree = tree_gen.generate();

        let premises = proof_tree.premises();
        let conclusion = proof_tree.conclusion().clone();

        // Determine theme based on proof structure
        let theme = self.infer_theme_from_tree(&proof_tree);

        let theorem = Theorem::with_difficulty_value(
            premises,
            conclusion,
            difficulty,
            difficulty_value,
            Some(theme),
            None,
        );

        GeneratedTheorem { theorem, proof_tree }
    }

    /// Generate theorem from proof tree (without returning the tree)
    fn generate_from_tree(&self, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        self.generate_with_proof_and_value(difficulty, difficulty_value).theorem
    }

    /// Generate theorem using equivalence obfuscation
    /// Creates a tautology by wrapping a valid argument and applying random equivalence transforms
    fn generate_from_obfuscation(&self, difficulty_value: u8, rng: &mut impl Rng) -> Theorem {
        let config = ObfuscateConfig::for_difficulty_value(difficulty_value);
        let gen = ObfuscateGenerator::new(config);
        gen.generate(rng)
    }

    /// Infer the theme from a proof tree based on the root rule
    fn infer_theme_from_tree(&self, tree: &ProofTree) -> Theme {
        match tree.root.rule_name() {
            Some("CP") => Theme::ConditionalProof,
            Some("IP") => Theme::IndirectProof,
            Some("NegIntro") => Theme::IndirectProof,
            Some("CaseSplit") => Theme::Mixed,
            Some("MP") => Theme::ModusPonens,
            Some("MT") => Theme::ModusTollens,
            Some("HS") => Theme::HypotheticalSyllogism,
            Some("DS") => Theme::DisjunctiveSyllogism,
            Some("CD") => Theme::ConstructiveDilemma,
            Some("Conj") => Theme::Conjunction,
            Some("Add") | Some("Simp") => Theme::Disjunction,
            _ => Theme::Mixed,
        }
    }

    /// Legacy generation method (template-based)
    fn generate_legacy(&self, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        let mut rng = rand::thread_rng();

        // Choose a generation strategy based on difficulty
        let theme = self.choose_theme(&mut rng, difficulty);

        match theme {
            Theme::ModusPonens => self.generate_mp_style(&mut rng, difficulty, difficulty_value),
            Theme::ModusTollens => self.generate_mt_style(&mut rng, difficulty, difficulty_value),
            Theme::HypotheticalSyllogism => self.generate_hs_style(&mut rng, difficulty, difficulty_value),
            Theme::DisjunctiveSyllogism => self.generate_ds_style(&mut rng, difficulty, difficulty_value),
            Theme::Conjunction => self.generate_conj_style(&mut rng, difficulty, difficulty_value),
            Theme::ConditionalProof => self.generate_cp_style(&mut rng, difficulty, difficulty_value),
            Theme::IndirectProof => self.generate_ip_style(&mut rng, difficulty, difficulty_value),
            _ => self.generate_mixed_style(&mut rng, difficulty, difficulty_value),
        }
    }

    fn choose_theme(&self, rng: &mut impl Rng, difficulty: Difficulty) -> Theme {
        let themes: Vec<Theme> = match difficulty {
            Difficulty::Easy => vec![
                Theme::ModusPonens,
                Theme::ModusTollens,
                Theme::DisjunctiveSyllogism,
                Theme::Conjunction,
            ],
            Difficulty::Medium => vec![
                Theme::ModusPonens,
                Theme::ModusTollens,
                Theme::HypotheticalSyllogism,
                Theme::DisjunctiveSyllogism,
                Theme::ConditionalProof,
            ],
            Difficulty::Hard => vec![
                Theme::HypotheticalSyllogism,
                Theme::ConditionalProof,
                Theme::IndirectProof,
                Theme::Equivalence,
            ],
            Difficulty::Expert => vec![
                Theme::ConditionalProof,
                Theme::IndirectProof,
                Theme::Mixed,
            ],
        };

        themes[rng.gen_range(0..themes.len())]
    }

    fn random_atom(&self, rng: &mut impl Rng) -> Formula {
        let idx = rng.gen_range(0..self.config.atom_pool.len());
        Formula::Atom(self.config.atom_pool[idx].clone())
    }

    fn random_formula(&self, rng: &mut impl Rng, max_depth: usize) -> Formula {
        if max_depth == 0 {
            return self.random_atom(rng);
        }

        let choice = rng.gen_range(0..100);
        match choice {
            0..=29 => self.random_atom(rng),
            30..=44 => Formula::Not(Box::new(self.random_formula(rng, max_depth - 1))),
            45..=59 => Formula::And(
                Box::new(self.random_formula(rng, max_depth - 1)),
                Box::new(self.random_formula(rng, max_depth - 1)),
            ),
            60..=74 => Formula::Or(
                Box::new(self.random_formula(rng, max_depth - 1)),
                Box::new(self.random_formula(rng, max_depth - 1)),
            ),
            75..=94 => Formula::Implies(
                Box::new(self.random_formula(rng, max_depth - 1)),
                Box::new(self.random_formula(rng, max_depth - 1)),
            ),
            _ => {
                if self.config.allow_biconditional {
                    Formula::Biconditional(
                        Box::new(self.random_formula(rng, max_depth - 1)),
                        Box::new(self.random_formula(rng, max_depth - 1)),
                    )
                } else {
                    Formula::Implies(
                        Box::new(self.random_formula(rng, max_depth - 1)),
                        Box::new(self.random_formula(rng, max_depth - 1)),
                    )
                }
            }
        }
    }

    fn generate_mp_style(&self, rng: &mut impl Rng, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        let p = self.random_atom(rng);
        let q = self.random_atom(rng);

        Theorem::with_difficulty_value(
            vec![
                Formula::Implies(Box::new(p.clone()), Box::new(q.clone())),
                p,
            ],
            q,
            difficulty,
            difficulty_value,
            Some(Theme::ModusPonens),
            None,
        )
    }

    fn generate_mt_style(&self, rng: &mut impl Rng, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        let p = self.random_atom(rng);
        let q = self.random_atom(rng);

        Theorem::with_difficulty_value(
            vec![
                Formula::Implies(Box::new(p.clone()), Box::new(q.clone())),
                Formula::Not(Box::new(q)),
            ],
            Formula::Not(Box::new(p)),
            difficulty,
            difficulty_value,
            Some(Theme::ModusTollens),
            None,
        )
    }

    fn generate_hs_style(&self, rng: &mut impl Rng, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        let p = self.random_atom(rng);
        let q = self.random_atom(rng);
        let r = self.random_atom(rng);

        Theorem::with_difficulty_value(
            vec![
                Formula::Implies(Box::new(p.clone()), Box::new(q.clone())),
                Formula::Implies(Box::new(q), Box::new(r.clone())),
            ],
            Formula::Implies(Box::new(p), Box::new(r)),
            difficulty,
            difficulty_value,
            Some(Theme::HypotheticalSyllogism),
            None,
        )
    }

    fn generate_ds_style(&self, rng: &mut impl Rng, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        let p = self.random_atom(rng);
        let q = self.random_atom(rng);

        Theorem::with_difficulty_value(
            vec![
                Formula::Or(Box::new(p.clone()), Box::new(q.clone())),
                Formula::Not(Box::new(p)),
            ],
            q,
            difficulty,
            difficulty_value,
            Some(Theme::DisjunctiveSyllogism),
            None,
        )
    }

    fn generate_conj_style(&self, rng: &mut impl Rng, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        let p = self.random_atom(rng);
        let q = self.random_atom(rng);

        // P, Q ⊢ P ∧ Q
        Theorem::with_difficulty_value(
            vec![p.clone(), q.clone()],
            Formula::And(Box::new(p), Box::new(q)),
            difficulty,
            difficulty_value,
            Some(Theme::Conjunction),
            None,
        )
    }

    fn generate_cp_style(&self, rng: &mut impl Rng, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        let p = self.random_atom(rng);
        let q = self.random_atom(rng);

        // P → Q ⊢ ¬Q → ¬P (contraposition via conditional proof)
        Theorem::with_difficulty_value(
            vec![Formula::Implies(Box::new(p.clone()), Box::new(q.clone()))],
            Formula::Implies(
                Box::new(Formula::Not(Box::new(q))),
                Box::new(Formula::Not(Box::new(p))),
            ),
            difficulty,
            difficulty_value,
            Some(Theme::ConditionalProof),
            None,
        )
    }

    fn generate_ip_style(&self, rng: &mut impl Rng, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        let p = self.random_atom(rng);

        // ⊢ P ∨ ¬P (law of excluded middle)
        Theorem::with_difficulty_value(
            vec![],
            Formula::Or(
                Box::new(p.clone()),
                Box::new(Formula::Not(Box::new(p))),
            ),
            difficulty,
            difficulty_value,
            Some(Theme::IndirectProof),
            None,
        )
    }

    fn generate_mixed_style(&self, rng: &mut impl Rng, difficulty: Difficulty, difficulty_value: u8) -> Theorem {
        // Generate a random but solvable theorem
        let p = self.random_atom(rng);
        let q = self.random_atom(rng);
        let r = self.random_atom(rng);

        // (P → Q) ∧ (Q → R), P ⊢ R
        Theorem::with_difficulty_value(
            vec![
                Formula::And(
                    Box::new(Formula::Implies(Box::new(p.clone()), Box::new(q.clone()))),
                    Box::new(Formula::Implies(Box::new(q), Box::new(r.clone()))),
                ),
                p,
            ],
            r,
            difficulty,
            difficulty_value,
            Some(Theme::Mixed),
            None,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // === GeneratorConfig Construction Tests ===

    #[test]
    fn test_config_default_values() {
        let config = GeneratorConfig::default();

        assert_eq!(config.max_premises, 3);
        assert_eq!(config.max_depth, 3);
        assert_eq!(config.atom_pool.len(), 4);
        assert!(config.atom_pool.contains(&"P".to_string()));
        assert!(config.atom_pool.contains(&"Q".to_string()));
        assert!(config.allow_biconditional);
        assert!(config.allow_nested_negation);
    }

    #[test]
    fn test_config_for_easy_difficulty() {
        let config = GeneratorConfig::for_difficulty(Difficulty::Easy);

        assert_eq!(config.max_premises, 2);
        assert_eq!(config.max_depth, 2);
        assert_eq!(config.atom_pool.len(), 2);
        assert!(!config.allow_biconditional);
        assert!(!config.allow_nested_negation);
    }

    #[test]
    fn test_config_for_hard_difficulty() {
        let config = GeneratorConfig::for_difficulty(Difficulty::Hard);

        assert_eq!(config.max_premises, 3);
        assert_eq!(config.max_depth, 4);
        assert_eq!(config.atom_pool.len(), 4);
        assert!(config.allow_biconditional);
        assert!(config.allow_nested_negation);
    }

    // === Difficulty Value Boundary Tests ===

    #[test]
    fn test_difficulty_value_1_maps_to_easy() {
        let difficulty = TheoremGenerator::preset_for_value(1);
        assert_eq!(difficulty, Difficulty::Easy);
    }

    #[test]
    fn test_difficulty_value_25_maps_to_easy() {
        let difficulty = TheoremGenerator::preset_for_value(25);
        assert_eq!(difficulty, Difficulty::Easy);
    }

    #[test]
    fn test_difficulty_value_26_maps_to_medium() {
        let difficulty = TheoremGenerator::preset_for_value(26);
        assert_eq!(difficulty, Difficulty::Medium);
    }

    #[test]
    fn test_difficulty_value_46_maps_to_hard() {
        let difficulty = TheoremGenerator::preset_for_value(46);
        assert_eq!(difficulty, Difficulty::Hard);
    }

    #[test]
    fn test_difficulty_value_71_maps_to_expert() {
        let difficulty = TheoremGenerator::preset_for_value(71);
        assert_eq!(difficulty, Difficulty::Expert);
    }

    #[test]
    fn test_difficulty_value_100_maps_to_expert() {
        let difficulty = TheoremGenerator::preset_for_value(100);
        assert_eq!(difficulty, Difficulty::Expert);
    }

    // === Theorem Generation Property Tests ===

    #[test]
    fn test_generate_easy_produces_valid_theorem() {
        let generator = TheoremGenerator::with_difficulty(Difficulty::Easy);
        let theorem = generator.generate(Difficulty::Easy);

        // Easy theorems should have a theme
        assert!(theorem.theme.is_some());
        // Easy theorems should have a reasonable difficulty value
        assert!(theorem.difficulty_value <= 25);
    }

    #[test]
    fn test_generate_hard_produces_valid_theorem() {
        let generator = TheoremGenerator::with_difficulty(Difficulty::Hard);
        let theorem = generator.generate(Difficulty::Hard);

        // Hard theorems should have a theme
        assert!(theorem.theme.is_some());
        // Difficulty value should be in hard range
        assert!(theorem.difficulty_value >= 46 && theorem.difficulty_value <= 70);
    }

    #[test]
    fn test_generate_with_proof_returns_matching_tree() {
        let generator = TheoremGenerator::with_difficulty(Difficulty::Easy);
        let generated = generator.generate_with_proof(Difficulty::Easy);

        // The proof tree's conclusion should match the theorem's conclusion
        assert_eq!(generated.proof_tree.conclusion(), &generated.theorem.conclusion);

        // The proof tree's premises should match the theorem's premises
        let tree_premises = generated.proof_tree.premises();
        for premise in &generated.theorem.premises {
            assert!(tree_premises.contains(premise),
                "Theorem premise {:?} not found in proof tree premises {:?}",
                premise, tree_premises);
        }
    }

    #[test]
    fn test_generated_formula_respects_max_depth() {
        let generator = TheoremGenerator::with_difficulty(Difficulty::Easy);
        let config = GeneratorConfig::for_difficulty(Difficulty::Easy);

        // Generate several theorems and check conclusion depth
        for _ in 0..10 {
            let theorem = generator.generate(Difficulty::Easy);
            // Easy config has max_depth of 2
            // The conclusion depth should be reasonable (not excessively deep)
            let depth = theorem.conclusion.depth();
            // Allow some flexibility since generation is probabilistic
            assert!(depth <= config.max_depth + 2,
                "Conclusion depth {} exceeds expected max {}",
                depth, config.max_depth + 2);
        }
    }

    // === Original Tests ===

    #[test]
    fn test_generate_easy() {
        let generator = TheoremGenerator::with_difficulty(Difficulty::Easy);
        let theorem = generator.generate(Difficulty::Easy);

        assert!(!theorem.premises.is_empty() || theorem.theme == Some(Theme::IndirectProof));
    }

    #[test]
    fn test_generate_multiple() {
        let generator = TheoremGenerator::with_difficulty(Difficulty::Medium);

        for _ in 0..10 {
            let theorem = generator.generate(Difficulty::Medium);
            assert!(theorem.theme.is_some());
        }
    }
}
