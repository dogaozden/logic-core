use serde::{Deserialize, Serialize};
use uuid::Uuid;
use super::formula::Formula;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Difficulty {
    Easy,
    Medium,
    Hard,
    Expert,
}

// ─── DifficultySpec system (for extended generation) ─────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BaseComplexity {
    Simple,
    Complex,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DifficultySpec {
    pub variables: u8,              // 2-20
    pub passes: u16,                // 1-N
    pub transforms_per_pass: u16,   // per pass
    pub base_complexity: BaseComplexity,
    pub substitution_depth: u16,    // 0-N
    #[serde(default)]
    pub max_formula_nodes: Option<u32>,  // None = use default (20,000)
    #[serde(default)]
    pub max_formula_depth: Option<u32>,  // None = use default (100)
    #[serde(default)]
    pub bridge_atoms: Option<u8>,  // None = use default for tier, Some(n) = n bridge atoms
    /// Whether to force multi-rule transformation chains (Contraposition+DeMorgan, etc.).
    /// None = auto (derived from difficulty_value >= 85), Some(bool) = explicit override.
    #[serde(default)]
    pub gnarly_combos: Option<bool>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DifficultyTier {
    Baby,
    Easy,
    Medium,
    Hard,
    Expert,
    Nightmare,
    Marathon,
    Absurd,
    Cosmic,
    Mind,
}

impl DifficultySpec {
    pub fn from_tier(tier: DifficultyTier) -> Self {
        match tier {
            DifficultyTier::Baby      => Self { variables: 2, passes: 1,  transforms_per_pass: 2,  base_complexity: BaseComplexity::Simple,  substitution_depth: 0, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(0), gnarly_combos: Some(false) },
            DifficultyTier::Easy      => Self { variables: 2, passes: 1,  transforms_per_pass: 2,  base_complexity: BaseComplexity::Simple,  substitution_depth: 0, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(0), gnarly_combos: Some(false) },
            DifficultyTier::Medium    => Self { variables: 3, passes: 1,  transforms_per_pass: 5,  base_complexity: BaseComplexity::Simple,  substitution_depth: 0, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(0), gnarly_combos: Some(false) },
            DifficultyTier::Hard      => Self { variables: 4, passes: 1,  transforms_per_pass: 10, base_complexity: BaseComplexity::Complex, substitution_depth: 0, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(0), gnarly_combos: Some(false) },
            DifficultyTier::Expert    => Self { variables: 5, passes: 1,  transforms_per_pass: 15, base_complexity: BaseComplexity::Complex, substitution_depth: 2, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(0), gnarly_combos: Some(true) },
            DifficultyTier::Nightmare => Self { variables: 5, passes: 2,  transforms_per_pass: 12, base_complexity: BaseComplexity::Complex, substitution_depth: 3, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(1), gnarly_combos: Some(true) },
            DifficultyTier::Marathon  => Self { variables: 5, passes: 3,  transforms_per_pass: 15, base_complexity: BaseComplexity::Complex, substitution_depth: 4, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(1), gnarly_combos: Some(true) },
            DifficultyTier::Absurd    => Self { variables: 6, passes: 5,  transforms_per_pass: 20, base_complexity: BaseComplexity::Complex, substitution_depth: 4, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(1), gnarly_combos: Some(true) },
            DifficultyTier::Cosmic    => Self { variables: 7, passes: 10, transforms_per_pass: 20, base_complexity: BaseComplexity::Complex, substitution_depth: 4, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(2), gnarly_combos: Some(true) },
            DifficultyTier::Mind      => Self { variables: 7, passes: 20, transforms_per_pass: 24, base_complexity: BaseComplexity::Complex, substitution_depth: 4, max_formula_nodes: None, max_formula_depth: None, bridge_atoms: Some(2), gnarly_combos: Some(true) },
        }
    }

    /// Bridge from the legacy 1-100 difficulty value to a spec.
    pub fn from_difficulty_value(d: u8) -> Self {
        let d_clamped = d.clamp(1, 100) as usize;
        let variables = match d_clamped {
            1..=40 => 2,
            41..=60 => 3,
            61..=80 => 4,
            _ => 5,
        } as u8;
        let transforms_per_pass = match d_clamped {
            1..=25 => 1 + (d_clamped - 1) * 2 / 24,
            26..=45 => 3 + (d_clamped - 26) * 3 / 19,
            46..=70 => 6 + (d_clamped - 46) * 5 / 24,
            71..=85 => 11 + (d_clamped - 71) * 5 / 14,
            86..=95 => 16 + (d_clamped - 86) * 4 / 9,
            _ => 20 + (d_clamped - 96) * 4 / 4,
        } as u16;
        let substitution_depth = match d_clamped {
            1..=69 => 0,
            70..=84 => 1,
            _ => 2,
        };
        let base_complexity = if d_clamped >= 70 {
            BaseComplexity::Complex
        } else {
            BaseComplexity::Simple
        };
        Self {
            variables,
            passes: 1,
            transforms_per_pass,
            base_complexity,
            substitution_depth,
            max_formula_nodes: None,
            max_formula_depth: None,
            bridge_atoms: None,
            gnarly_combos: None,
        }
    }
}

impl DifficultyTier {
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "baby" => Some(Self::Baby),
            "easy" => Some(Self::Easy),
            "medium" => Some(Self::Medium),
            "hard" => Some(Self::Hard),
            "expert" => Some(Self::Expert),
            "nightmare" => Some(Self::Nightmare),
            "marathon" => Some(Self::Marathon),
            "absurd" => Some(Self::Absurd),
            "cosmic" => Some(Self::Cosmic),
            "mind" => Some(Self::Mind),
            _ => None,
        }
    }

    pub fn label(&self) -> &'static str {
        match self {
            Self::Baby => "Baby",
            Self::Easy => "Easy",
            Self::Medium => "Medium",
            Self::Hard => "Hard",
            Self::Expert => "Expert",
            Self::Nightmare => "Nightmare",
            Self::Marathon => "Marathon",
            Self::Absurd => "Absurd",
            Self::Cosmic => "Cosmic",
            Self::Mind => "Mind",
        }
    }

    /// Map a DifficultyTier to the legacy 4-level Difficulty for backward compatibility.
    pub fn to_legacy_difficulty(&self) -> Difficulty {
        match self {
            Self::Baby | Self::Easy => Difficulty::Easy,
            Self::Medium => Difficulty::Medium,
            Self::Hard => Difficulty::Hard,
            Self::Expert | Self::Nightmare | Self::Marathon
            | Self::Absurd | Self::Cosmic | Self::Mind => Difficulty::Expert,
        }
    }

    /// Return all tiers in order from easiest to hardest.
    pub fn all() -> &'static [DifficultyTier] {
        &[
            Self::Baby, Self::Easy, Self::Medium, Self::Hard, Self::Expert,
            Self::Nightmare, Self::Marathon, Self::Absurd, Self::Cosmic, Self::Mind,
        ]
    }
}

impl Difficulty {
    pub fn display_name(&self) -> &'static str {
        match self {
            Difficulty::Easy => "Easy",
            Difficulty::Medium => "Medium",
            Difficulty::Hard => "Hard",
            Difficulty::Expert => "Expert",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Theme {
    ModusPonens,
    ModusTollens,
    HypotheticalSyllogism,
    DisjunctiveSyllogism,
    ConstructiveDilemma,
    Conjunction,
    Disjunction,
    DoubleNegation,
    Biconditional,
    ConditionalProof,
    IndirectProof,
    Equivalence,
    Mixed,
}

impl Theme {
    pub fn display_name(&self) -> &'static str {
        match self {
            Theme::ModusPonens => "Modus Ponens",
            Theme::ModusTollens => "Modus Tollens",
            Theme::HypotheticalSyllogism => "Hypothetical Syllogism",
            Theme::DisjunctiveSyllogism => "Disjunctive Syllogism",
            Theme::ConstructiveDilemma => "Constructive Dilemma",
            Theme::Conjunction => "Conjunction",
            Theme::Disjunction => "Disjunction",
            Theme::DoubleNegation => "Double Negation",
            Theme::Biconditional => "Biconditional",
            Theme::ConditionalProof => "Conditional Proof",
            Theme::IndirectProof => "Indirect Proof",
            Theme::Equivalence => "Equivalence",
            Theme::Mixed => "Mixed",
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Theorem {
    pub id: String,
    pub premises: Vec<Formula>,
    pub conclusion: Formula,
    pub difficulty: Difficulty,
    /// The actual 1-100 difficulty value used to generate this theorem.
    /// For classic theorems, this is derived from the preset difficulty.
    #[serde(default = "default_difficulty_value")]
    pub difficulty_value: u8,
    /// The 10-level tier used to generate this theorem (Baby through Mind).
    /// None for legacy theorems generated before the tier system.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tier: Option<DifficultyTier>,
    pub theme: Option<Theme>,
    pub name: Option<String>,
    pub is_classic: bool,
}

/// Default difficulty value for backwards compatibility with serialized data
fn default_difficulty_value() -> u8 {
    50 // Mid-range default
}

impl Theorem {
    pub fn new(
        premises: Vec<Formula>,
        conclusion: Formula,
        difficulty: Difficulty,
        theme: Option<Theme>,
        name: Option<String>,
    ) -> Self {
        // Use midpoint of difficulty range as default
        let difficulty_value = Self::default_value_for_preset(difficulty);
        Self::with_difficulty_value(premises, conclusion, difficulty, difficulty_value, theme, name)
    }

    pub fn with_difficulty_value(
        premises: Vec<Formula>,
        conclusion: Formula,
        difficulty: Difficulty,
        difficulty_value: u8,
        theme: Option<Theme>,
        name: Option<String>,
    ) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            premises,
            conclusion,
            difficulty,
            difficulty_value,
            tier: None,
            theme,
            name,
            is_classic: false,
        }
    }

    /// Create a theorem generated from a DifficultyTier.
    pub fn from_tier(
        premises: Vec<Formula>,
        conclusion: Formula,
        tier: DifficultyTier,
        theme: Option<Theme>,
    ) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            premises,
            conclusion,
            difficulty: tier.to_legacy_difficulty(),
            difficulty_value: 100, // Tier-based generation uses spec, not legacy value
            tier: Some(tier),
            theme,
            name: None,
            is_classic: false,
        }
    }

    /// Get the midpoint difficulty value for a preset
    pub fn default_value_for_preset(difficulty: Difficulty) -> u8 {
        match difficulty {
            Difficulty::Easy => 13,     // midpoint of 1-25
            Difficulty::Medium => 35,   // midpoint of 26-45
            Difficulty::Hard => 58,     // midpoint of 46-70
            Difficulty::Expert => 85,   // midpoint of 71-100
        }
    }

    pub fn display_string(&self) -> String {
        if self.premises.is_empty() {
            format!("⊢ {}", self.conclusion.display_string())
        } else {
            let premises_str = self
                .premises
                .iter()
                .map(|p| p.display_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("{} ⊢ {}", premises_str, self.conclusion.display_string())
        }
    }
}

/// Classic theorems for training
pub fn get_classic_theorems() -> Vec<Theorem> {
    vec![
        // 1. Simple Modus Ponens
        Theorem {
            id: "classic-1".to_string(),
            premises: vec![
                Formula::parse("P -> Q").unwrap(),
                Formula::parse("P").unwrap(),
            ],
            conclusion: Formula::parse("Q").unwrap(),
            difficulty: Difficulty::Easy,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Easy),
            theme: Some(Theme::ModusPonens),
            name: Some("Modus Ponens".to_string()),
            tier: None,
            is_classic: true,
        },
        // 2. Modus Tollens
        Theorem {
            id: "classic-2".to_string(),
            premises: vec![
                Formula::parse("P -> Q").unwrap(),
                Formula::parse("~Q").unwrap(),
            ],
            conclusion: Formula::parse("~P").unwrap(),
            difficulty: Difficulty::Easy,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Easy),
            theme: Some(Theme::ModusTollens),
            name: Some("Modus Tollens".to_string()),
            tier: None,
            is_classic: true,
        },
        // 3. Hypothetical Syllogism
        Theorem {
            id: "classic-3".to_string(),
            premises: vec![
                Formula::parse("P -> Q").unwrap(),
                Formula::parse("Q -> R").unwrap(),
            ],
            conclusion: Formula::parse("P -> R").unwrap(),
            difficulty: Difficulty::Easy,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Easy),
            theme: Some(Theme::HypotheticalSyllogism),
            name: Some("Hypothetical Syllogism".to_string()),
            tier: None,
            is_classic: true,
        },
        // 4. Disjunctive Syllogism
        Theorem {
            id: "classic-4".to_string(),
            premises: vec![
                Formula::parse("P | Q").unwrap(),
                Formula::parse("~P").unwrap(),
            ],
            conclusion: Formula::parse("Q").unwrap(),
            difficulty: Difficulty::Easy,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Easy),
            theme: Some(Theme::DisjunctiveSyllogism),
            name: Some("Disjunctive Syllogism".to_string()),
            tier: None,
            is_classic: true,
        },
        // 5. Constructive Dilemma
        Theorem {
            id: "classic-5".to_string(),
            premises: vec![
                Formula::parse("(P -> Q) & (R -> S)").unwrap(),
                Formula::parse("P | R").unwrap(),
            ],
            conclusion: Formula::parse("Q | S").unwrap(),
            difficulty: Difficulty::Medium,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Medium),
            theme: Some(Theme::ConstructiveDilemma),
            name: Some("Constructive Dilemma".to_string()),
            tier: None,
            is_classic: true,
        },
        // 6. Law of Excluded Middle (requires indirect proof)
        Theorem {
            id: "classic-6".to_string(),
            premises: vec![],
            conclusion: Formula::parse("P | ~P").unwrap(),
            difficulty: Difficulty::Medium,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Medium),
            theme: Some(Theme::IndirectProof),
            name: Some("Law of Excluded Middle".to_string()),
            tier: None,
            is_classic: true,
        },
        // 7. Double Negation Elimination
        Theorem {
            id: "classic-7".to_string(),
            premises: vec![Formula::parse("~~P").unwrap()],
            conclusion: Formula::parse("P").unwrap(),
            difficulty: Difficulty::Easy,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Easy),
            theme: Some(Theme::DoubleNegation),
            name: Some("Double Negation Elimination".to_string()),
            tier: None,
            is_classic: true,
        },
        // 8. Contraposition
        Theorem {
            id: "classic-8".to_string(),
            premises: vec![Formula::parse("P -> Q").unwrap()],
            conclusion: Formula::parse("~Q -> ~P").unwrap(),
            difficulty: Difficulty::Medium,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Medium),
            theme: Some(Theme::ConditionalProof),
            name: Some("Contraposition".to_string()),
            tier: None,
            is_classic: true,
        },
        // 9. DeMorgan's Law (And to Or)
        Theorem {
            id: "classic-9".to_string(),
            premises: vec![Formula::parse("~(P & Q)").unwrap()],
            conclusion: Formula::parse("~P | ~Q").unwrap(),
            difficulty: Difficulty::Hard,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Hard),
            theme: Some(Theme::Equivalence),
            name: Some("De Morgan (And to Or)".to_string()),
            tier: None,
            is_classic: true,
        },
        // 10. DeMorgan's Law (Or to And)
        Theorem {
            id: "classic-10".to_string(),
            premises: vec![Formula::parse("~(P | Q)").unwrap()],
            conclusion: Formula::parse("~P & ~Q").unwrap(),
            difficulty: Difficulty::Hard,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Hard),
            theme: Some(Theme::Equivalence),
            name: Some("De Morgan (Or to And)".to_string()),
            tier: None,
            is_classic: true,
        },
        // 11. Material Implication
        Theorem {
            id: "classic-11".to_string(),
            premises: vec![Formula::parse("P -> Q").unwrap()],
            conclusion: Formula::parse("~P | Q").unwrap(),
            difficulty: Difficulty::Medium,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Medium),
            theme: Some(Theme::Equivalence),
            name: Some("Material Implication".to_string()),
            tier: None,
            is_classic: true,
        },
        // 12. Exportation
        Theorem {
            id: "classic-12".to_string(),
            premises: vec![Formula::parse("(P & Q) -> R").unwrap()],
            conclusion: Formula::parse("P -> (Q -> R)").unwrap(),
            difficulty: Difficulty::Hard,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Hard),
            theme: Some(Theme::ConditionalProof),
            name: Some("Exportation".to_string()),
            tier: None,
            is_classic: true,
        },
        // 13. Pierce's Law (requires indirect proof)
        Theorem {
            id: "classic-13".to_string(),
            premises: vec![],
            conclusion: Formula::parse("((P -> Q) -> P) -> P").unwrap(),
            difficulty: Difficulty::Expert,
            difficulty_value: Theorem::default_value_for_preset(Difficulty::Expert),
            theme: Some(Theme::IndirectProof),
            name: Some("Peirce's Law".to_string()),
            tier: None,
            is_classic: true,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classic_theorems_valid() {
        let classics = get_classic_theorems();
        assert_eq!(classics.len(), 13);
        for theorem in &classics {
            assert!(theorem.is_classic);
        }
    }

    #[test]
    fn test_display_string() {
        let theorem = &get_classic_theorems()[0];
        assert_eq!(theorem.display_string(), "P ⊃ Q, P ⊢ Q");
    }
}
