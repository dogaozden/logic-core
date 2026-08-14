use rand::Rng;
use std::collections::HashSet;
use crate::models::Formula;
use super::super::truth_table::compute_truth_table;

/// Constant for tautology truth table (all 1s)
pub const TAUTOLOGY: u32 = 0xFFFFFFFF;

/// Tracks what proof techniques are required and which have been used.
/// Used to ensure theorems actually force certain techniques at higher difficulties.
#[derive(Debug, Clone, Default)]
pub struct RequiredTechniques {
    /// Whether CP must be used (difficulty >= 30)
    pub need_cp: bool,
    /// Whether case split must be used (difficulty >= 50)
    pub need_case_split: bool,
    /// Whether IP must be used (future: difficulty >= 80)
    pub need_ip: bool,
    /// Whether CP has actually been used in construction
    pub used_cp: bool,
    /// Whether case split has actually been used in construction
    pub used_case_split: bool,
    /// Whether IP has actually been used in construction
    pub used_ip: bool,
    /// Whether CP was used INSIDE a case split branch (for nested technique enforcement)
    pub cp_inside_case_split: bool,
    /// Whether case split was used INSIDE a CP subproof (for nested technique enforcement)
    pub case_split_inside_cp: bool,
}

impl RequiredTechniques {
    /// Create requirements based on difficulty value (1-100)
    pub fn for_difficulty_value(d: u8) -> Self {
        Self {
            need_cp: d >= 30,
            need_case_split: d >= 50,
            need_ip: false, // Future: d >= 80
            ..Default::default()
        }
    }

    /// Check if all required techniques have been used
    pub fn all_requirements_met(&self) -> bool {
        let basic = (!self.need_cp || self.used_cp) &&
                    (!self.need_case_split || self.used_case_split) &&
                    (!self.need_ip || self.used_ip);

        // If both CP and case split are required, they must be nested
        // (CP inside case split OR case split inside CP)
        if self.need_cp && self.need_case_split {
            return basic && (self.cp_inside_case_split || self.case_split_inside_cp);
        }

        basic
    }
}

/// Internal error signals during backward construction.
/// These guide retry logic without creating invalid proofs.
#[derive(Debug, Clone)]
pub enum GenerationError {
    /// CP would be trivial (premises already entail the consequent)
    TrivialCP,
    /// DS is available (negation of a disjunct is available), case split not forced
    DSAvailable,
    /// Hit the depth/fragment limit without completing
    DepthExhausted,
    /// Cannot commit a premise (would create contradiction or redundancy)
    NoPremiseAvailable,
    /// Required techniques were not used in the constructed proof
    RequirementsNotMet,
    /// The goal couldn't be proven with current constraints
    CannotProve,
}

/// Configuration for proof tree generation
#[derive(Debug, Clone)]
pub struct TreeGenConfig {
    /// Pool of atoms to use (P, Q, R, etc.)
    pub atom_pool: Vec<String>,
    /// Target number of fragments (inference steps)
    pub target_fragments: usize,
    /// Maximum allowed nesting depth
    pub max_nesting: usize,
    /// Minimum fragments before stopping
    pub min_fragments: usize,
    /// Minimum proof steps required (for difficulty enforcement)
    /// This is different from min_fragments - it's about how many steps
    /// the SHORTEST proof would take, not how complex the tree structure is
    pub min_proof_steps: usize,
    /// Whether the theorem MUST force conditional proof (CP)
    /// True when conclusion is A⊃B and premises don't entail B alone
    pub require_forces_cp: bool,
    /// Whether the theorem MUST force case split (∨-Elim)
    /// True when premises contain A∨B and neither ~A nor ~B is available
    pub require_forces_case_split: bool,
    /// Whether the theorem MUST force indirect proof (IP)
    /// True when conclusion is atomic/negation and not directly derivable
    pub require_forces_ip: bool,
}

impl TreeGenConfig {
    /// Create config from continuous difficulty value (1-100)
    /// Parameters interpolate smoothly based on difficulty value.
    pub fn for_difficulty_value(difficulty: u8) -> Self {
        let d = difficulty.clamp(1, 100) as usize;

        // Atom count: 2-5 (2 at d=1, 5 at d=100)
        let atom_count = 2 + (d * 3 / 100);
        let atoms: Vec<String> = ["P", "Q", "R", "S", "T"]
            .iter()
            .take(atom_count)
            .map(|s| s.to_string())
            .collect();

        Self {
            atom_pool: atoms,
            target_fragments: 2 + (d * 10 / 100),   // 2-12
            max_nesting: 1 + (d * 4 / 100),         // 1-5
            min_fragments: 1 + (d * 7 / 100),       // 1-8
            min_proof_steps: 1 + (d * 6 / 100),     // 1-7
            require_forces_cp: d >= 30,
            require_forces_case_split: d >= 50,
            require_forces_ip: false,
        }
    }

    /// Create config appropriate for difficulty preset.
    /// Randomizes within the preset's range for variety.
    pub fn for_difficulty(difficulty: crate::models::theorem::Difficulty) -> Self {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let value = match difficulty {
            crate::models::theorem::Difficulty::Easy => rng.gen_range(1..=25),
            crate::models::theorem::Difficulty::Medium => rng.gen_range(26..=45),
            crate::models::theorem::Difficulty::Hard => rng.gen_range(46..=70),
            crate::models::theorem::Difficulty::Expert => rng.gen_range(71..=100),
        };
        Self::for_difficulty_value(value)
    }
}

/// Context maintained during backward proof construction.
/// Tracks premises (committed), assumptions (discharged), and constraints.
#[derive(Debug, Clone)]
pub struct ConstructionContext {
    /// Formulas that will become theorem premises (not discharged)
    pub premises: Vec<Formula>,
    /// Active subproof assumptions (will be discharged)
    pub assumptions: Vec<Formula>,
    /// Combined truth table of all premises (AND of all, starts as TAUTOLOGY)
    pub combined_premises_tt: u32,
    /// Truth tables of individual committed premises (for duplicate/equivalence checking)
    pub premise_truth_tables: HashSet<u32>,
    /// Remaining depth/fragment budget
    pub remaining_depth: usize,
    /// Required techniques tracking
    pub required: RequiredTechniques,
    /// Pool of atoms to use
    pub atom_pool: Vec<String>,
    /// Maximum nesting depth allowed
    pub max_nesting: usize,
    /// Current nesting depth
    pub current_nesting: usize,
}

impl ConstructionContext {
    /// Create a new construction context
    pub fn new(config: &TreeGenConfig, required: RequiredTechniques) -> Self {
        Self {
            premises: Vec::new(),
            assumptions: Vec::new(),
            combined_premises_tt: TAUTOLOGY,
            premise_truth_tables: HashSet::new(),
            remaining_depth: config.target_fragments,
            required,
            atom_pool: config.atom_pool.clone(),
            max_nesting: config.max_nesting,
            current_nesting: 0,
        }
    }

    /// Check if a formula can be committed as a premise without creating degeneracy
    pub fn can_commit_premise(&self, formula: &Formula) -> bool {
        let tt = compute_truth_table(formula);

        // Would create contradiction?
        if (self.combined_premises_tt & tt) == 0 {
            return false;
        }

        // Equivalent to existing premise?
        if self.premise_truth_tables.contains(&tt) {
            return false;
        }

        true
    }

    /// Commit a formula as a premise (update constraint tracking)
    /// Returns true if committed successfully
    pub fn commit_premise(&mut self, formula: Formula) -> bool {
        let tt = compute_truth_table(&formula);

        // Check for contradiction
        if (self.combined_premises_tt & tt) == 0 {
            return false;
        }

        // Check for duplicate
        if self.premise_truth_tables.contains(&tt) {
            return false;
        }

        // Check that we won't make combined_premises_tt == 0 (contradiction)
        let new_combined = self.combined_premises_tt & tt;
        if new_combined == 0 {
            return false;
        }

        self.premise_truth_tables.insert(tt);
        self.combined_premises_tt = new_combined;
        self.premises.push(formula);
        true
    }

    /// Check if a formula is available (either as premise or assumption)
    pub fn is_available(&self, formula: &Formula) -> bool {
        let tt = compute_truth_table(formula);
        // Check premises
        if self.premises.iter().any(|p| compute_truth_table(p) == tt) {
            return true;
        }
        // Check assumptions
        if self.assumptions.iter().any(|a| compute_truth_table(a) == tt) {
            return true;
        }
        false
    }

    /// Get all available formulas (premises + assumptions)
    pub fn available_formulas(&self) -> Vec<&Formula> {
        self.premises.iter().chain(self.assumptions.iter()).collect()
    }

    /// Enter a subproof with a new assumption
    /// Returns a new context with the assumption added
    pub fn enter_subproof(&self, assumption: Formula) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.assumptions.push(assumption);
        new_ctx.current_nesting += 1;
        new_ctx
    }

    /// Check if there's nesting budget remaining
    pub fn has_nesting_budget(&self) -> bool {
        self.current_nesting < self.max_nesting
    }

    /// Random atom from the pool
    pub fn random_atom(&self, rng: &mut impl Rng) -> Formula {
        let idx = rng.gen_range(0..self.atom_pool.len());
        Formula::Atom(self.atom_pool[idx].clone())
    }

    /// Generate a random formula of limited depth
    pub fn random_formula(&self, rng: &mut impl Rng, max_depth: usize) -> Formula {
        if max_depth == 0 {
            return self.random_atom(rng);
        }

        let choice = rng.gen_range(0..100);
        match choice {
            0..=50 => self.random_atom(rng),
            51..=65 => {
                Formula::Not(Box::new(self.random_formula(rng, max_depth - 1)))
            }
            66..=80 => {
                Formula::And(
                    Box::new(self.random_formula(rng, max_depth - 1)),
                    Box::new(self.random_formula(rng, max_depth - 1)),
                )
            }
            81..=90 => {
                Formula::Or(
                    Box::new(self.random_formula(rng, max_depth - 1)),
                    Box::new(self.random_formula(rng, max_depth - 1)),
                )
            }
            _ => {
                Formula::Implies(
                    Box::new(self.random_formula(rng, max_depth - 1)),
                    Box::new(self.random_formula(rng, max_depth - 1)),
                )
            }
        }
    }
}
