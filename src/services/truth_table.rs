use crate::models::Formula;
use std::collections::{BTreeSet, HashSet};

// Constants
const MASK_32: u32 = 0xFFFFFFFF;
const TAUTOLOGY: u32 = 0xFFFFFFFF;
const CONTRADICTION: u32 = 0x00000000;

// ─── Dynamic truth table engine (supports >5 variables) ──────────────────────

/// Dynamic truth table backed by a Vec<u64> bitvector.
/// Supports up to 20 variables (2^20 = 1M rows, ~128 KB).
#[derive(Debug, Clone)]
pub struct DynTruthTable {
    bits: Vec<u64>,
    num_vars: u8,
}

impl DynTruthTable {
    /// Number of u64 words needed for `n` variables (2^n bits / 64 bits per word).
    fn words(num_vars: u8) -> usize {
        let total_bits = 1u64 << num_vars as u64;
        ((total_bits + 63) / 64) as usize
    }

    /// Build the truth table for variable at `index` among `num_vars` variables.
    /// Variable 0 alternates in blocks of 2^(n-1), variable n-1 alternates every bit.
    pub fn new_var(index: u8, num_vars: u8) -> Self {
        let n_words = Self::words(num_vars);
        let mut bits = vec![0u64; n_words];
        // The block size for variable `index` is 2^(num_vars - 1 - index).
        let block_size: u64 = 1u64 << (num_vars as u64 - 1 - index as u64);

        let total_rows = 1u64 << num_vars as u64;
        for row in 0..total_rows {
            // Variable is true when (row / block_size) is even
            if (row / block_size) % 2 == 0 {
                let word_idx = (row / 64) as usize;
                let bit_idx = row % 64;
                bits[word_idx] |= 1u64 << bit_idx;
            }
        }
        Self { bits, num_vars }
    }

    /// All-true (tautology) table.
    pub fn tautology(num_vars: u8) -> Self {
        let n_words = Self::words(num_vars);
        let total_bits = 1u64 << num_vars as u64;
        let mut bits = vec![!0u64; n_words];
        // Mask the last word if total_bits is not a multiple of 64
        let remainder = total_bits % 64;
        if remainder != 0 && !bits.is_empty() {
            let last = bits.len() - 1;
            bits[last] = (1u64 << remainder) - 1;
        }
        Self { bits, num_vars }
    }

    /// All-false (contradiction) table.
    pub fn contradiction(num_vars: u8) -> Self {
        let n_words = Self::words(num_vars);
        Self { bits: vec![0u64; n_words], num_vars }
    }

    pub fn not(&self) -> Self {
        let total_bits = 1u64 << self.num_vars as u64;
        let remainder = total_bits % 64;
        let mut bits: Vec<u64> = self.bits.iter().map(|w| !w).collect();
        if remainder != 0 && !bits.is_empty() {
            let last = bits.len() - 1;
            bits[last] &= (1u64 << remainder) - 1;
        }
        Self { bits, num_vars: self.num_vars }
    }

    pub fn and(&self, other: &Self) -> Self {
        debug_assert_eq!(self.num_vars, other.num_vars);
        let bits = self.bits.iter().zip(&other.bits).map(|(a, b)| a & b).collect();
        Self { bits, num_vars: self.num_vars }
    }

    pub fn or(&self, other: &Self) -> Self {
        debug_assert_eq!(self.num_vars, other.num_vars);
        let bits = self.bits.iter().zip(&other.bits).map(|(a, b)| a | b).collect();
        Self { bits, num_vars: self.num_vars }
    }

    pub fn implies(&self, other: &Self) -> Self {
        self.not().or(other)
    }

    pub fn biconditional(&self, other: &Self) -> Self {
        debug_assert_eq!(self.num_vars, other.num_vars);
        let total_bits = 1u64 << self.num_vars as u64;
        let remainder = total_bits % 64;
        let mut bits: Vec<u64> = self.bits.iter().zip(&other.bits).map(|(a, b)| !(a ^ b)).collect();
        if remainder != 0 && !bits.is_empty() {
            let last = bits.len() - 1;
            bits[last] &= (1u64 << remainder) - 1;
        }
        Self { bits, num_vars: self.num_vars }
    }

    pub fn is_tautology(&self) -> bool {
        let taut = Self::tautology(self.num_vars);
        self.bits == taut.bits
    }

    pub fn is_contradiction(&self) -> bool {
        self.bits.iter().all(|w| *w == 0)
    }

    pub fn eq(&self, other: &Self) -> bool {
        self.num_vars == other.num_vars && self.bits == other.bits
    }
}

/// Collect atoms from a formula into a sorted Vec (alphabetical, deterministic).
fn collect_sorted_atoms(formula: &Formula) -> Vec<String> {
    let atoms: BTreeSet<String> = formula.atoms().into_iter().collect();
    atoms.into_iter().collect()
}

/// Compute a dynamic truth table for any formula (supports >5 variables).
pub fn compute_truth_table_dynamic(formula: &Formula) -> DynTruthTable {
    let atoms = collect_sorted_atoms(formula);
    let num_vars = atoms.len().max(1) as u8;
    let var_map: std::collections::HashMap<&str, u8> = atoms.iter().enumerate()
        .map(|(i, a)| (a.as_str(), i as u8))
        .collect();
    eval_dyn(formula, &var_map, num_vars)
}

fn eval_dyn(formula: &Formula, var_map: &std::collections::HashMap<&str, u8>, num_vars: u8) -> DynTruthTable {
    match formula {
        Formula::Atom(name) => {
            if let Some(&idx) = var_map.get(name.as_str()) {
                DynTruthTable::new_var(idx, num_vars)
            } else {
                DynTruthTable::tautology(num_vars)
            }
        }
        Formula::Not(inner) => eval_dyn(inner, var_map, num_vars).not(),
        Formula::And(l, r) => eval_dyn(l, var_map, num_vars).and(&eval_dyn(r, var_map, num_vars)),
        Formula::Or(l, r) => eval_dyn(l, var_map, num_vars).or(&eval_dyn(r, var_map, num_vars)),
        Formula::Implies(l, r) => eval_dyn(l, var_map, num_vars).implies(&eval_dyn(r, var_map, num_vars)),
        Formula::Biconditional(l, r) => eval_dyn(l, var_map, num_vars).biconditional(&eval_dyn(r, var_map, num_vars)),
        Formula::Contradiction => DynTruthTable::contradiction(num_vars),
    }
}

/// Check if a formula is a tautology, auto-selecting the engine.
/// Uses the fast u32 path for formulas with ≤5 standard atoms (P,Q,R,S,T),
/// dynamic path otherwise.
pub fn is_tautology_dynamic(formula: &Formula) -> bool {
    let atoms = formula.atoms();
    let standard = ["P", "Q", "R", "S", "T"];
    if atoms.len() <= 5 && atoms.iter().all(|a| standard.contains(&a.as_str())) {
        is_tautology(formula)
    } else {
        compute_truth_table_dynamic(formula).is_tautology()
    }
}

/// Variable truth tables (standard row ordering PQRST from 11111 to 00000)
fn var_truth_table(name: &str) -> u32 {
    match name {
        "P" => 0xFFFF0000,
        "Q" => 0xFF00FF00,
        "R" => 0xF0F0F0F0,
        "S" => 0xCCCCCCCC,
        "T" => 0xAAAAAAAA,
        _ => 0xFFFF0000, // Default to P pattern for unknown vars
    }
}

/// Compute 32-bit truth table for any formula
pub fn compute_truth_table(formula: &Formula) -> u32 {
    match formula {
        Formula::Atom(name) => var_truth_table(name),
        Formula::Not(inner) => !compute_truth_table(inner) & MASK_32,
        Formula::And(l, r) => compute_truth_table(l) & compute_truth_table(r),
        Formula::Or(l, r) => compute_truth_table(l) | compute_truth_table(r),
        Formula::Implies(l, r) => (!compute_truth_table(l) | compute_truth_table(r)) & MASK_32,
        Formula::Biconditional(l, r) => !(compute_truth_table(l) ^ compute_truth_table(r)) & MASK_32,
        Formula::Contradiction => CONTRADICTION,
    }
}

// === Semantic Checks ===

/// Check if a formula is a tautology (always true)
pub fn is_tautology(formula: &Formula) -> bool {
    compute_truth_table(formula) == TAUTOLOGY
}

/// Check if a formula is a contradiction (always false)
pub fn is_contradiction(formula: &Formula) -> bool {
    compute_truth_table(formula) == CONTRADICTION
}

/// Check if two formulas are semantically equivalent
pub fn are_equivalent(f1: &Formula, f2: &Formula) -> bool {
    compute_truth_table(f1) == compute_truth_table(f2)
}

/// Check if a set of premises is consistent (not contradictory)
pub fn premises_consistent(premises: &[Formula]) -> bool {
    let combined: u32 = premises.iter()
        .map(|p| compute_truth_table(p))
        .fold(TAUTOLOGY, |acc, tt| acc & tt);
    combined != CONTRADICTION
}

/// Check if premises semantically entail a conclusion
pub fn entails(premises: &[Formula], conclusion: &Formula) -> bool {
    let combined_premises: u32 = premises.iter()
        .map(|p| compute_truth_table(p))
        .fold(TAUTOLOGY, |acc, tt| acc & tt);
    let conclusion_tt = compute_truth_table(conclusion);
    // Counterexample = row where premises true but conclusion false
    (combined_premises & (!conclusion_tt & MASK_32)) == CONTRADICTION
}

/// Check if any single premise alone entails the conclusion
pub fn single_premise_entails(premises: &[Formula], conclusion: &Formula) -> bool {
    let conclusion_tt = compute_truth_table(conclusion);
    for p in premises {
        let premise_tt = compute_truth_table(p);
        // Check if premise alone entails conclusion
        if (premise_tt & (!conclusion_tt & MASK_32)) == CONTRADICTION {
            return true;
        }
    }
    false
}

/// Check if the negation of the conclusion is semantically equivalent to any premise
pub fn conclusion_negation_available(premises: &[Formula], conclusion: &Formula) -> bool {
    let neg_conclusion_tt = !compute_truth_table(conclusion) & MASK_32;
    premises.iter().any(|p| compute_truth_table(p) == neg_conclusion_tt)
}

/// Check if a conditional conclusion is trivially provable via explosion
/// (i.e., one of the antecedents' negations is available as a premise)
pub fn conditional_trivial_via_explosion(premises: &[Formula], conclusion: &Formula) -> bool {
    // Extract antecedent chain from nested conditionals
    let mut antecedents = vec![];
    let mut current = conclusion;
    while let Formula::Implies(ant, cons) = current {
        antecedents.push(ant.as_ref());
        current = cons.as_ref();
    }
    if antecedents.is_empty() { return false; }

    // Check if ~antecedent is equivalent to any premise
    for ant in antecedents {
        let neg_ant_tt = !compute_truth_table(ant) & MASK_32;
        if premises.iter().any(|p| compute_truth_table(p) == neg_ant_tt) {
            return true;
        }
    }
    false
}

/// Check if all premises are necessary for the entailment
pub fn all_premises_necessary(premises: &[Formula], conclusion: &Formula) -> bool {
    if !entails(premises, conclusion) { return false; }
    for i in 0..premises.len() {
        let reduced: Vec<_> = premises.iter().enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, p)| p.clone())
            .collect();
        if entails(&reduced, conclusion) {
            return false; // Premise i was redundant
        }
    }
    true
}

/// Check if there are redundant (semantically equivalent) premises
pub fn has_redundant_premises(premises: &[Formula]) -> bool {
    let truth_tables: Vec<u32> = premises.iter().map(compute_truth_table).collect();
    let unique: HashSet<u32> = truth_tables.iter().copied().collect();
    truth_tables.len() != unique.len()
}

// === Forcing Check Functions ===

/// Check if theorem FORCES conditional proof.
/// True if: conclusion is A⊃B AND premises alone don't entail B
pub fn forces_cp(premises: &[Formula], conclusion: &Formula) -> bool {
    if let Formula::Implies(_, consequent) = conclusion {
        // If premises already entail the consequent, CP is optional
        // (can just derive B, then wrap in trivial CP)
        !entails(premises, consequent)
    } else {
        false // Not a conditional conclusion
    }
}

/// Check if theorem FORCES case split (∨-Elim).
/// True if: premises contain A∨B AND neither ~A nor ~B is available
pub fn forces_case_split(premises: &[Formula]) -> bool {
    for p in premises {
        if let Formula::Or(left, right) = p {
            let neg_left_tt = !compute_truth_table(left) & MASK_32;
            let neg_right_tt = !compute_truth_table(right) & MASK_32;

            let neg_left_available = premises.iter()
                .any(|q| compute_truth_table(q) == neg_left_tt);
            let neg_right_available = premises.iter()
                .any(|q| compute_truth_table(q) == neg_right_tt);

            // If neither negation available, DS is blocked → must case split
            if !neg_left_available && !neg_right_available {
                return true;
            }
        }
    }
    false
}

/// Check if theorem FORCES indirect proof.
/// True if: conclusion is not directly derivable via single basic rule application
/// AND not a conditional (which would use CP instead)
pub fn forces_ip(premises: &[Formula], conclusion: &Formula) -> bool {
    // IP is typically needed for:
    // 1. Atomic conclusions not derivable via MP/Simp/DS
    // 2. Negation conclusions not derivable via MT
    // 3. Classical tautology patterns

    // Skip if it's a conditional (CP territory)
    if matches!(conclusion, Formula::Implies(_, _)) {
        return false;
    }

    // Skip if it's a disjunction (Add territory) or conjunction (Conj territory)
    if matches!(conclusion, Formula::Or(_, _) | Formula::And(_, _)) {
        return false;
    }

    // For atoms and negations: check if directly derivable
    !can_derive_directly(premises, conclusion)
}

/// Helper: Check if conclusion is directly derivable via ONE basic rule application
fn can_derive_directly(premises: &[Formula], conclusion: &Formula) -> bool {
    let conclusion_tt = compute_truth_table(conclusion);

    // 1. Direct availability (0 steps)
    if premises.iter().any(|p| compute_truth_table(p) == conclusion_tt) {
        return true;
    }

    // 2. MP: Find A⊃B where B ≡ conclusion, and A available
    for p in premises {
        if let Formula::Implies(ant, cons) = p {
            if compute_truth_table(cons.as_ref()) == conclusion_tt {
                let ant_tt = compute_truth_table(ant.as_ref());
                if premises.iter().any(|q| compute_truth_table(q) == ant_tt) {
                    return true;
                }
            }
        }
    }

    // 3. MT: If conclusion is ~A, find A⊃B and ~B
    if let Formula::Not(inner) = conclusion {
        let inner_tt = compute_truth_table(inner.as_ref());
        for p in premises {
            if let Formula::Implies(ant, cons) = p {
                if compute_truth_table(ant.as_ref()) == inner_tt {
                    // Found A⊃B where A matches. Need ~B available.
                    let neg_cons_tt = !compute_truth_table(cons.as_ref()) & MASK_32;
                    if premises.iter().any(|q| compute_truth_table(q) == neg_cons_tt) {
                        return true;
                    }
                }
            }
        }
    }

    // 4. Simp: Find A∧B where A ≡ conclusion or B ≡ conclusion
    for p in premises {
        if let Formula::And(left, right) = p {
            if compute_truth_table(left.as_ref()) == conclusion_tt ||
               compute_truth_table(right.as_ref()) == conclusion_tt {
                return true;
            }
        }
    }

    // 5. DS: Find A∨B and ~A where B ≡ conclusion (or vice versa)
    for p in premises {
        if let Formula::Or(left, right) = p {
            // A∨B, ~A ⊢ B
            if compute_truth_table(right.as_ref()) == conclusion_tt {
                let neg_left_tt = !compute_truth_table(left.as_ref()) & MASK_32;
                if premises.iter().any(|q| compute_truth_table(q) == neg_left_tt) {
                    return true;
                }
            }
            // A∨B, ~B ⊢ A
            if compute_truth_table(left.as_ref()) == conclusion_tt {
                let neg_right_tt = !compute_truth_table(right.as_ref()) & MASK_32;
                if premises.iter().any(|q| compute_truth_table(q) == neg_right_tt) {
                    return true;
                }
            }
        }
    }

    // 6. DN: If conclusion is ~~A, check if A is available
    if let Formula::Not(inner) = conclusion {
        if let Formula::Not(inner2) = inner.as_ref() {
            let inner2_tt = compute_truth_table(inner2.as_ref());
            if premises.iter().any(|q| compute_truth_table(q) == inner2_tt) {
                return true;
            }
        }
    }

    false
}

// === Main Validation ===

use super::proof_tree::DegenerateProofError;

/// Validate that a theorem is non-degenerate
pub fn validate_theorem(premises: &[Formula], conclusion: &Formula) -> Result<(), DegenerateProofError> {
    validate_theorem_with_difficulty(premises, conclusion, None, false, false, false)
}

/// Validate theorem with optional difficulty-based requirements
/// - min_steps: minimum number of proof steps required
/// - require_cp: if true, theorem must force conditional proof
/// - require_case_split: if true, theorem must force case split (disjunction elimination)
/// - require_ip: if true, theorem must force indirect proof
pub fn validate_theorem_with_difficulty(
    premises: &[Formula],
    conclusion: &Formula,
    min_steps: Option<usize>,
    require_cp: bool,
    require_case_split: bool,
    require_ip: bool,
) -> Result<(), DegenerateProofError> {
    // 1. Premises consistent
    if !premises_consistent(premises) {
        return Err(DegenerateProofError::ContradictoryPremises);
    }

    // 1.5. No tautological premises (P⊃P, P∨~P, etc. - always true, useless)
    for premise in premises {
        if is_tautology(premise) {
            return Err(DegenerateProofError::TautologicalPremise);
        }
    }

    // 2. Conclusion not a tautology
    if is_tautology(conclusion) {
        return Err(DegenerateProofError::TautologicalConclusion);
    }

    // 3. No single premise entails conclusion
    if single_premise_entails(premises, conclusion) {
        return Err(DegenerateProofError::SinglePremiseEntails);
    }

    // 4. Negation of conclusion not available
    if conclusion_negation_available(premises, conclusion) {
        return Err(DegenerateProofError::NegationOfConclusionAvailable);
    }

    // 5. Conditional not trivially provable via explosion
    if conditional_trivial_via_explosion(premises, conclusion) {
        return Err(DegenerateProofError::ConditionalTrivialViaExplosion);
    }

    // 6. No redundant premises
    if has_redundant_premises(premises) {
        return Err(DegenerateProofError::RedundantPremises);
    }

    // 7. All premises necessary
    if !all_premises_necessary(premises, conclusion) {
        return Err(DegenerateProofError::UnnecessaryPremise);
    }

    // 8. Theorem must be valid
    if !entails(premises, conclusion) {
        return Err(DegenerateProofError::InvalidTheorem);
    }

    // 9. Check minimum proof steps (difficulty enforcement)
    if let Some(min) = min_steps {
        if let Some(actual) = super::proof_search::minimum_proof_steps(premises, conclusion, min) {
            if actual < min {
                return Err(DegenerateProofError::TooEasy {
                    min_steps: min,
                    actual_steps: actual,
                });
            }
        }
    }

    // 10. Forcing requirements (structural difficulty checks)
    if require_cp && !forces_cp(premises, conclusion) {
        return Err(DegenerateProofError::DoesNotForceCP);
    }

    if require_case_split && !forces_case_split(premises) {
        return Err(DegenerateProofError::DoesNotForceCaseSplit);
    }

    if require_ip && !forces_ip(premises, conclusion) {
        return Err(DegenerateProofError::DoesNotForceIP);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(name: &str) -> Formula {
        Formula::Atom(name.to_string())
    }

    fn not(f: Formula) -> Formula {
        Formula::Not(Box::new(f))
    }

    fn and(a: Formula, b: Formula) -> Formula {
        Formula::And(Box::new(a), Box::new(b))
    }

    fn or(a: Formula, b: Formula) -> Formula {
        Formula::Or(Box::new(a), Box::new(b))
    }

    fn implies(a: Formula, b: Formula) -> Formula {
        Formula::Implies(Box::new(a), Box::new(b))
    }

    // === Truth Table Tests ===

    #[test]
    fn test_atom_truth_tables() {
        assert_eq!(compute_truth_table(&atom("P")), 0xFFFF0000);
        assert_eq!(compute_truth_table(&atom("Q")), 0xFF00FF00);
        assert_eq!(compute_truth_table(&atom("R")), 0xF0F0F0F0);
    }

    #[test]
    fn test_negation_truth_table() {
        // ~P should flip all bits of P
        let p_tt = compute_truth_table(&atom("P"));
        let not_p_tt = compute_truth_table(&not(atom("P")));
        assert_eq!(not_p_tt, !p_tt & MASK_32);
    }

    #[test]
    fn test_double_negation_equivalence() {
        // ~~P should be equivalent to P
        let p = atom("P");
        let not_not_p = not(not(atom("P")));
        assert!(are_equivalent(&p, &not_not_p));
    }

    #[test]
    fn test_demorgan() {
        // ~(P & Q) should be equivalent to ~P | ~Q
        let left = not(and(atom("P"), atom("Q")));
        let right = or(not(atom("P")), not(atom("Q")));
        assert!(are_equivalent(&left, &right));
    }

    #[test]
    fn test_implication_equivalence() {
        // P -> Q should be equivalent to ~P | Q
        let impl_form = implies(atom("P"), atom("Q"));
        let disj_form = or(not(atom("P")), atom("Q"));
        assert!(are_equivalent(&impl_form, &disj_form));
    }

    // === Tautology Tests ===

    #[test]
    fn test_lem_is_tautology() {
        // P | ~P is a tautology
        let lem = or(atom("P"), not(atom("P")));
        assert!(is_tautology(&lem));
    }

    #[test]
    fn test_self_implication_is_tautology() {
        // P -> P is a tautology
        let self_impl = implies(atom("P"), atom("P"));
        assert!(is_tautology(&self_impl));
    }

    #[test]
    fn test_atom_not_tautology() {
        assert!(!is_tautology(&atom("P")));
    }

    // === Contradiction Tests ===

    #[test]
    fn test_contradiction_constant() {
        assert!(is_contradiction(&Formula::Contradiction));
    }

    #[test]
    fn test_p_and_not_p_is_contradiction() {
        let contra = and(atom("P"), not(atom("P")));
        assert!(is_contradiction(&contra));
    }

    // === Semantic Entailment Tests ===

    #[test]
    fn test_mp_entailment() {
        // P, P -> Q entails Q
        let premises = vec![atom("P"), implies(atom("P"), atom("Q"))];
        let conclusion = atom("Q");
        assert!(entails(&premises, &conclusion));
    }

    #[test]
    fn test_single_premise_entails_disjunction() {
        // P single-handedly entails P | Q
        let premises = vec![atom("P")];
        let conclusion = or(atom("P"), atom("Q"));
        assert!(single_premise_entails(&premises, &conclusion));
    }

    #[test]
    fn test_single_premise_entails_double_negation() {
        // P single-handedly entails ~~P
        let premises = vec![atom("P")];
        let conclusion = not(not(atom("P")));
        assert!(single_premise_entails(&premises, &conclusion));
    }

    // === Degenerate Proof Tests ===

    #[test]
    fn test_reject_contradictory_premises() {
        // P, ~P |- Q should be rejected
        let premises = vec![atom("P"), not(atom("P"))];
        let conclusion = atom("Q");
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::ContradictoryPremises)
        ));
    }

    #[test]
    fn test_reject_tautological_conclusion() {
        // ... |- P | ~P should be rejected
        let premises = vec![atom("Q")];
        let conclusion = or(atom("P"), not(atom("P")));
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::TautologicalConclusion)
        ));
    }

    #[test]
    fn test_reject_single_premise_entails() {
        // P |- P should be rejected (begging the question)
        let premises = vec![atom("P")];
        let conclusion = atom("P");
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::SinglePremiseEntails)
        ));
    }

    #[test]
    fn test_reject_semantic_single_premise_entails() {
        // P |- ~~P should be rejected (semantically the same)
        let premises = vec![atom("P")];
        let conclusion = not(not(atom("P")));
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::SinglePremiseEntails)
        ));
    }

    #[test]
    fn test_reject_conjunction_entails_conjunct() {
        // P & Q |- P should be rejected
        let premises = vec![and(atom("P"), atom("Q"))];
        let conclusion = atom("P");
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::SinglePremiseEntails)
        ));
    }

    #[test]
    fn test_reject_disjunction_via_add() {
        // P |- P | Q should be rejected
        let premises = vec![atom("P")];
        let conclusion = or(atom("P"), atom("Q"));
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::SinglePremiseEntails)
        ));
    }

    #[test]
    fn test_reject_semantic_contradiction() {
        // T | T, ~T |- Q should be rejected (T|T is equivalent to T)
        let premises = vec![or(atom("T"), atom("T")), not(atom("T"))];
        let conclusion = atom("Q");
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::ContradictoryPremises)
        ));
    }

    #[test]
    fn test_reject_explosion_conditional() {
        // ~P |- P -> Q should be rejected
        // Note: This gets caught by SinglePremiseEntails first, because ~P semantically
        // entails P -> Q (since P -> Q is ~P | Q, and if ~P is true, so is ~P | Q)
        let premises = vec![not(atom("P"))];
        let conclusion = implies(atom("P"), atom("Q"));
        let result = validate_theorem(&premises, &conclusion);
        assert!(result.is_err());
        // Either SinglePremiseEntails or ConditionalTrivialViaExplosion is valid
        assert!(matches!(
            result.unwrap_err(),
            DegenerateProofError::SinglePremiseEntails | DegenerateProofError::ConditionalTrivialViaExplosion
        ));
    }

    #[test]
    fn test_reject_redundant_premises() {
        // P, P, Q |- P & Q should be rejected (redundant P)
        let premises = vec![atom("P"), atom("P"), atom("Q")];
        let conclusion = and(atom("P"), atom("Q"));
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::RedundantPremises)
        ));
    }

    #[test]
    fn test_reject_unnecessary_premise() {
        // P, Q, R |- P & Q should be rejected (R unnecessary)
        let premises = vec![atom("P"), atom("Q"), atom("R")];
        let conclusion = and(atom("P"), atom("Q"));
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::UnnecessaryPremise)
        ));
    }

    #[test]
    fn test_valid_mp_theorem() {
        // P, P -> Q |- Q is valid and non-degenerate
        let premises = vec![atom("P"), implies(atom("P"), atom("Q"))];
        let conclusion = atom("Q");
        assert!(validate_theorem(&premises, &conclusion).is_ok());
    }

    #[test]
    fn test_valid_hs_theorem() {
        // P -> Q, Q -> R |- P -> R is valid and non-degenerate
        let premises = vec![
            implies(atom("P"), atom("Q")),
            implies(atom("Q"), atom("R")),
        ];
        let conclusion = implies(atom("P"), atom("R"));
        assert!(validate_theorem(&premises, &conclusion).is_ok());
    }

    // === Forcing Check Tests ===

    #[test]
    fn test_forces_cp_true() {
        // A⊃B, C⊃D ⊢ (A∧C)⊃(B∧D) - premises don't entail B∧D
        let a = atom("P");
        let b = atom("Q");
        let c = atom("R");
        let d = atom("S");
        let premises = vec![implies(a.clone(), b.clone()), implies(c.clone(), d.clone())];
        let conclusion = implies(and(a, c), and(b, d));
        assert!(forces_cp(&premises, &conclusion));
    }

    #[test]
    fn test_forces_cp_false() {
        // A, B ⊢ C⊃(A∧B) - premises DO entail A∧B, so CP is trivial
        let a = atom("P");
        let b = atom("Q");
        let c = atom("R");
        let premises = vec![a.clone(), b.clone()];
        let conclusion = implies(c, and(a, b));
        assert!(!forces_cp(&premises, &conclusion));
    }

    #[test]
    fn test_forces_cp_not_conditional() {
        // P, P⊃Q ⊢ Q - conclusion is not conditional, so CP not forced
        let premises = vec![atom("P"), implies(atom("P"), atom("Q"))];
        let conclusion = atom("Q");
        assert!(!forces_cp(&premises, &conclusion));
    }

    #[test]
    fn test_forces_case_split_true() {
        // A∨B, A⊃C, B⊃C ⊢ C - no ~A or ~B available
        let a = atom("P");
        let b = atom("Q");
        let c = atom("R");
        let premises = vec![or(a.clone(), b.clone()), implies(a, c.clone()), implies(b, c)];
        assert!(forces_case_split(&premises));
    }

    #[test]
    fn test_forces_case_split_false() {
        // A∨B, ~A ⊢ B - DS works, no case split needed
        let a = atom("P");
        let b = atom("Q");
        let premises = vec![or(a.clone(), b), not(a)];
        assert!(!forces_case_split(&premises));
    }

    #[test]
    fn test_forces_case_split_no_disjunction() {
        // P, P⊃Q ⊢ Q - no disjunction in premises
        let premises = vec![atom("P"), implies(atom("P"), atom("Q"))];
        assert!(!forces_case_split(&premises));
    }

    #[test]
    fn test_rejects_tautological_premise() {
        // P⊃P, Q ⊢ Q - P⊃P is tautology
        let premises = vec![implies(atom("P"), atom("P")), atom("Q")];
        let conclusion = atom("Q");
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::TautologicalPremise)
        ));
    }

    #[test]
    fn test_rejects_lem_premise() {
        // P∨~P, Q ⊢ Q - P∨~P is tautology
        let premises = vec![or(atom("P"), not(atom("P"))), atom("Q")];
        let conclusion = atom("Q");
        assert!(matches!(
            validate_theorem(&premises, &conclusion),
            Err(DegenerateProofError::TautologicalPremise)
        ));
    }

    #[test]
    fn test_forces_ip_atom_not_directly_derivable() {
        // P⊃Q, Q⊃R ⊢ P (hypothetically - this is invalid but tests the function)
        // forces_ip checks structure, not validity
        let premises = vec![implies(atom("P"), atom("Q")), implies(atom("Q"), atom("R"))];
        let conclusion = atom("P");
        // P is not directly derivable from these premises via basic rules
        assert!(forces_ip(&premises, &conclusion));
    }

    #[test]
    fn test_forces_ip_atom_directly_derivable() {
        // P, P⊃Q ⊢ Q - Q is derivable via MP
        let premises = vec![atom("P"), implies(atom("P"), atom("Q"))];
        let conclusion = atom("Q");
        // Q is directly derivable via MP
        assert!(!forces_ip(&premises, &conclusion));
    }

    #[test]
    fn test_forces_ip_conditional_conclusion() {
        // ... ⊢ P⊃Q - conditionals use CP, not IP
        let premises = vec![atom("P")];
        let conclusion = implies(atom("P"), atom("Q"));
        assert!(!forces_ip(&premises, &conclusion));
    }

    #[test]
    fn test_can_derive_directly_via_simp() {
        // P∧Q ⊢ P - derivable via Simp
        let premises = vec![and(atom("P"), atom("Q"))];
        let conclusion = atom("P");
        assert!(can_derive_directly(&premises, &conclusion));
    }

    #[test]
    fn test_can_derive_directly_via_ds() {
        // P∨Q, ~P ⊢ Q - derivable via DS
        let premises = vec![or(atom("P"), atom("Q")), not(atom("P"))];
        let conclusion = atom("Q");
        assert!(can_derive_directly(&premises, &conclusion));
    }

    #[test]
    fn test_can_derive_directly_via_mt() {
        // P⊃Q, ~Q ⊢ ~P - derivable via MT
        let premises = vec![implies(atom("P"), atom("Q")), not(atom("Q"))];
        let conclusion = not(atom("P"));
        assert!(can_derive_directly(&premises, &conclusion));
    }

    // === New Edge Case Tests ===

    #[test]
    fn test_forces_ip_with_negation_conclusion() {
        // For a negation conclusion like ~P, check forces_ip behavior
        // If ~P is not directly derivable, IP might be needed

        // P⊃Q ⊢ ~P (hypothetically invalid but tests structure)
        let premises = vec![implies(atom("P"), atom("Q"))];
        let conclusion = not(atom("P"));

        // ~P is not directly available via MT (need ~Q), so IP might be forced
        let result = forces_ip(&premises, &conclusion);
        // Since ~P can't be derived via basic rules from P⊃Q alone, should return true
        assert!(result, "forces_ip should return true when negation can't be directly derived");
    }

    #[test]
    fn test_forces_case_split_multiple_disjunctions() {
        // Test with multiple disjunctions in premises
        // P∨Q, R∨S ⊢ X
        // Both disjunctions lack their negations, so case split is forced

        let p = atom("P");
        let q = atom("Q");
        let r = atom("R");
        let s = atom("S");

        let premises = vec![or(p, q), or(r, s)];

        // Should force case split because neither ~P/~Q nor ~R/~S is available
        assert!(forces_case_split(&premises));
    }

    #[test]
    fn test_can_derive_directly_via_dn_elimination() {
        // ~~P ⊢ P - should be derivable via DN (recognized as direct availability)
        let premises = vec![not(not(atom("P")))];
        let conclusion = atom("P");

        // Note: can_derive_directly checks for DN in conclusion form (~~A where A is conclusion)
        // but here we have ~~P as premise and P as conclusion
        // This tests semantic equivalence - ~~P and P have the same truth table
        assert!(can_derive_directly(&premises, &conclusion),
            "P should be derivable from ~~P via semantic equivalence");
    }

    #[test]
    fn test_biconditional_truth_table_computation() {
        // P ≡ Q should be equivalent to (P ⊃ Q) & (Q ⊃ P)
        let p = atom("P");
        let q = atom("Q");

        let biconditional = Formula::Biconditional(Box::new(p.clone()), Box::new(q.clone()));
        let expanded = and(
            implies(p.clone(), q.clone()),
            implies(q, p),
        );

        // Both should have the same truth table
        let bicon_tt = compute_truth_table(&biconditional);
        let expanded_tt = compute_truth_table(&expanded);

        assert_eq!(bicon_tt, expanded_tt,
            "P≡Q should have same truth table as (P⊃Q)&(Q⊃P)");

        // Also verify they are semantically equivalent
        assert!(are_equivalent(&biconditional, &expanded));
    }

    // === Dynamic Truth Table Tests ===

    #[test]
    fn test_dyn_tautology_simple() {
        // P | ~P is a tautology
        let lem = or(atom("P"), not(atom("P")));
        assert!(is_tautology_dynamic(&lem));
    }

    #[test]
    fn test_dyn_not_tautology() {
        assert!(!is_tautology_dynamic(&atom("P")));
    }

    #[test]
    fn test_dyn_agrees_with_u32() {
        // Test that dynamic engine agrees with u32 for standard atoms
        let formulas = vec![
            implies(atom("P"), atom("P")),
            implies(and(atom("P"), implies(atom("P"), atom("Q"))), atom("Q")),
            or(atom("P"), not(atom("P"))),
            and(atom("P"), not(atom("P"))),
        ];
        for f in &formulas {
            assert_eq!(
                is_tautology(f),
                compute_truth_table_dynamic(f).is_tautology(),
                "Disagreement on: {:?}",
                f
            );
        }
    }

    #[test]
    fn test_dyn_six_variables() {
        // A | ~A with a non-standard atom name should work dynamically
        let a = Formula::Atom("A".to_string());
        let b = Formula::Atom("B".to_string());
        let c = Formula::Atom("C".to_string());
        let d = Formula::Atom("D".to_string());
        let e = Formula::Atom("E".to_string());
        let f = Formula::Atom("F".to_string());

        // (A | ~A) is a tautology regardless of other atoms in a larger formula
        let taut = or(a.clone(), not(a.clone()));
        assert!(is_tautology_dynamic(&taut));

        // A & B & C & D & E & F is NOT a tautology
        let big_and = Formula::And(
            Box::new(Formula::And(
                Box::new(Formula::And(Box::new(a), Box::new(b))),
                Box::new(Formula::And(Box::new(c), Box::new(d))),
            )),
            Box::new(Formula::And(Box::new(e), Box::new(f))),
        );
        assert!(!is_tautology_dynamic(&big_and));
    }

    #[test]
    fn test_dyn_modus_ponens_wrapped() {
        // (A & (A -> B)) -> B is a tautology for any atom names
        let a = Formula::Atom("X".to_string());
        let b = Formula::Atom("Y".to_string());
        let wrapped = implies(
            and(a.clone(), implies(a, b.clone())),
            b,
        );
        assert!(is_tautology_dynamic(&wrapped));
    }
}
