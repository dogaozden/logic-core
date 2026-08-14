use serde::{Deserialize, Serialize};
use crate::models::formula::Formula;

/// Proof techniques that involve subproofs
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ProofTechnique {
    /// Conditional Proof: Assume P, derive Q, conclude P → Q
    ConditionalProof,

    /// Indirect Proof (Reductio ad Absurdum):
    /// - Assume ~P, derive contradiction, conclude P
    /// - Assume P, derive contradiction, conclude ~P
    IndirectProof,
}

/// Check if a formula represents a contradiction (⊥ or P · ~P)
pub fn is_contradiction(formula: &Formula) -> bool {
    // Check for ⊥
    if matches!(formula, Formula::Contradiction) {
        return true;
    }
    // Check for P · ~P (conjunction where one conjunct is negation of other)
    if let Formula::And(left, right) = formula {
        // left = ~right
        if let Formula::Not(inner) = left.as_ref() {
            if inner.as_ref() == right.as_ref() {
                return true;
            }
        }
        // right = ~left
        if let Formula::Not(inner) = right.as_ref() {
            if inner.as_ref() == left.as_ref() {
                return true;
            }
        }
    }
    false
}

impl ProofTechnique {
    pub fn name(&self) -> &'static str {
        match self {
            ProofTechnique::ConditionalProof => "Conditional Proof",
            ProofTechnique::IndirectProof => "Indirect Proof",
        }
    }

    pub fn abbreviation(&self) -> &'static str {
        match self {
            ProofTechnique::ConditionalProof => "CP",
            ProofTechnique::IndirectProof => "IP",
        }
    }

    pub fn description(&self) -> &'static str {
        match self {
            ProofTechnique::ConditionalProof => {
                "Assume the antecedent P, derive the consequent Q within the subproof, \
                 then conclude P → Q outside the subproof."
            }
            ProofTechnique::IndirectProof => {
                "Assume P or ~P, derive a contradiction (⊥ or Q · ~Q), \
                 then conclude the opposite of your assumption."
            }
        }
    }

    /// Get the conclusion formula given the assumption and the derived formula
    pub fn get_conclusion(&self, assumption: &Formula, derived: &Formula) -> Option<Formula> {
        match self {
            ProofTechnique::ConditionalProof => {
                // Assume P, derive Q → conclude P → Q
                Some(Formula::Implies(
                    Box::new(assumption.clone()),
                    Box::new(derived.clone()),
                ))
            }
            ProofTechnique::IndirectProof => {
                // Must derive a contradiction (⊥ or P · ~P)
                if !is_contradiction(derived) {
                    return None;
                }
                // IP handles both directions:
                // - Assume ~P, derive contradiction → conclude P (removes negation)
                // - Assume P, derive contradiction → conclude ~P (adds negation)
                if let Formula::Not(inner) = assumption {
                    Some(inner.as_ref().clone())
                } else {
                    Some(Formula::Not(Box::new(assumption.clone())))
                }
            }
        }
    }

    /// Verify that the conclusion follows correctly from the subproof
    pub fn verify_conclusion(
        &self,
        assumption: &Formula,
        derived: &Formula,
        conclusion: &Formula,
    ) -> bool {
        if let Some(expected) = self.get_conclusion(assumption, derived) {
            expected == *conclusion
        } else {
            false
        }
    }

    /// Get all proof techniques
    pub fn all() -> Vec<ProofTechnique> {
        vec![
            ProofTechnique::ConditionalProof,
            ProofTechnique::IndirectProof,
        ]
    }

    /// Check if this technique requires a contradiction to be derived
    pub fn requires_contradiction(&self) -> bool {
        matches!(self, ProofTechnique::IndirectProof)
    }

    /// Get the type of assumption expected for this technique
    pub fn expected_assumption_type(&self) -> AssumptionType {
        match self {
            ProofTechnique::ConditionalProof => AssumptionType::Any,
            // IP accepts any assumption - it will negate whatever you assumed
            ProofTechnique::IndirectProof => AssumptionType::Any,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssumptionType {
    /// Any formula can be assumed
    Any,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_conditional_proof() {
        let assumption = Formula::parse("P").unwrap();
        let derived = Formula::parse("Q").unwrap();
        let expected = Formula::parse("P -> Q").unwrap();

        let conclusion = ProofTechnique::ConditionalProof
            .get_conclusion(&assumption, &derived)
            .unwrap();
        assert_eq!(conclusion, expected);
    }

    #[test]
    fn test_indirect_proof_with_contradiction_symbol() {
        // Assume ~P, derive ⊥ → conclude P
        let assumption = Formula::parse("~P").unwrap();
        let derived = Formula::Contradiction;
        let expected = Formula::parse("P").unwrap();

        let conclusion = ProofTechnique::IndirectProof
            .get_conclusion(&assumption, &derived)
            .unwrap();
        assert_eq!(conclusion, expected);
    }

    #[test]
    fn test_indirect_proof_with_p_and_not_p() {
        // Assume ~P, derive A · ~A → conclude P
        let assumption = Formula::parse("~P").unwrap();
        let derived = Formula::parse("A & ~A").unwrap();
        let expected = Formula::parse("P").unwrap();

        let conclusion = ProofTechnique::IndirectProof
            .get_conclusion(&assumption, &derived)
            .unwrap();
        assert_eq!(conclusion, expected);
    }

    #[test]
    fn test_indirect_proof_with_not_p_and_p() {
        // Assume ~P, derive ~A · A → conclude P (order reversed)
        let assumption = Formula::parse("~P").unwrap();
        let derived = Formula::parse("~A & A").unwrap();
        let expected = Formula::parse("P").unwrap();

        let conclusion = ProofTechnique::IndirectProof
            .get_conclusion(&assumption, &derived)
            .unwrap();
        assert_eq!(conclusion, expected);
    }

    #[test]
    fn test_indirect_proof_requires_contradiction() {
        let assumption = Formula::parse("~P").unwrap();
        let derived = Formula::parse("Q").unwrap(); // Not a contradiction

        let conclusion = ProofTechnique::IndirectProof.get_conclusion(&assumption, &derived);
        assert!(conclusion.is_none());
    }

    #[test]
    fn test_indirect_proof_non_negated_assumption() {
        // IP can also handle: Assume P, derive ⊥ → conclude ~P
        let assumption = Formula::parse("P").unwrap();
        let derived = Formula::Contradiction;
        let expected = Formula::parse("~P").unwrap();

        let conclusion = ProofTechnique::IndirectProof
            .get_conclusion(&assumption, &derived)
            .unwrap();
        assert_eq!(conclusion, expected);
    }

    #[test]
    fn test_indirect_proof_complex_formula() {
        // Test with complex formula: Assume (P ∨ Q) . R, derive ⊥ → conclude ~[(P ∨ Q) . R]
        let assumption = Formula::parse("(P | Q) & R").unwrap();
        let derived = Formula::Contradiction;

        let conclusion = ProofTechnique::IndirectProof
            .get_conclusion(&assumption, &derived)
            .unwrap();

        // Should be ~[(P ∨ Q) . R]
        if let Formula::Not(inner) = &conclusion {
            assert_eq!(**inner, assumption);
        } else {
            panic!("Expected negation");
        }
    }

    #[test]
    fn test_is_contradiction() {
        // ⊥ is a contradiction
        assert!(is_contradiction(&Formula::Contradiction));

        // P · ~P is a contradiction
        let p_and_not_p = Formula::parse("P & ~P").unwrap();
        assert!(is_contradiction(&p_and_not_p));

        // ~P · P is a contradiction
        let not_p_and_p = Formula::parse("~P & P").unwrap();
        assert!(is_contradiction(&not_p_and_p));

        // Complex: (A ⊃ B) · ~(A ⊃ B)
        let complex = Formula::parse("(A > B) & ~(A > B)").unwrap();
        assert!(is_contradiction(&complex));

        // User's exact case: ~(R ∨ S) · (R ∨ S)
        let user_case = Formula::parse("~(R | S) & (R | S)").unwrap();
        assert!(is_contradiction(&user_case), "~(R | S) & (R | S) should be a contradiction");

        // P · Q is NOT a contradiction
        let p_and_q = Formula::parse("P & Q").unwrap();
        assert!(!is_contradiction(&p_and_q));

        // P · ~Q is NOT a contradiction (different formulas)
        let p_and_not_q = Formula::parse("P & ~Q").unwrap();
        assert!(!is_contradiction(&p_and_not_q));

        // Just P is NOT a contradiction
        let just_p = Formula::parse("P").unwrap();
        assert!(!is_contradiction(&just_p));
    }
}
