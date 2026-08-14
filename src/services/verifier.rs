use crate::models::{
    Formula, Proof, ProofLine, Justification,
    rules::{InferenceRule, EquivalenceRule, ProofTechnique},
};

/// Result of proof verification
#[derive(Debug, Clone)]
pub struct VerificationResult {
    pub is_valid: bool,
    pub message: Option<String>,
}

impl VerificationResult {
    pub fn valid() -> Self {
        Self {
            is_valid: true,
            message: None,
        }
    }

    pub fn invalid(message: impl Into<String>) -> Self {
        Self {
            is_valid: false,
            message: Some(message.into()),
        }
    }
}

/// Verifies proof lines and justifications
pub struct ProofVerifier;

impl ProofVerifier {
    /// Verify a single line in the context of the proof
    pub fn verify_line(line: &ProofLine, proof: &Proof) -> VerificationResult {
        match &line.justification {
            Justification::Premise => Self::verify_premise(line, proof),
            Justification::Assumption { technique } => {
                Self::verify_assumption(line, *technique, proof)
            }
            Justification::Inference { rule, lines } => {
                Self::verify_inference(line, *rule, lines, proof)
            }
            Justification::Equivalence { rule, line: ref_line } => {
                Self::verify_equivalence(line, *rule, *ref_line, proof)
            }
            Justification::SubproofConclusion {
                technique,
                subproof_start,
                subproof_end,
            } => Self::verify_subproof_conclusion(
                line,
                *technique,
                *subproof_start,
                *subproof_end,
                proof,
            ),
        }
    }

    fn verify_premise(line: &ProofLine, proof: &Proof) -> VerificationResult {
        // Check that this formula is actually a premise of the theorem
        if proof.theorem.premises.contains(&line.formula) {
            VerificationResult::valid()
        } else {
            VerificationResult::invalid("Formula is not a premise of the theorem")
        }
    }

    fn verify_assumption(
        _line: &ProofLine,
        _technique: ProofTechnique,
        _proof: &Proof,
    ) -> VerificationResult {
        // Assumptions are always valid when opening a subproof
        // The technique just indicates the purpose
        VerificationResult::valid()
    }

    fn verify_inference(
        line: &ProofLine,
        rule: InferenceRule,
        referenced_lines: &[usize],
        proof: &Proof,
    ) -> VerificationResult {
        // Check correct number of premises
        if referenced_lines.len() != rule.premise_count() {
            return VerificationResult::invalid(format!(
                "{} requires {} premise(s), but {} were provided",
                rule.name(),
                rule.premise_count(),
                referenced_lines.len()
            ));
        }

        // Check all referenced lines exist and are accessible
        let mut premises: Vec<&Formula> = Vec::new();
        for &ref_line in referenced_lines {
            if ref_line >= line.line_number {
                return VerificationResult::invalid(format!(
                    "Cannot reference line {} from line {} (must reference earlier lines)",
                    ref_line, line.line_number
                ));
            }

            if !proof.is_line_accessible(line.line_number, ref_line) {
                return VerificationResult::invalid(format!(
                    "Line {} is not accessible from line {} (different scope)",
                    ref_line, line.line_number
                ));
            }

            match proof.get_line(ref_line) {
                Some(ref_proof_line) => {
                    if !ref_proof_line.is_valid {
                        return VerificationResult::invalid(format!(
                            "Referenced line {} is invalid",
                            ref_line
                        ));
                    }
                    premises.push(&ref_proof_line.formula);
                }
                None => {
                    return VerificationResult::invalid(format!(
                        "Referenced line {} does not exist",
                        ref_line
                    ));
                }
            }
        }

        // Apply the rule and check if the conclusion matches
        // For rules that need additional formula input, we extract it from the conclusion
        let additional = if rule.requires_formula_input() {
            // For disjunction introduction, the additional formula is in the conclusion
            match &line.formula {
                Formula::Or(left, right) => {
                    if premises.len() == 1 {
                        if premises[0] == left.as_ref() {
                            Some(right.as_ref())
                        } else if premises[0] == right.as_ref() {
                            Some(left.as_ref())
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            }
        } else {
            None
        };

        if rule.verify(&premises, &line.formula, additional) {
            VerificationResult::valid()
        } else {
            VerificationResult::invalid(format!(
                "The formula does not follow from the given premises using {}",
                rule.name()
            ))
        }
    }

    fn verify_equivalence(
        line: &ProofLine,
        rule: EquivalenceRule,
        ref_line: usize,
        proof: &Proof,
    ) -> VerificationResult {
        // Check reference line exists and is accessible
        if ref_line >= line.line_number {
            return VerificationResult::invalid(format!(
                "Cannot reference line {} from line {} (must reference earlier lines)",
                ref_line, line.line_number
            ));
        }

        if !proof.is_line_accessible(line.line_number, ref_line) {
            return VerificationResult::invalid(format!(
                "Line {} is not accessible from line {} (different scope)",
                ref_line, line.line_number
            ));
        }

        let source_line = match proof.get_line(ref_line) {
            Some(l) => l,
            None => {
                return VerificationResult::invalid(format!(
                    "Referenced line {} does not exist",
                    ref_line
                ));
            }
        };

        if !source_line.is_valid {
            return VerificationResult::invalid(format!(
                "Referenced line {} is invalid",
                ref_line
            ));
        }

        // Check if the target formula can be derived from the source using this rule
        if Self::is_valid_equivalence_application(&source_line.formula, &line.formula, rule) {
            VerificationResult::valid()
        } else {
            // Check for case-sensitivity issues to provide a better error message
            if Self::is_valid_equivalence_application_case_insensitive(&source_line.formula, &line.formula, rule) {
                return VerificationResult::invalid(format!(
                    "Cannot derive the formula using {}. Note: Propositional logic is case-sensitive (e.g., 'P' vs 'p'). Check your casing.",
                    rule.name()
                ));
            }

            VerificationResult::invalid(format!(
                "Cannot derive the formula from line {} using {}",
                ref_line,
                rule.name()
            ))
        }
    }

    fn is_valid_equivalence_application_case_insensitive(source: &Formula, target: &Formula, rule: EquivalenceRule) -> bool {
        // Convert both to a canonical lowercase representation for comparison
        let lowercase_source = Self::to_lowercase_formula(source);
        let lowercase_target = Self::to_lowercase_formula(target);
        
        // This is a bit complex because we need to check if the rule applies to the lowercase versions
        // and if those transformed versions match the lowercase target.
        let top_level_forms = rule.equivalent_forms(&lowercase_source);
        if top_level_forms.iter().any(|f| Self::to_lowercase_formula(f) == lowercase_target) {
            return true;
        }

        // Check subformulas (lowercase)
        for subformula in lowercase_source.subformulas() {
            for equivalent in rule.equivalent_forms(&subformula) {
                let transformed = Self::replace_subformula(&lowercase_source, &subformula, &equivalent);
                if Self::to_lowercase_formula(&transformed) == lowercase_target {
                    return true;
                }
            }
        }
        false
    }

    fn to_lowercase_formula(formula: &Formula) -> Formula {
        match formula {
            Formula::Atom(name) => Formula::Atom(name.to_lowercase()),
            Formula::Not(inner) => Formula::Not(Box::new(Self::to_lowercase_formula(inner))),
            Formula::And(left, right) => Formula::And(
                Box::new(Self::to_lowercase_formula(left)),
                Box::new(Self::to_lowercase_formula(right)),
            ),
            Formula::Or(left, right) => Formula::Or(
                Box::new(Self::to_lowercase_formula(left)),
                Box::new(Self::to_lowercase_formula(right)),
            ),
            Formula::Implies(left, right) => Formula::Implies(
                Box::new(Self::to_lowercase_formula(left)),
                Box::new(Self::to_lowercase_formula(right)),
            ),
            Formula::Biconditional(left, right) => Formula::Biconditional(
                Box::new(Self::to_lowercase_formula(left)),
                Box::new(Self::to_lowercase_formula(right)),
            ),
            Formula::Contradiction => Formula::Contradiction,
        }
    }

    fn is_valid_equivalence_application(source: &Formula, target: &Formula, rule: EquivalenceRule) -> bool {
        // First check if the transformation applies at the top level
        let top_level_forms = rule.equivalent_forms(source);
        if top_level_forms.contains(target) {
            return true;
        }

        // Check if transformation can be applied to any subformula
        Self::check_subformula_equivalence(source, target, rule)
    }

    fn check_subformula_equivalence(source: &Formula, target: &Formula, rule: EquivalenceRule) -> bool {
        // Try to find a subformula in source that can be transformed to match target
        for subformula in source.subformulas() {
            for equivalent in rule.equivalent_forms(&subformula) {
                // Try replacing the subformula with its equivalent
                let transformed = Self::replace_subformula(source, &subformula, &equivalent);
                if transformed == *target {
                    return true;
                }
            }
        }
        false
    }

    fn replace_subformula(formula: &Formula, target: &Formula, replacement: &Formula) -> Formula {
        if formula == target {
            return replacement.clone();
        }

        match formula {
            Formula::Atom(_) | Formula::Contradiction => formula.clone(),
            Formula::Not(inner) => {
                Formula::Not(Box::new(Self::replace_subformula(inner, target, replacement)))
            }
            Formula::And(left, right) => Formula::And(
                Box::new(Self::replace_subformula(left, target, replacement)),
                Box::new(Self::replace_subformula(right, target, replacement)),
            ),
            Formula::Or(left, right) => Formula::Or(
                Box::new(Self::replace_subformula(left, target, replacement)),
                Box::new(Self::replace_subformula(right, target, replacement)),
            ),
            Formula::Implies(left, right) => Formula::Implies(
                Box::new(Self::replace_subformula(left, target, replacement)),
                Box::new(Self::replace_subformula(right, target, replacement)),
            ),
            Formula::Biconditional(left, right) => Formula::Biconditional(
                Box::new(Self::replace_subformula(left, target, replacement)),
                Box::new(Self::replace_subformula(right, target, replacement)),
            ),
        }
    }

    fn verify_subproof_conclusion(
        line: &ProofLine,
        technique: ProofTechnique,
        subproof_start: usize,
        subproof_end: usize,
        proof: &Proof,
    ) -> VerificationResult {
        // Check subproof lines exist
        let start_line = match proof.get_line(subproof_start) {
            Some(l) => l,
            None => {
                return VerificationResult::invalid(format!(
                    "Subproof start line {} does not exist",
                    subproof_start
                ));
            }
        };

        let end_line = match proof.get_line(subproof_end) {
            Some(l) => l,
            None => {
                return VerificationResult::invalid(format!(
                    "Subproof end line {} does not exist",
                    subproof_end
                ));
            }
        };

        // Verify the start line is an assumption
        let assumption_technique = match &start_line.justification {
            Justification::Assumption { technique } => *technique,
            _ => {
                return VerificationResult::invalid(format!(
                    "Line {} is not an assumption",
                    subproof_start
                ));
            }
        };

        // Check the technique matches
        if assumption_technique != technique {
            return VerificationResult::invalid(format!(
                "Assumption technique ({}) does not match conclusion technique ({})",
                assumption_technique.name(),
                technique.name()
            ));
        }

        // Check the subproof is accessible (must have just been closed)
        if !proof.scope_manager.is_subproof_accessible(line.line_number, subproof_start, subproof_end) {
            return VerificationResult::invalid(format!(
                "Subproof lines {}-{} are not accessible from line {}",
                subproof_start, subproof_end, line.line_number
            ));
        }

        // Verify the conclusion follows from the technique
        let assumption = &start_line.formula;
        let derived = &end_line.formula;

        if technique.verify_conclusion(assumption, derived, &line.formula) {
            VerificationResult::valid()
        } else {
            VerificationResult::invalid(format!(
                "The conclusion does not follow from the subproof using {}",
                technique.name()
            ))
        }
    }

    /// Verify all lines in a proof
    pub fn verify_proof(proof: &mut Proof) {
        for i in 0..proof.lines.len() {
            let line = &proof.lines[i];
            let result = Self::verify_line(line, proof);

            // Update the line's validity
            let line = &mut proof.lines[i];
            line.is_valid = result.is_valid;
            line.validation_message = result.message;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::theorem::{Theorem, Difficulty};

    // Helper functions
    fn atom(name: &str) -> Formula {
        Formula::Atom(name.to_string())
    }

    fn not(f: Formula) -> Formula {
        Formula::Not(Box::new(f))
    }

    #[allow(dead_code)]
    fn and(a: Formula, b: Formula) -> Formula {
        Formula::And(Box::new(a), Box::new(b))
    }

    fn or(a: Formula, b: Formula) -> Formula {
        Formula::Or(Box::new(a), Box::new(b))
    }

    fn implies(a: Formula, b: Formula) -> Formula {
        Formula::Implies(Box::new(a), Box::new(b))
    }

    fn make_mp_theorem() -> Theorem {
        Theorem::new(
            vec![
                Formula::parse("P -> Q").unwrap(),
                Formula::parse("P").unwrap(),
            ],
            Formula::parse("Q").unwrap(),
            Difficulty::Easy,
            None,
            Some("Test MP".to_string()),
        )
    }

    fn make_cd_theorem() -> Theorem {
        // Constructive Dilemma: (P -> Q) & (R -> S), P | R ⊢ Q | S
        Theorem::new(
            vec![
                Formula::parse("(P -> Q) & (R -> S)").unwrap(),
                Formula::parse("P | R").unwrap(),
            ],
            Formula::parse("Q | S").unwrap(),
            Difficulty::Medium,
            None,
            Some("Test CD".to_string()),
        )
    }

    // === VerificationResult Construction Tests ===

    #[test]
    fn test_verification_result_valid_has_no_message() {
        let result = VerificationResult::valid();
        assert!(result.is_valid);
        assert!(result.message.is_none());
    }

    #[test]
    fn test_verification_result_invalid_captures_message() {
        let result = VerificationResult::invalid("Test error message");
        assert!(!result.is_valid);
        assert_eq!(result.message, Some("Test error message".to_string()));
    }

    // === Line Reference Error Tests ===

    #[test]
    fn test_verify_inference_forward_reference_rejected() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Try to reference line 4 from line 3 (forward reference)
        proof.add_line(
            atom("Q"),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 4], // line 4 doesn't exist yet
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[2], &proof);
        assert!(!result.is_valid);
        assert!(result.message.as_ref().unwrap().contains("must reference earlier lines"));
    }

    #[test]
    fn test_verify_inference_nonexistent_line_rejected() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Try to reference line 100 which doesn't exist
        proof.add_line(
            atom("Q"),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 100],
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[2], &proof);
        assert!(!result.is_valid);
        // Either "must reference earlier lines" or "does not exist"
        let msg = result.message.as_ref().unwrap();
        assert!(msg.contains("earlier") || msg.contains("exist"));
    }

    #[test]
    fn test_verify_inference_inaccessible_scope_rejected() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Open a subproof
        proof.open_subproof(atom("R"), ProofTechnique::ConditionalProof);

        // Add a line inside the subproof
        proof.add_line(
            atom("Q"),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );

        // Close the subproof
        proof.close_subproof(
            implies(atom("R"), atom("Q")),
            ProofTechnique::ConditionalProof,
        );

        // Try to reference line 4 (inside closed subproof) from line 6
        proof.add_line(
            atom("Q"),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 4], // line 4 is inside closed subproof
            },
        );

        let result = ProofVerifier::verify_line(proof.lines.last().unwrap(), &proof);
        assert!(!result.is_valid);
        assert!(result.message.as_ref().unwrap().contains("not accessible") ||
                result.message.as_ref().unwrap().contains("scope"));
    }

    #[test]
    fn test_verify_inference_invalid_referenced_line_rejected() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Add an invalid line first
        proof.add_line(
            atom("R"), // R doesn't follow from premises
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );

        // Mark it as invalid
        proof.lines[2].is_valid = false;

        // Try to use the invalid line
        proof.add_line(
            or(atom("R"), atom("S")),
            Justification::Inference {
                rule: InferenceRule::Addition,
                lines: vec![3],
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[3], &proof);
        assert!(!result.is_valid);
        assert!(result.message.as_ref().unwrap().contains("invalid"));
    }

    // === Premise Count Validation Tests ===

    #[test]
    fn test_verify_inference_wrong_premise_count_mp() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // MP requires 2 premises, provide only 1
        proof.add_line(
            atom("Q"),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1], // only 1 line, MP needs 2
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[2], &proof);
        assert!(!result.is_valid);
        assert!(result.message.as_ref().unwrap().contains("requires"));
        assert!(result.message.as_ref().unwrap().contains("premise"));
    }

    #[test]
    fn test_verify_inference_wrong_premise_count_cd() {
        let theorem = make_cd_theorem();
        let mut proof = Proof::new(theorem);

        // CD requires 4 premises, provide only 2
        proof.add_line(
            or(atom("Q"), atom("S")),
            Justification::Inference {
                rule: InferenceRule::ConstructiveDilemma,
                lines: vec![1, 2], // only 2 lines, CD needs 4
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[2], &proof);
        assert!(!result.is_valid);
        assert!(result.message.as_ref().unwrap().contains("requires"));
    }

    // === Equivalence Rule Verification Tests ===

    #[test]
    fn test_verify_equivalence_forward_reference_rejected() {
        let theorem = Theorem::new(
            vec![atom("P")],
            not(not(atom("P"))),
            Difficulty::Easy,
            None,
            None,
        );
        let mut proof = Proof::new(theorem);

        // Try to reference line 5 from line 2 (forward reference)
        proof.add_line(
            not(not(atom("P"))),
            Justification::Equivalence {
                rule: EquivalenceRule::DoubleNegation,
                line: 5, // doesn't exist
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[1], &proof);
        assert!(!result.is_valid);
        assert!(result.message.as_ref().unwrap().contains("earlier"));
    }

    #[test]
    fn test_verify_equivalence_case_sensitivity_hint() {
        let theorem = Theorem::new(
            vec![atom("P")],
            atom("p"), // lowercase p - different from P
            Difficulty::Easy,
            None,
            None,
        );
        let mut proof = Proof::new(theorem);

        // Try to derive 'p' from 'P' using DN (should fail with case sensitivity hint)
        proof.add_line(
            atom("p"),
            Justification::Equivalence {
                rule: EquivalenceRule::DoubleNegation,
                line: 1,
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[1], &proof);
        assert!(!result.is_valid);
        // Should provide helpful case-sensitivity message
        let msg = result.message.as_ref().unwrap();
        assert!(msg.contains("case") || msg.contains("Cannot derive"));
    }

    // === Subproof Conclusion Verification Tests ===

    #[test]
    fn test_verify_subproof_conclusion_technique_mismatch() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Open a CP subproof
        proof.open_subproof(atom("R"), ProofTechnique::ConditionalProof);

        // Add a line inside
        proof.add_line(
            atom("Q"),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );

        // Close with wrong technique (IP instead of CP)
        let line_number = proof.next_line_number();
        let depth = proof.current_depth() - 1;

        proof.lines.push(ProofLine::new(
            line_number,
            not(atom("R")), // IP conclusion format
            Justification::SubproofConclusion {
                technique: ProofTechnique::IndirectProof, // Wrong technique!
                subproof_start: 3,
                subproof_end: 4,
            },
            depth,
            None,
        ));

        let result = ProofVerifier::verify_line(proof.lines.last().unwrap(), &proof);
        assert!(!result.is_valid);
        assert!(result.message.as_ref().unwrap().contains("technique") ||
                result.message.as_ref().unwrap().contains("match"));
    }

    #[test]
    fn test_verify_subproof_conclusion_inaccessible_subproof() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Open a subproof
        proof.open_subproof(atom("R"), ProofTechnique::ConditionalProof);
        proof.add_line(
            atom("Q"),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );
        proof.close_subproof(
            implies(atom("R"), atom("Q")),
            ProofTechnique::ConditionalProof,
        );

        // Try to close a non-existent subproof range
        let line_number = proof.next_line_number();
        proof.lines.push(ProofLine::new(
            line_number,
            implies(atom("X"), atom("Y")),
            Justification::SubproofConclusion {
                technique: ProofTechnique::ConditionalProof,
                subproof_start: 100, // doesn't exist
                subproof_end: 101,
            },
            0,
            None,
        ));

        let result = ProofVerifier::verify_line(proof.lines.last().unwrap(), &proof);
        assert!(!result.is_valid);
        assert!(result.message.as_ref().unwrap().contains("does not exist") ||
                result.message.as_ref().unwrap().contains("not accessible"));
    }

    // === Full Proof Verification Tests ===

    #[test]
    fn test_verify_proof_marks_all_lines_valid_or_invalid() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Add valid MP conclusion
        proof.add_line(
            atom("Q"),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );

        // Add invalid line
        proof.add_line(
            atom("R"), // R doesn't follow
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );

        ProofVerifier::verify_proof(&mut proof);

        // Check all lines have been validated
        assert!(proof.lines[0].is_valid); // Premise
        assert!(proof.lines[1].is_valid); // Premise
        assert!(proof.lines[2].is_valid); // Valid MP
        assert!(!proof.lines[3].is_valid); // Invalid - R doesn't follow
        assert!(proof.lines[3].validation_message.is_some());
    }

    #[test]
    fn test_verify_premise() {
        let theorem = make_mp_theorem();
        let proof = Proof::new(theorem);

        let result = ProofVerifier::verify_line(&proof.lines[0], &proof);
        assert!(result.is_valid);
    }

    #[test]
    fn test_verify_modus_ponens() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Add MP conclusion
        proof.add_line(
            Formula::parse("Q").unwrap(),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[2], &proof);
        assert!(result.is_valid);
    }

    #[test]
    fn test_verify_invalid_mp() {
        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Try to derive R (which doesn't follow)
        proof.add_line(
            Formula::parse("R").unwrap(),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[2], &proof);
        assert!(!result.is_valid);
    }

    #[test]
    fn test_verify_double_negation_equiv() {
        let theorem = Theorem::new(
            vec![Formula::parse("P").unwrap()],
            Formula::parse("~~P").unwrap(),
            Difficulty::Easy,
            None,
            None,
        );
        let mut proof = Proof::new(theorem);

        proof.add_line(
            Formula::parse("~~P").unwrap(),
            Justification::Equivalence {
                rule: EquivalenceRule::DoubleNegation,
                line: 1,
            },
        );

        let result = ProofVerifier::verify_line(&proof.lines[1], &proof);
        assert!(result.is_valid);
    }

    #[test]
    fn test_verify_ip_close_with_contradiction_symbol() {
        // Simulates user's scenario:
        // 1. P ⊃ Q           Premise
        // 2. P               Premise
        //    3. ~(R ∨ S) · (R ∨ S)  Assumption (IP)
        //       4. Q               MP 1, 2
        //       5. R ∨ S           Simp 3
        //       6. ~(R ∨ S)        Simp 3
        //       7. ⊥               NegE 5, 6
        // 8. ~[~(R ∨ S) · (R ∨ S)] IP 3-7
        use crate::models::rules::technique::ProofTechnique;

        let theorem = make_mp_theorem();
        let mut proof = Proof::new(theorem);

        // Open IP subproof with assumption ~(R | S) & (R | S)
        let assumption = Formula::parse("~(R | S) & (R | S)").unwrap();
        proof.open_subproof(assumption.clone(), ProofTechnique::IndirectProof);

        // Line 4: Q via MP 1, 2
        proof.add_line(
            Formula::parse("Q").unwrap(),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );

        // Line 5: R | S via Simp 3
        proof.add_line(
            Formula::parse("R | S").unwrap(),
            Justification::Inference {
                rule: InferenceRule::Simplification,
                lines: vec![3],
            },
        );

        // Line 6: ~(R | S) via Simp 3
        proof.add_line(
            Formula::parse("~(R | S)").unwrap(),
            Justification::Inference {
                rule: InferenceRule::Simplification,
                lines: vec![3],
            },
        );

        // Line 7: ⊥ via NegE 5, 6
        proof.add_line(
            Formula::Contradiction,
            Justification::Inference {
                rule: InferenceRule::Contradiction,
                lines: vec![5, 6],
            },
        );

        // Close subproof with conclusion ~[~(R | S) & (R | S)]
        let conclusion = Formula::parse("~[~(R | S) & (R | S)]").unwrap();
        proof.close_subproof(conclusion.clone(), ProofTechnique::IndirectProof);

        // Verify the conclusion line (last line)
        let last_idx = proof.lines.len() - 1;
        let result = ProofVerifier::verify_line(&proof.lines[last_idx], &proof);
        
        if !result.is_valid {
            eprintln!("Verification failed: {:?}", result.message);
            eprintln!("Last line: {:?}", proof.lines[last_idx]);
            eprintln!("Scope manager: {:?}", proof.scope_manager);
        }
        
        assert!(result.is_valid, "IP close verification should succeed. Error: {:?}", result.message);
    }
}
