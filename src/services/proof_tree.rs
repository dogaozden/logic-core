use serde::{Deserialize, Serialize};
use crate::models::Formula;

/// Represents a node in a proof tree.
/// Each node either proves a formula directly (Premise/Assumption)
/// or derives it from child nodes via a rule application.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProofNode {
    /// A premise - an undischarged assumption that becomes part of the theorem
    Premise(Formula),

    /// An assumption made for a subproof (CP, IP, NegIntro)
    /// Will be discharged when the subproof closes
    Assumption(Formula),

    /// A derived formula from applying a rule to child nodes
    Derivation {
        /// The formula this node proves
        result: Formula,
        /// Which rule/fragment was applied
        rule: String,
        /// Sub-proofs feeding into this derivation
        children: Vec<ProofNode>,
        /// For subproof rules (CP, IP, NegIntro): the assumption made
        assumption: Option<Formula>,
    },
}

impl ProofNode {
    /// Create a new premise node
    pub fn premise(formula: Formula) -> Self {
        ProofNode::Premise(formula)
    }

    /// Create a new assumption node
    pub fn assumption(formula: Formula) -> Self {
        ProofNode::Assumption(formula)
    }

    /// Create a new derivation node
    pub fn derivation(
        result: Formula,
        rule: &str,
        children: Vec<ProofNode>,
        assumption: Option<Formula>,
    ) -> Self {
        ProofNode::Derivation {
            result,
            rule: rule.to_string(),
            children,
            assumption,
        }
    }

    /// Get the formula this node proves/establishes
    pub fn formula(&self) -> &Formula {
        match self {
            ProofNode::Premise(f) => f,
            ProofNode::Assumption(f) => f,
            ProofNode::Derivation { result, .. } => result,
        }
    }

    /// Check if this node is a premise
    pub fn is_premise(&self) -> bool {
        matches!(self, ProofNode::Premise(_))
    }

    /// Check if this node is an assumption
    pub fn is_assumption(&self) -> bool {
        matches!(self, ProofNode::Assumption(_))
    }

    /// Get the rule name if this is a derivation
    pub fn rule_name(&self) -> Option<&str> {
        match self {
            ProofNode::Derivation { rule, .. } => Some(rule),
            _ => None,
        }
    }

    /// Get children if this is a derivation
    pub fn children(&self) -> &[ProofNode] {
        match self {
            ProofNode::Derivation { children, .. } => children,
            _ => &[],
        }
    }

    /// Count total nodes in the tree
    pub fn node_count(&self) -> usize {
        match self {
            ProofNode::Premise(_) | ProofNode::Assumption(_) => 1,
            ProofNode::Derivation { children, .. } => {
                1 + children.iter().map(|c| c.node_count()).sum::<usize>()
            }
        }
    }

    /// Count derivation nodes (inference steps) in the tree
    pub fn derivation_count(&self) -> usize {
        match self {
            ProofNode::Premise(_) | ProofNode::Assumption(_) => 0,
            ProofNode::Derivation { children, .. } => {
                1 + children.iter().map(|c| c.derivation_count()).sum::<usize>()
            }
        }
    }

    /// Calculate maximum nesting depth (subproof depth)
    pub fn nesting_depth(&self) -> usize {
        match self {
            ProofNode::Premise(_) | ProofNode::Assumption(_) => 0,
            ProofNode::Derivation { rule, children, .. } => {
                let child_depth = children.iter()
                    .map(|c| c.nesting_depth())
                    .max()
                    .unwrap_or(0);

                // Rules that create subproofs add nesting
                if is_nesting_rule(rule) {
                    1 + child_depth
                } else {
                    child_depth
                }
            }
        }
    }

    /// Collect all undischarged premises (leaves that aren't in discharged scopes)
    pub fn collect_premises(&self) -> Vec<Formula> {
        let mut premises = Vec::new();
        self.collect_premises_inner(&mut premises);
        premises
    }

    fn collect_premises_inner(&self, premises: &mut Vec<Formula>) {
        match self {
            ProofNode::Premise(f) => {
                if !premises.contains(f) {
                    premises.push(f.clone());
                }
            }
            ProofNode::Assumption(_) => {
                // Assumptions are discharged by their enclosing subproof
                // Don't include them as premises
            }
            ProofNode::Derivation { children, .. } => {
                for child in children {
                    child.collect_premises_inner(premises);
                }
            }
        }
    }

    /// Pretty print the proof tree for debugging
    pub fn pretty_print(&self, indent: usize) -> String {
        let indent_str = "  ".repeat(indent);
        match self {
            ProofNode::Premise(f) => {
                format!("{}Premise: {}", indent_str, f.display_string())
            }
            ProofNode::Assumption(f) => {
                format!("{}Assumption: {}", indent_str, f.display_string())
            }
            ProofNode::Derivation { result, rule, children, assumption } => {
                let mut lines = Vec::new();

                // Print the derivation header
                if let Some(assume) = assumption {
                    lines.push(format!("{}[Assume {}]", indent_str, assume.display_string()));
                }

                // Print children
                for child in children {
                    lines.push(child.pretty_print(indent + 1));
                }

                // Print the conclusion
                lines.push(format!("{}{}: {}", indent_str, rule, result.display_string()));

                lines.join("\n")
            }
        }
    }
}

/// Check if a rule name represents a nesting (subproof-creating) rule
fn is_nesting_rule(rule: &str) -> bool {
    matches!(rule, "CP" | "IP" | "NegIntro" | "CaseSplit")
}

/// Error type for degenerate proof detection
#[derive(Debug, Clone)]
pub enum DegenerateProofError {
    /// Premises are semantically contradictory (no row where all are true)
    ContradictoryPremises,
    /// Conclusion is a tautology (always true regardless of premises)
    TautologicalConclusion,
    /// A premise is a tautology (always true, contributes nothing)
    TautologicalPremise,
    /// A single premise alone entails the conclusion
    SinglePremiseEntails,
    /// The negation of the conclusion is semantically available as a premise
    NegationOfConclusionAvailable,
    /// A conditional conclusion is trivially provable via explosion
    ConditionalTrivialViaExplosion,
    /// Premises contain semantically equivalent formulas
    RedundantPremises,
    /// At least one premise is unnecessary for the entailment
    UnnecessaryPremise,
    /// The premises do not semantically entail the conclusion
    InvalidTheorem,
    /// The proof is too easy (can be solved in fewer than min_steps)
    TooEasy { min_steps: usize, actual_steps: usize },
    /// Theorem doesn't require subproof rules (CP/IP) - too easy for hard/expert
    NoSubproofRequired,
    /// Theorem doesn't force conditional proof (conclusion is A⊃B but premises entail B)
    DoesNotForceCP,
    /// Theorem doesn't force case split (no disjunction without available negation)
    DoesNotForceCaseSplit,
    /// Theorem doesn't force indirect proof
    DoesNotForceIP,
}

impl std::fmt::Display for DegenerateProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DegenerateProofError::ContradictoryPremises => {
                write!(f, "Premises are contradictory (no interpretation makes all true)")
            }
            DegenerateProofError::TautologicalConclusion => {
                write!(f, "Conclusion is a tautology (no proof needed)")
            }
            DegenerateProofError::TautologicalPremise => {
                write!(f, "A premise is a tautology (always true, contributes nothing)")
            }
            DegenerateProofError::SinglePremiseEntails => {
                write!(f, "A single premise entails the conclusion (trivial proof)")
            }
            DegenerateProofError::NegationOfConclusionAvailable => {
                write!(f, "Negation of conclusion is available as a premise")
            }
            DegenerateProofError::ConditionalTrivialViaExplosion => {
                write!(f, "Conditional trivially provable via explosion")
            }
            DegenerateProofError::RedundantPremises => {
                write!(f, "Redundant (semantically equivalent) premises detected")
            }
            DegenerateProofError::UnnecessaryPremise => {
                write!(f, "At least one premise is unnecessary for the proof")
            }
            DegenerateProofError::InvalidTheorem => {
                write!(f, "Invalid theorem: premises do not entail conclusion")
            }
            DegenerateProofError::TooEasy { min_steps, actual_steps } => {
                write!(f, "Proof too easy: solvable in {} steps, need at least {}", actual_steps, min_steps)
            }
            DegenerateProofError::NoSubproofRequired => {
                write!(f, "Theorem solvable without subproof rules (CP/IP required for this difficulty)")
            }
            DegenerateProofError::DoesNotForceCP => {
                write!(f, "Theorem doesn't force conditional proof (conclusion A⊃B but premises entail B)")
            }
            DegenerateProofError::DoesNotForceCaseSplit => {
                write!(f, "Theorem doesn't force case split (no disjunction requires it)")
            }
            DegenerateProofError::DoesNotForceIP => {
                write!(f, "Theorem doesn't force indirect proof")
            }
        }
    }
}


/// Represents a complete proof tree with metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofTree {
    /// The root node of the proof tree
    pub root: ProofNode,
    /// Number of fragments/rules used
    pub fragment_count: usize,
    /// Maximum nesting depth achieved
    pub max_nesting: usize,
}

impl ProofTree {
    pub fn new(root: ProofNode) -> Self {
        let fragment_count = root.derivation_count();
        let max_nesting = root.nesting_depth();
        Self {
            root,
            fragment_count,
            max_nesting,
        }
    }

    /// Get the conclusion (what the proof proves)
    pub fn conclusion(&self) -> &Formula {
        self.root.formula()
    }

    /// Get the premises (undischarged assumptions)
    pub fn premises(&self) -> Vec<Formula> {
        self.root.collect_premises()
    }

    /// Check if this proof tree produces a degenerate theorem
    /// Uses semantic (truth table) validation
    pub fn validate(&self) -> Result<(), DegenerateProofError> {
        let premises = self.premises();
        let conclusion = self.conclusion();
        super::truth_table::validate_theorem(&premises, conclusion)
    }

    /// Check if this proof tree is valid with difficulty requirements
    /// min_proof_steps: minimum number of steps the shortest proof should require
    /// require_cp: if true, theorem must force conditional proof
    /// require_case_split: if true, theorem must force case split
    /// require_ip: if true, theorem must force indirect proof
    pub fn validate_with_difficulty(
        &self,
        min_proof_steps: usize,
        require_cp: bool,
        require_case_split: bool,
        require_ip: bool,
    ) -> Result<(), DegenerateProofError> {
        let premises = self.premises();
        let conclusion = self.conclusion();
        super::truth_table::validate_theorem_with_difficulty(
            &premises,
            conclusion,
            Some(min_proof_steps),
            require_cp,
            require_case_split,
            require_ip,
        )
    }

    /// Check if this proof tree is valid (non-degenerate)
    pub fn is_valid(&self) -> bool {
        self.validate().is_ok()
    }

    /// Check if this proof tree is valid with difficulty requirements
    pub fn is_valid_with_difficulty(
        &self,
        min_proof_steps: usize,
        require_cp: bool,
        require_case_split: bool,
        require_ip: bool,
    ) -> bool {
        self.validate_with_difficulty(min_proof_steps, require_cp, require_case_split, require_ip).is_ok()
    }

    /// Pretty print the entire proof tree
    pub fn pretty_print(&self) -> String {
        let premises = self.premises();
        let premises_str = if premises.is_empty() {
            "∅".to_string()
        } else {
            premises.iter()
                .map(|p| p.display_string())
                .collect::<Vec<_>>()
                .join(", ")
        };

        format!(
            "Theorem: {} ⊢ {}\n\
             Fragments: {}, Nesting: {}\n\n\
             Proof Tree:\n{}",
            premises_str,
            self.conclusion().display_string(),
            self.fragment_count,
            self.max_nesting,
            self.root.pretty_print(0)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::services::truth_table;

    fn atom(name: &str) -> Formula {
        Formula::Atom(name.to_string())
    }

    fn implies(a: Formula, b: Formula) -> Formula {
        Formula::Implies(Box::new(a), Box::new(b))
    }

    #[test]
    fn test_premise_node() {
        let p = atom("P");
        let node = ProofNode::premise(p.clone());
        assert!(node.is_premise());
        assert_eq!(node.formula(), &p);
        assert_eq!(node.node_count(), 1);
        assert_eq!(node.derivation_count(), 0);
    }

    #[test]
    fn test_simple_derivation() {
        // MP: P, P -> Q |- Q
        let p = atom("P");
        let q = atom("Q");
        let p_implies_q = implies(p.clone(), q.clone());

        let node = ProofNode::derivation(
            q.clone(),
            "MP",
            vec![
                ProofNode::premise(p_implies_q),
                ProofNode::premise(p),
            ],
            None,
        );

        assert_eq!(node.derivation_count(), 1);
        assert_eq!(node.nesting_depth(), 0);

        let premises = node.collect_premises();
        assert_eq!(premises.len(), 2);
    }

    #[test]
    fn test_cp_nesting() {
        // CP: |- P -> P (assume P, reiterate P, close)
        let p = atom("P");

        // Inside CP: just the assumption itself serves as proof of P
        let node = ProofNode::derivation(
            implies(p.clone(), p.clone()),
            "CP",
            vec![
                ProofNode::assumption(p.clone()), // The assumption proves P
            ],
            Some(p.clone()),
        );

        assert_eq!(node.derivation_count(), 1);
        assert_eq!(node.nesting_depth(), 1);

        // No premises - assumption is discharged
        let premises = node.collect_premises();
        assert_eq!(premises.len(), 0);
    }

    #[test]
    fn test_proof_tree() {
        let p = atom("P");
        let q = atom("Q");

        let root = ProofNode::derivation(
            q.clone(),
            "MP",
            vec![
                ProofNode::premise(implies(p.clone(), q.clone())),
                ProofNode::premise(p),
            ],
            None,
        );

        let tree = ProofTree::new(root);
        assert_eq!(tree.fragment_count, 1);
        assert_eq!(tree.max_nesting, 0);
        assert_eq!(tree.premises().len(), 2);
        assert_eq!(tree.conclusion(), &q);
    }

    #[test]
    fn test_contradictory_premises_detected() {
        let p = atom("P");
        let not_p = Formula::Not(Box::new(p.clone()));
        let q = atom("Q");

        // P, ~P |- Q should be detected as degenerate
        let premises = vec![p.clone(), not_p.clone()];
        let result = truth_table::validate_theorem(&premises, &q);

        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), DegenerateProofError::ContradictoryPremises));
    }

    #[test]
    fn test_valid_premises_pass() {
        let p = atom("P");
        let q = atom("Q");
        let p_implies_q = implies(p.clone(), q.clone());

        // P, P -> Q |- Q is valid (not degenerate)
        let premises = vec![p, p_implies_q];
        let result = truth_table::validate_theorem(&premises, &q);

        assert!(result.is_ok());
    }

    #[test]
    fn test_single_premise_entails_detected() {
        let p = atom("P");
        let q = atom("Q");

        // P, Q |- P is trivial (single premise entails)
        let premises = vec![p.clone(), q];
        let result = truth_table::validate_theorem(&premises, &p);

        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), DegenerateProofError::SinglePremiseEntails));
    }

    #[test]
    fn test_tautological_conclusion_detected() {
        let p = atom("P");
        let q = atom("Q");
        // P | ~P is a tautology
        let tautology = Formula::Or(
            Box::new(p.clone()),
            Box::new(Formula::Not(Box::new(p.clone()))),
        );

        // Q |- P | ~P should be rejected (tautological conclusion)
        let premises = vec![q.clone()];
        let result = truth_table::validate_theorem(&premises, &tautology);

        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), DegenerateProofError::TautologicalConclusion));
    }

    #[test]
    fn test_self_implication_tautology() {
        let p = atom("P");

        // P -> P is a tautology
        let self_impl = implies(p.clone(), p.clone());
        assert!(truth_table::is_tautology(&self_impl));

        // P -> Q is not a tautology
        let q = atom("Q");
        let normal_impl = implies(p, q);
        assert!(!truth_table::is_tautology(&normal_impl));
    }

    #[test]
    fn test_nested_conjunction_contradiction() {
        let p = atom("P");
        let t = atom("T");
        let q = atom("Q");
        let not_p = Formula::Not(Box::new(p.clone()));

        // T . P contains P, and ~P is a premise
        // This should be caught as a contradiction (semantically)
        let t_and_p = Formula::And(Box::new(t.clone()), Box::new(p.clone()));
        let premises = vec![t_and_p, not_p.clone()];

        let result = truth_table::validate_theorem(&premises, &q);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), DegenerateProofError::ContradictoryPremises));
    }

    #[test]
    fn test_deeply_nested_conjunction_contradiction() {
        let p = atom("P");
        let q = atom("Q");
        let r = atom("R");
        let not_p = Formula::Not(Box::new(p.clone()));

        // (Q . (R . P)) contains P deeply nested
        let r_and_p = Formula::And(Box::new(r.clone()), Box::new(p.clone()));
        let nested = Formula::And(Box::new(q.clone()), Box::new(r_and_p));

        let premises = vec![nested, not_p.clone()];
        let goal = atom("S");

        let result = truth_table::validate_theorem(&premises, &goal);
        assert!(result.is_err(), "Should detect contradiction even when P is deeply nested");
    }

    #[test]
    fn test_proof_tree_validation() {
        let p = atom("P");
        let not_p = Formula::Not(Box::new(p.clone()));
        let q = atom("Q");

        // Build a tree with contradictory premises
        let root = ProofNode::derivation(
            q.clone(),
            "DS", // Doesn't matter, just need premises
            vec![
                ProofNode::premise(p.clone()),
                ProofNode::premise(not_p.clone()),
            ],
            None,
        );

        let tree = ProofTree::new(root);
        assert!(!tree.is_valid());
        assert!(tree.validate().is_err());
    }

    #[test]
    fn test_semantic_double_negation_entailment() {
        // P |- ~~P should be detected as single premise entails (semantic equivalence)
        let p = atom("P");
        let not_not_p = Formula::Not(Box::new(Formula::Not(Box::new(p.clone()))));

        let premises = vec![p.clone()];
        let result = truth_table::validate_theorem(&premises, &not_not_p);

        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), DegenerateProofError::SinglePremiseEntails));
    }

    // === New Edge Case Tests ===

    #[test]
    fn test_deeply_nested_subproofs_count_correctly() {
        // Build a tree with multiple levels of nesting
        // CP { CP { MP } }
        let p = atom("P");
        let q = atom("Q");
        let _r = atom("R"); // Available for more complex tests

        // Inner CP: |- Q -> Q
        let inner_cp = ProofNode::derivation(
            implies(q.clone(), q.clone()),
            "CP",
            vec![ProofNode::assumption(q.clone())],
            Some(q.clone()),
        );

        // Outer CP: |- P -> (Q -> Q)
        let outer_cp = ProofNode::derivation(
            implies(p.clone(), implies(q.clone(), q.clone())),
            "CP",
            vec![
                ProofNode::assumption(p.clone()),
                inner_cp,
            ],
            Some(p.clone()),
        );

        // Nesting depth should be 2 (two CP rules)
        assert_eq!(outer_cp.nesting_depth(), 2);

        // Total derivation count should be 2
        assert_eq!(outer_cp.derivation_count(), 2);
    }

    #[test]
    fn test_validate_with_difficulty_min_steps_boundary() {
        // Create a simple tree that has a known number of steps
        let p = atom("P");
        let q = atom("Q");

        // P, P -> Q |- Q (1 step - MP)
        let root = ProofNode::derivation(
            q.clone(),
            "MP",
            vec![
                ProofNode::premise(implies(p.clone(), q.clone())),
                ProofNode::premise(p),
            ],
            None,
        );

        let tree = ProofTree::new(root);

        // Should pass with min_steps = 1
        assert!(tree.is_valid_with_difficulty(1, false, false, false));

        // Basic validation should still pass
        assert!(tree.is_valid());
    }

    #[test]
    fn test_validate_with_difficulty_requires_cp_true() {
        // P -> Q, Q -> R |- P -> R
        // This requires CP because conclusion is conditional
        let p = atom("P");
        let q = atom("Q");
        let r = atom("R");

        let root = ProofNode::derivation(
            implies(p.clone(), r.clone()),
            "CP",
            vec![
                ProofNode::derivation(
                    r.clone(),
                    "HS",
                    vec![
                        ProofNode::premise(implies(p.clone(), q.clone())),
                        ProofNode::premise(implies(q, r.clone())),
                        ProofNode::assumption(p.clone()),
                    ],
                    None,
                ),
            ],
            Some(p),
        );

        let tree = ProofTree::new(root);

        // The tree should have nesting >= 1 due to CP
        assert!(tree.max_nesting >= 1);
    }

    #[test]
    fn test_pretty_print_deep_tree() {
        // Build a moderately complex tree and verify pretty_print doesn't panic
        let p = atom("P");
        let q = atom("Q");

        let inner = ProofNode::derivation(
            q.clone(),
            "MP",
            vec![
                ProofNode::premise(implies(p.clone(), q.clone())),
                ProofNode::premise(p.clone()),
            ],
            None,
        );

        let outer = ProofNode::derivation(
            implies(p.clone(), q.clone()),
            "CP",
            vec![
                ProofNode::assumption(p.clone()),
                inner,
            ],
            Some(p),
        );

        let tree = ProofTree::new(outer);
        let output = tree.pretty_print();

        // Verify output contains expected elements
        assert!(output.contains("Theorem:"));
        assert!(output.contains("Fragments:"));
        assert!(output.contains("Nesting:"));
        assert!(output.contains("Proof Tree:"));
        assert!(output.contains("CP"));
        assert!(output.contains("MP"));
        assert!(output.contains("Premise:"));
    }
}
