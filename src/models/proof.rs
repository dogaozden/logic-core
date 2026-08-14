use serde::{Deserialize, Serialize};
use uuid::Uuid;
use super::formula::Formula;
use super::theorem::Theorem;
use super::scope::ScopeManager;
use super::rules::inference::InferenceRule;
use super::rules::equivalence::EquivalenceRule;
use super::rules::technique::ProofTechnique;

/// Justification for a proof line
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum Justification {
    Premise,
    Assumption {
        technique: ProofTechnique,
    },
    Inference {
        rule: InferenceRule,
        lines: Vec<usize>,
    },
    Equivalence {
        rule: EquivalenceRule,
        line: usize,
    },
    SubproofConclusion {
        technique: ProofTechnique,
        subproof_start: usize,
        subproof_end: usize,
    },
}

impl Justification {
    pub fn display_string(&self) -> String {
        match self {
            Justification::Premise => "Premise".to_string(),
            Justification::Assumption { technique } => {
                format!("Assumption ({})", technique.abbreviation())
            }
            Justification::Inference { rule, lines } => {
                let lines_str = lines
                    .iter()
                    .map(|l| l.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{} {}", rule.abbreviation(), lines_str)
            }
            Justification::Equivalence { rule, line } => {
                format!("{} {}", rule.abbreviation(), line)
            }
            Justification::SubproofConclusion {
                technique,
                subproof_start,
                subproof_end,
            } => {
                format!("{} {}-{}", technique.abbreviation(), subproof_start, subproof_end)
            }
        }
    }

    pub fn referenced_lines(&self) -> Vec<usize> {
        match self {
            Justification::Premise => vec![],
            Justification::Assumption { .. } => vec![],
            Justification::Inference { lines, .. } => lines.clone(),
            Justification::Equivalence { line, .. } => vec![*line],
            Justification::SubproofConclusion {
                subproof_start,
                subproof_end,
                ..
            } => vec![*subproof_start, *subproof_end],
        }
    }
}

/// A single line in a proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofLine {
    pub id: String,
    pub line_number: usize,
    pub formula: Formula,
    pub justification: Justification,
    pub depth: usize,
    pub scope_id: Option<String>,
    pub is_valid: bool,
    pub validation_message: Option<String>,
}

impl ProofLine {
    pub fn new(
        line_number: usize,
        formula: Formula,
        justification: Justification,
        depth: usize,
        scope_id: Option<String>,
    ) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            line_number,
            formula,
            justification,
            depth,
            scope_id,
            is_valid: true,
            validation_message: None,
        }
    }

    pub fn set_valid(&mut self, valid: bool, message: Option<String>) {
        self.is_valid = valid;
        self.validation_message = message;
    }
}

/// A complete proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Proof {
    pub id: String,
    pub theorem: Theorem,
    pub lines: Vec<ProofLine>,
    pub scope_manager: ScopeManager,
    pub is_complete: bool,
}

impl Proof {
    pub fn new(theorem: Theorem) -> Self {
        let mut proof = Self {
            id: Uuid::new_v4().to_string(),
            theorem: theorem.clone(),
            lines: Vec::new(),
            scope_manager: ScopeManager::new(),
            is_complete: false,
        };

        // Add premises as initial lines
        for premise in &theorem.premises {
            let line_number = proof.lines.len() + 1;
            proof.lines.push(ProofLine::new(
                line_number,
                premise.clone(),
                Justification::Premise,
                0,
                None,
            ));
        }

        proof
    }

    pub fn current_line_number(&self) -> usize {
        self.lines.len()
    }

    pub fn next_line_number(&self) -> usize {
        self.lines.len() + 1
    }

    pub fn current_depth(&self) -> usize {
        self.scope_manager.current_depth()
    }

    pub fn get_line(&self, line_number: usize) -> Option<&ProofLine> {
        self.lines.iter().find(|l| l.line_number == line_number)
    }

    pub fn get_line_mut(&mut self, line_number: usize) -> Option<&mut ProofLine> {
        self.lines.iter_mut().find(|l| l.line_number == line_number)
    }

    pub fn add_line(&mut self, formula: Formula, justification: Justification) -> &ProofLine {
        let line_number = self.next_line_number();
        let depth = self.current_depth();
        let scope_id = self.scope_manager.current_scope_id();

        let line = ProofLine::new(line_number, formula, justification, depth, scope_id);
        self.lines.push(line);
        self.lines.last().expect("line was just pushed")
    }

    pub fn open_subproof(&mut self, assumption: Formula, technique: ProofTechnique) -> &ProofLine {
        let line_number = self.next_line_number();
        let scope_id = self.scope_manager.open_scope(line_number, assumption.clone(), technique);
        let depth = self.current_depth();

        let line = ProofLine::new(
            line_number,
            assumption,
            Justification::Assumption { technique },
            depth,
            Some(scope_id),
        );
        self.lines.push(line);
        self.lines.last().expect("line was just pushed")
    }

    pub fn close_subproof(&mut self, conclusion: Formula, technique: ProofTechnique) -> Option<&ProofLine> {
        // Find the current scope
        let scope = self.scope_manager.current_scope()?.clone();
        let subproof_start = scope.start_line;

        // The conclusion goes at the parent scope level
        let end_line = self.next_line_number();

        // Close the scope first
        self.scope_manager.close_scope(end_line - 1);

        let depth = self.current_depth();
        let scope_id = self.scope_manager.current_scope_id();

        let line = ProofLine::new(
            end_line,
            conclusion,
            Justification::SubproofConclusion {
                technique,
                subproof_start,
                subproof_end: end_line - 1,
            },
            depth,
            scope_id,
        );
        self.lines.push(line);
        Some(self.lines.last().expect("line was just pushed"))
    }

    pub fn remove_last_line(&mut self) -> Option<ProofLine> {
        // Don't remove premises
        if self.lines.len() <= self.theorem.premises.len() {
            return None;
        }

        let removed = self.lines.pop();

        // If we removed an assumption, we need to remove the scope
        if let Some(ref line) = removed {
            if matches!(line.justification, Justification::Assumption { .. }) {
                self.scope_manager.pop_scope(line.line_number);
            }
        }

        removed
    }

    pub fn is_line_accessible(&self, from_line: usize, to_line: usize) -> bool {
        self.scope_manager.is_accessible(from_line, to_line)
    }

    pub fn check_complete(&mut self) -> bool {
        // Proof is complete if:
        // 1. There are no open scopes
        // 2. The conclusion appears in the proof at depth 0
        // 3. All lines are valid

        if self.scope_manager.has_open_scopes() {
            self.is_complete = false;
            return false;
        }

        let conclusion = &self.theorem.conclusion;
        let has_conclusion = self.lines.iter().any(|l| {
            l.depth == 0 && l.formula == *conclusion && l.is_valid
        });

        let all_valid = self.lines.iter().all(|l| l.is_valid);

        self.is_complete = has_conclusion && all_valid;
        self.is_complete
    }

    /// Get accessible lines from the current position
    pub fn accessible_lines(&self) -> Vec<usize> {
        let current = self.next_line_number();
        (1..current)
            .filter(|&line| self.is_line_accessible(current, line))
            .collect()
    }

    /// Check if current subproof can be auto-closed and return the conclusion
    /// Returns (technique, conclusion_formula) if auto-close is possible
    pub fn get_auto_close_conclusion(&self) -> Option<(ProofTechnique, Formula)> {
        use crate::models::rules::technique::is_contradiction;

        // Get current open scope
        let current_scope = self.scope_manager.current_scope()?;
        let assumption = &current_scope.assumption;
        let technique = current_scope.technique;
        let scope_start = current_scope.start_line;

        if technique.requires_contradiction() {
            // For IP: Search for ANY contradiction within the current subproof scope
            for line in self.lines.iter().rev() {
                // Only consider lines within the current scope
                if line.line_number < scope_start {
                    break;
                }
                // Check if this line is a contradiction
                if is_contradiction(&line.formula) {
                    // Found a contradiction - IP can be closed
                    let conclusion = technique.get_conclusion(assumption, &line.formula)?;
                    return Some((technique, conclusion));
                }
            }
            // No contradiction found in the subproof
            None
        } else {
            // For CP: use the last line within the subproof scope
            let last_line_in_scope = self.lines.iter()
                .rev()
                .find(|l| l.line_number >= scope_start)?;
            let derived = &last_line_in_scope.formula;
            let conclusion = technique.get_conclusion(assumption, derived)?;
            Some((technique, conclusion))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::theorem::Difficulty;

    fn make_simple_theorem() -> Theorem {
        Theorem::new(
            vec![
                Formula::parse("P -> Q").unwrap(),
                Formula::parse("P").unwrap(),
            ],
            Formula::parse("Q").unwrap(),
            Difficulty::Easy,
            None,
            Some("Test".to_string()),
        )
    }

    #[test]
    fn test_new_proof_has_premises() {
        let theorem = make_simple_theorem();
        let proof = Proof::new(theorem);
        assert_eq!(proof.lines.len(), 2);
        assert!(matches!(proof.lines[0].justification, Justification::Premise));
        assert!(matches!(proof.lines[1].justification, Justification::Premise));
    }

    #[test]
    fn test_add_line() {
        let theorem = make_simple_theorem();
        let mut proof = Proof::new(theorem);
        proof.add_line(
            Formula::parse("Q").unwrap(),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );
        assert_eq!(proof.lines.len(), 3);
        assert_eq!(proof.lines[2].line_number, 3);
    }

    #[test]
    fn test_subproof() {
        let theorem = make_simple_theorem();
        let mut proof = Proof::new(theorem);

        // Open a subproof
        proof.open_subproof(Formula::parse("R").unwrap(), ProofTechnique::ConditionalProof);
        assert_eq!(proof.current_depth(), 1);
        assert_eq!(proof.lines.len(), 3);

        // Add a line inside the subproof
        proof.add_line(
            Formula::parse("Q").unwrap(),
            Justification::Inference {
                rule: InferenceRule::ModusPonens,
                lines: vec![1, 2],
            },
        );
        assert_eq!(proof.lines[3].depth, 1);
    }

    #[test]
    fn test_ip_subproof_with_p_and_not_p() {
        // Simulate user's scenario: Open IP subproof, derive P · ~P, close with negation of assumption
        let theorem = make_simple_theorem();
        let mut proof = Proof::new(theorem);

        // Open IP subproof with assumption ~(R ∨ S) · (R ∨ S)
        let assumption = Formula::parse("~(R | S) & (R | S)").unwrap();
        proof.open_subproof(assumption.clone(), ProofTechnique::IndirectProof);
        assert_eq!(proof.current_depth(), 1);
        assert!(proof.scope_manager.has_open_scopes(), "Scope should be open after open_subproof");

        // Add some lines (simulating user's derivation)
        proof.add_line(
            Formula::parse("R | S").unwrap(),
            Justification::Inference {
                rule: InferenceRule::Simplification,
                lines: vec![3],
            },
        );
        proof.add_line(
            Formula::parse("~(R | S)").unwrap(),
            Justification::Inference {
                rule: InferenceRule::Simplification,
                lines: vec![3],
            },
        );
        // Last line is the contradiction P · ~P
        proof.add_line(
            Formula::parse("~(R | S) & (R | S)").unwrap(),
            Justification::Inference {
                rule: InferenceRule::Conjunction,
                lines: vec![5, 4],
            },
        );

        // Verify scope is still open
        assert!(proof.scope_manager.has_open_scopes(), "Scope should still be open before close");
        assert!(proof.scope_manager.current_scope().is_some(), "current_scope() should return Some");

        // Close the subproof with negation of assumption
        let conclusion = Formula::parse("~[~(R | S) & (R | S)]").unwrap();
        let result = proof.close_subproof(conclusion, ProofTechnique::IndirectProof);
        assert!(result.is_some(), "close_subproof should return Some");

        // Verify scope is now closed
        assert!(!proof.scope_manager.has_open_scopes(), "Scope should be closed after close_subproof");
    }
}
