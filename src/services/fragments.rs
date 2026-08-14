use serde::{Deserialize, Serialize};
use crate::models::Formula;

/// Proof fragments - composable building blocks for proof generation.
/// Each fragment represents a single inference step or subproof pattern.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Fragment {
    // === Basic inference rules (no nesting) ===

    /// Modus Ponens: A, A ⊃ B → B
    MP,

    /// Modus Tollens: A ⊃ B, ~B → ~A
    MT,

    /// Hypothetical Syllogism: A ⊃ B, B ⊃ C → A ⊃ C
    HS,

    /// Disjunctive Syllogism: A ∨ B, ~A → B
    DS,

    /// Simplification: A · B → A (or B)
    Simp,

    /// Conjunction: A, B → A · B
    Conj,

    /// Addition: A → A ∨ B
    Add,

    /// Constructive Dilemma: A ∨ B, A ⊃ C, B ⊃ D → C ∨ D
    CD,

    // === Subproof wrappers (add nesting depth) ===

    /// Conditional Proof: [assume A, derive B] → A ⊃ B
    CP,

    /// Indirect Proof: [assume ~A, derive ⊥] → A
    IP,

    /// Negation Introduction: [assume A, derive ⊥] → ~A
    NegIntro,

    /// Case Split: A ∨ B, [A → C], [B → C] → C
    CaseSplit,
}

impl Fragment {
    /// Does this fragment add subproof nesting?
    pub fn adds_nesting(&self) -> bool {
        matches!(self, Fragment::CP | Fragment::IP | Fragment::NegIntro | Fragment::CaseSplit)
    }

    /// Get display name for the fragment
    pub fn name(&self) -> &'static str {
        match self {
            Fragment::MP => "Modus Ponens",
            Fragment::MT => "Modus Tollens",
            Fragment::HS => "Hypothetical Syllogism",
            Fragment::DS => "Disjunctive Syllogism",
            Fragment::Simp => "Simplification",
            Fragment::Conj => "Conjunction",
            Fragment::Add => "Addition",
            Fragment::CD => "Constructive Dilemma",
            Fragment::CP => "Conditional Proof",
            Fragment::IP => "Indirect Proof",
            Fragment::NegIntro => "Negation Introduction",
            Fragment::CaseSplit => "Case Split",
        }
    }

    /// Get short code for the fragment (used in proof trees)
    pub fn code(&self) -> &'static str {
        match self {
            Fragment::MP => "MP",
            Fragment::MT => "MT",
            Fragment::HS => "HS",
            Fragment::DS => "DS",
            Fragment::Simp => "Simp",
            Fragment::Conj => "Conj",
            Fragment::Add => "Add",
            Fragment::CD => "CD",
            Fragment::CP => "CP",
            Fragment::IP => "IP",
            Fragment::NegIntro => "NegIntro",
            Fragment::CaseSplit => "CaseSplit",
        }
    }

    /// Get fragments that can produce a goal of the given shape
    pub fn fragments_for_goal(goal: &Formula) -> Vec<Fragment> {
        let mut candidates = Vec::new();

        match goal {
            // Implications can come from CP, HS
            Formula::Implies(_, _) => {
                candidates.push(Fragment::CP);
                candidates.push(Fragment::HS);
            }

            // Negations can come from MT, NegIntro
            Formula::Not(inner) => {
                // Double negation can come from IP proving the inner
                if matches!(inner.as_ref(), Formula::Not(_)) {
                    candidates.push(Fragment::IP);
                }
                candidates.push(Fragment::MT);
                candidates.push(Fragment::NegIntro);
            }

            // Disjunctions can come from Add, CD, DS (less directly)
            Formula::Or(_, _) => {
                candidates.push(Fragment::Add);
                candidates.push(Fragment::CD);
            }

            // Conjunctions can come from Conj
            Formula::And(_, _) => {
                candidates.push(Fragment::Conj);
            }

            // Contradiction can come from NegE (handled separately)
            Formula::Contradiction => {
                // Contradictions are derived from P and ~P
                // This is handled as a special case in generation
            }

            // Atoms, biconditionals - use general rules
            _ => {}
        }

        // These fragments can produce any formula type
        candidates.push(Fragment::MP);     // Can produce anything as consequent
        candidates.push(Fragment::DS);     // Can produce any disjunct
        candidates.push(Fragment::Simp);   // Can produce either conjunct
        candidates.push(Fragment::IP);     // Can prove any formula
        candidates.push(Fragment::CaseSplit); // Can prove any formula

        candidates
    }

    /// Get all basic (non-nesting) fragments
    pub fn basic_fragments() -> Vec<Fragment> {
        vec![
            Fragment::MP,
            Fragment::MT,
            Fragment::HS,
            Fragment::DS,
            Fragment::Simp,
            Fragment::Conj,
            Fragment::Add,
            Fragment::CD,
        ]
    }

    /// Get all nesting (subproof) fragments
    pub fn nesting_fragments() -> Vec<Fragment> {
        vec![
            Fragment::CP,
            Fragment::IP,
            Fragment::NegIntro,
            Fragment::CaseSplit,
        ]
    }

    /// Get all fragments
    pub fn all() -> Vec<Fragment> {
        vec![
            Fragment::MP,
            Fragment::MT,
            Fragment::HS,
            Fragment::DS,
            Fragment::Simp,
            Fragment::Conj,
            Fragment::Add,
            Fragment::CD,
            Fragment::CP,
            Fragment::IP,
            Fragment::NegIntro,
            Fragment::CaseSplit,
        ]
    }
}

/// Metadata about what inputs a fragment needs and what it produces
#[derive(Debug, Clone)]
pub struct FragmentSpec {
    /// The fragment type
    pub fragment: Fragment,
    /// Number of child proofs needed (not counting assumptions)
    pub child_count: usize,
    /// Does this fragment discharge an assumption?
    pub discharges_assumption: bool,
}

impl FragmentSpec {
    pub fn for_fragment(fragment: Fragment) -> Self {
        match fragment {
            Fragment::MP => Self { fragment, child_count: 2, discharges_assumption: false },
            Fragment::MT => Self { fragment, child_count: 2, discharges_assumption: false },
            Fragment::HS => Self { fragment, child_count: 2, discharges_assumption: false },
            Fragment::DS => Self { fragment, child_count: 2, discharges_assumption: false },
            Fragment::Simp => Self { fragment, child_count: 1, discharges_assumption: false },
            Fragment::Conj => Self { fragment, child_count: 2, discharges_assumption: false },
            Fragment::Add => Self { fragment, child_count: 1, discharges_assumption: false },
            Fragment::CD => Self { fragment, child_count: 3, discharges_assumption: false },
            Fragment::CP => Self { fragment, child_count: 1, discharges_assumption: true },
            Fragment::IP => Self { fragment, child_count: 1, discharges_assumption: true },
            Fragment::NegIntro => Self { fragment, child_count: 1, discharges_assumption: true },
            Fragment::CaseSplit => Self { fragment, child_count: 3, discharges_assumption: true },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nesting_classification() {
        assert!(!Fragment::MP.adds_nesting());
        assert!(!Fragment::MT.adds_nesting());
        assert!(!Fragment::Conj.adds_nesting());

        assert!(Fragment::CP.adds_nesting());
        assert!(Fragment::IP.adds_nesting());
        assert!(Fragment::NegIntro.adds_nesting());
        assert!(Fragment::CaseSplit.adds_nesting());
    }

    #[test]
    fn test_fragments_for_implication() {
        let goal = Formula::Implies(
            Box::new(Formula::Atom("P".to_string())),
            Box::new(Formula::Atom("Q".to_string())),
        );

        let fragments = Fragment::fragments_for_goal(&goal);
        assert!(fragments.contains(&Fragment::CP));
        assert!(fragments.contains(&Fragment::HS));
    }

    #[test]
    fn test_fragments_for_conjunction() {
        let goal = Formula::And(
            Box::new(Formula::Atom("P".to_string())),
            Box::new(Formula::Atom("Q".to_string())),
        );

        let fragments = Fragment::fragments_for_goal(&goal);
        assert!(fragments.contains(&Fragment::Conj));
    }

    #[test]
    fn test_all_fragments() {
        let all = Fragment::all();
        assert_eq!(all.len(), 12);

        let basic = Fragment::basic_fragments();
        let nesting = Fragment::nesting_fragments();
        assert_eq!(basic.len() + nesting.len(), all.len());
    }
}
