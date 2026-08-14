use serde::{Deserialize, Serialize};
use crate::models::formula::Formula;

/// Valid Argument Forms of Inference (1-8) from rules.md
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum InferenceRule {
    // 1. Modus Ponens (MP): p ⊃ q, p ∴ q
    ModusPonens,
    // 2. Modus Tollens (MT): p ⊃ q, ~q ∴ ~p
    ModusTollens,
    // 3. Disjunctive Syllogism (DS): p ∨ q, ~p ∴ q
    DisjunctiveSyllogism,
    // 4. Simplification (Simp): p · q ∴ p (or q)
    Simplification,
    // 5. Conjunction (Conj): p, q ∴ p · q
    Conjunction,
    // 6. Hypothetical Syllogism (HS): p ⊃ q, q ⊃ r ∴ p ⊃ r
    HypotheticalSyllogism,
    // 7. Addition (Add): p ∴ p ∨ q
    Addition,
    // 8. Constructive Dilemma (CD): p ∨ q, p ⊃ r, q ⊃ s ∴ r ∨ s
    ConstructiveDilemma,
    // 19. Contradiction (NegE): p, ~p ∴ ⊥
    Contradiction,
}

impl InferenceRule {
    pub fn name(&self) -> &'static str {
        match self {
            InferenceRule::ModusPonens => "Modus Ponens",
            InferenceRule::ModusTollens => "Modus Tollens",
            InferenceRule::DisjunctiveSyllogism => "Disjunctive Syllogism",
            InferenceRule::Simplification => "Simplification",
            InferenceRule::Conjunction => "Conjunction",
            InferenceRule::HypotheticalSyllogism => "Hypothetical Syllogism",
            InferenceRule::Addition => "Addition",
            InferenceRule::ConstructiveDilemma => "Constructive Dilemma",
            InferenceRule::Contradiction => "Contradiction Introduction",
        }
    }

    pub fn abbreviation(&self) -> &'static str {
        match self {
            InferenceRule::ModusPonens => "MP",
            InferenceRule::ModusTollens => "MT",
            InferenceRule::DisjunctiveSyllogism => "DS",
            InferenceRule::Simplification => "Simp",
            InferenceRule::Conjunction => "Conj",
            InferenceRule::HypotheticalSyllogism => "HS",
            InferenceRule::Addition => "Add",
            InferenceRule::ConstructiveDilemma => "CD",
            InferenceRule::Contradiction => "NegE",
        }
    }

    /// Number of premises required for this rule
    pub fn premise_count(&self) -> usize {
        match self {
            InferenceRule::ModusPonens => 2,
            InferenceRule::ModusTollens => 2,
            InferenceRule::DisjunctiveSyllogism => 2,
            InferenceRule::Simplification => 1,
            InferenceRule::Conjunction => 2,
            InferenceRule::HypotheticalSyllogism => 2,
            InferenceRule::Addition => 1,
            InferenceRule::ConstructiveDilemma => 3,
            InferenceRule::Contradiction => 2,
        }
    }

    /// Does this rule require additional formula input?
    pub fn requires_formula_input(&self) -> bool {
        matches!(self, InferenceRule::Addition)
    }

    /// Get all possible conclusions from applying this rule to the premises
    pub fn all_conclusions(&self, premises: &[&Formula], additional: Option<&Formula>) -> Vec<Formula> {
        let mut results = Vec::new();

        match self {
            InferenceRule::ModusPonens => {
                // p ⊃ q, p ∴ q
                if premises.len() != 2 {
                    return results;
                }
                for (i, j) in [(0, 1), (1, 0)] {
                    if let Formula::Implies(antecedent, consequent) = premises[i] {
                        if antecedent.as_ref() == premises[j] {
                            results.push(consequent.as_ref().clone());
                        }
                    }
                }
            }

            InferenceRule::ModusTollens => {
                // p ⊃ q, ~q ∴ ~p
                if premises.len() != 2 {
                    return results;
                }
                for (i, j) in [(0, 1), (1, 0)] {
                    if let Formula::Implies(antecedent, consequent) = premises[i] {
                        if let Formula::Not(inner) = premises[j] {
                            if consequent.as_ref() == inner.as_ref() {
                                results.push(Formula::Not(antecedent.clone()));
                            }
                        }
                    }
                }
            }

            InferenceRule::DisjunctiveSyllogism => {
                // p ∨ q, ~p ∴ q  or  p ∨ q, ~q ∴ p
                if premises.len() != 2 {
                    return results;
                }
                for (i, j) in [(0, 1), (1, 0)] {
                    if let Formula::Or(left, right) = premises[i] {
                        if let Formula::Not(negated) = premises[j] {
                            if negated.as_ref() == left.as_ref() {
                                results.push(right.as_ref().clone());
                            }
                            if negated.as_ref() == right.as_ref() {
                                results.push(left.as_ref().clone());
                            }
                        }
                    }
                }
            }

            InferenceRule::Simplification => {
                // p · q ∴ p  and  p · q ∴ q
                if premises.len() != 1 {
                    return results;
                }
                if let Formula::And(left, right) = premises[0] {
                    results.push(left.as_ref().clone());
                    results.push(right.as_ref().clone());
                }
            }

            InferenceRule::Conjunction => {
                // p, q ∴ p · q
                if premises.len() != 2 {
                    return results;
                }
                results.push(Formula::And(
                    Box::new(premises[0].clone()),
                    Box::new(premises[1].clone()),
                ));
            }

            InferenceRule::HypotheticalSyllogism => {
                // p ⊃ q, q ⊃ r ∴ p ⊃ r
                if premises.len() != 2 {
                    return results;
                }
                for (i, j) in [(0, 1), (1, 0)] {
                    if let Formula::Implies(p, q1) = premises[i] {
                        if let Formula::Implies(q2, r) = premises[j] {
                            if q1.as_ref() == q2.as_ref() {
                                results.push(Formula::Implies(p.clone(), r.clone()));
                            }
                        }
                    }
                }
            }

            InferenceRule::Addition => {
                // p ∴ p ∨ q (requires additional formula q)
                if premises.len() != 1 {
                    return results;
                }
                if let Some(additional) = additional {
                    // p ∨ q (premise on left)
                    results.push(Formula::Or(
                        Box::new(premises[0].clone()),
                        Box::new(additional.clone()),
                    ));
                    // q ∨ p (premise on right)
                    results.push(Formula::Or(
                        Box::new(additional.clone()),
                        Box::new(premises[0].clone()),
                    ));
                }
            }

            InferenceRule::ConstructiveDilemma => {
                // p ∨ q, p ⊃ r, q ⊃ s ∴ r ∨ s
                if premises.len() != 3 {
                    return results;
                }
                // Try all permutations to find disjunction and two implications
                for perm in [
                    [0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0],
                ] {
                    if let Formula::Or(p, q) = premises[perm[0]] {
                        if let Formula::Implies(p2, r) = premises[perm[1]] {
                            if let Formula::Implies(q2, s) = premises[perm[2]] {
                                if p.as_ref() == p2.as_ref() && q.as_ref() == q2.as_ref() {
                                    results.push(Formula::Or(r.clone(), s.clone()));
                                }
                            }
                        }
                    }
                }
            }

            InferenceRule::Contradiction => {
                // p, ~p ∴ ⊥
                if premises.len() != 2 {
                    return results;
                }
                for (i, j) in [(0, 1), (1, 0)] {
                    if let Formula::Not(inner) = premises[i] {
                        if inner.as_ref() == premises[j] {
                            results.push(Formula::Contradiction);
                        }
                    }
                }
            }
        }

        results
    }

    /// Apply the rule to the given premises (returns first valid conclusion)
    pub fn apply(&self, premises: &[&Formula], additional: Option<&Formula>) -> Option<Formula> {
        self.all_conclusions(premises, additional).into_iter().next()
    }

    /// Verify that the conclusion follows from the premises using this rule
    pub fn verify(&self, premises: &[&Formula], conclusion: &Formula, additional: Option<&Formula>) -> bool {
        self.all_conclusions(premises, additional).contains(conclusion)
    }

    /// Get all inference rules
    pub fn all() -> Vec<InferenceRule> {
        vec![
            InferenceRule::ModusPonens,
            InferenceRule::ModusTollens,
            InferenceRule::DisjunctiveSyllogism,
            InferenceRule::Simplification,
            InferenceRule::Conjunction,
            InferenceRule::HypotheticalSyllogism,
            InferenceRule::Addition,
            InferenceRule::ConstructiveDilemma,
            InferenceRule::Contradiction,
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_modus_ponens() {
        let p_implies_q = Formula::parse("P -> Q").unwrap();
        let p = Formula::parse("P").unwrap();
        let q = Formula::parse("Q").unwrap();

        let result = InferenceRule::ModusPonens.apply(&[&p_implies_q, &p], None);
        assert_eq!(result, Some(q.clone()));

        // Order shouldn't matter
        let result = InferenceRule::ModusPonens.apply(&[&p, &p_implies_q], None);
        assert_eq!(result, Some(q));
    }

    #[test]
    fn test_modus_tollens() {
        let p_implies_q = Formula::parse("P -> Q").unwrap();
        let not_q = Formula::parse("~Q").unwrap();
        let not_p = Formula::parse("~P").unwrap();

        let result = InferenceRule::ModusTollens.apply(&[&p_implies_q, &not_q], None);
        assert_eq!(result, Some(not_p));
    }

    #[test]
    fn test_disjunctive_syllogism() {
        let p_or_q = Formula::parse("P | Q").unwrap();
        let not_p = Formula::parse("~P").unwrap();
        let q = Formula::parse("Q").unwrap();

        let result = InferenceRule::DisjunctiveSyllogism.apply(&[&p_or_q, &not_p], None);
        assert_eq!(result, Some(q));
    }

    #[test]
    fn test_simplification() {
        let p_and_q = Formula::parse("P & Q").unwrap();
        let p = Formula::parse("P").unwrap();
        let q = Formula::parse("Q").unwrap();

        // Should return both possible conclusions
        let conclusions = InferenceRule::Simplification.all_conclusions(&[&p_and_q], None);
        assert!(conclusions.contains(&p));
        assert!(conclusions.contains(&q));

        // Verify works with either
        assert!(InferenceRule::Simplification.verify(&[&p_and_q], &p, None));
        assert!(InferenceRule::Simplification.verify(&[&p_and_q], &q, None));
    }

    #[test]
    fn test_conjunction() {
        let p = Formula::parse("P").unwrap();
        let q = Formula::parse("Q").unwrap();
        let p_and_q = Formula::parse("P & Q").unwrap();

        let result = InferenceRule::Conjunction.apply(&[&p, &q], None);
        assert_eq!(result, Some(p_and_q));
    }

    #[test]
    fn test_hypothetical_syllogism() {
        let p_implies_q = Formula::parse("P -> Q").unwrap();
        let q_implies_r = Formula::parse("Q -> R").unwrap();
        let p_implies_r = Formula::parse("P -> R").unwrap();

        let result = InferenceRule::HypotheticalSyllogism.apply(&[&p_implies_q, &q_implies_r], None);
        assert_eq!(result, Some(p_implies_r));
    }

    #[test]
    fn test_addition() {
        let p = Formula::parse("P").unwrap();
        let q = Formula::parse("Q").unwrap();
        let p_or_q = Formula::parse("P | Q").unwrap();
        let q_or_p = Formula::parse("Q | P").unwrap();

        // Both placements should work
        assert!(InferenceRule::Addition.verify(&[&p], &p_or_q, Some(&q)));
        assert!(InferenceRule::Addition.verify(&[&p], &q_or_p, Some(&q)));
    }

    #[test]
    fn test_contradiction() {
        let p = Formula::parse("P").unwrap();
        let not_p = Formula::parse("~P").unwrap();
        let contra = Formula::Contradiction;

        let result = InferenceRule::Contradiction.apply(&[&p, &not_p], None);
        assert_eq!(result, Some(contra));
    }
}
