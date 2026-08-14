use serde::{Deserialize, Serialize};
use crate::models::formula::Formula;

/// Valid Equivalence Forms (9-18) from rules.md
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum EquivalenceRule {
    // 9. Double Negation (DN): p :: ~~p
    DoubleNegation,
    // 10. De Morgan's Theorem (DeM): ~(p · q) :: (~p ∨ ~q), ~(p ∨ q) :: (~p · ~q)
    DeMorgan,
    // 11. Commutation (Comm): (p ∨ q) :: (q ∨ p), (p · q) :: (q · p)
    Commutation,
    // 12. Association (Assoc): [p ∨ (q ∨ r)] :: [(p ∨ q) ∨ r], [p · (q · r)] :: [(p · q) · r]
    Association,
    // 13. Distribution (Dist): [p · (q ∨ r)] :: [(p · q) ∨ (p · r)], [p ∨ (q · r)] :: [(p ∨ q) · (p ∨ r)]
    Distribution,
    // 14. Contraposition (Contra): (p ⊃ q) :: (~q ⊃ ~p)
    Contraposition,
    // 15. Implication (Impl): (p ⊃ q) :: (~p ∨ q)
    Implication,
    // 16. Exportation (Exp): [(p · q) ⊃ r] :: [p ⊃ (q ⊃ r)]
    Exportation,
    // 17. Tautology (Taut): p :: (p · p), p :: (p ∨ p)
    Tautology,
    // 18. Equivalence (Equiv): (p ≡ q) :: [(p ⊃ q) · (q ⊃ p)]
    Equivalence,
}

impl EquivalenceRule {
    pub fn name(&self) -> &'static str {
        match self {
            EquivalenceRule::DoubleNegation => "Double Negation",
            EquivalenceRule::DeMorgan => "DeMorgan's Theorem",
            EquivalenceRule::Commutation => "Commutation",
            EquivalenceRule::Association => "Association",
            EquivalenceRule::Distribution => "Distribution",
            EquivalenceRule::Contraposition => "Contraposition",
            EquivalenceRule::Implication => "Implication",
            EquivalenceRule::Exportation => "Exportation",
            EquivalenceRule::Tautology => "Tautology",
            EquivalenceRule::Equivalence => "Equivalence",
        }
    }

    pub fn abbreviation(&self) -> &'static str {
        match self {
            EquivalenceRule::DoubleNegation => "DN",
            EquivalenceRule::DeMorgan => "DeM",
            EquivalenceRule::Commutation => "Comm",
            EquivalenceRule::Association => "Assoc",
            EquivalenceRule::Distribution => "Dist",
            EquivalenceRule::Contraposition => "Contra",
            EquivalenceRule::Implication => "Impl",
            EquivalenceRule::Exportation => "Exp",
            EquivalenceRule::Tautology => "Taut",
            EquivalenceRule::Equivalence => "Equiv",
        }
    }

    /// Get all equivalent forms of the given formula using this rule
    /// Returns forms where the transformation was applied at the top level
    pub fn equivalent_forms(&self, formula: &Formula) -> Vec<Formula> {
        let mut results = Vec::new();

        match self {
            EquivalenceRule::DeMorgan => {
                // ~(P · Q) ≡ ~P ∨ ~Q (De Morgan for And)
                if let Formula::Not(inner) = formula {
                    if let Formula::And(p, q) = inner.as_ref() {
                        results.push(Formula::Or(
                            Box::new(Formula::Not(p.clone())),
                            Box::new(Formula::Not(q.clone())),
                        ));
                    }
                }
                if let Formula::Or(left, right) = formula {
                    if let (Formula::Not(p), Formula::Not(q)) = (left.as_ref(), right.as_ref()) {
                        results.push(Formula::Not(Box::new(Formula::And(
                            p.clone(),
                            q.clone(),
                        ))));
                    }
                }

                // ~(P ∨ Q) ≡ ~P · ~Q (De Morgan for Or)
                if let Formula::Not(inner) = formula {
                    if let Formula::Or(p, q) = inner.as_ref() {
                        results.push(Formula::And(
                            Box::new(Formula::Not(p.clone())),
                            Box::new(Formula::Not(q.clone())),
                        ));
                    }
                }
                if let Formula::And(left, right) = formula {
                    if let (Formula::Not(p), Formula::Not(q)) = (left.as_ref(), right.as_ref()) {
                        results.push(Formula::Not(Box::new(Formula::Or(
                            p.clone(),
                            q.clone(),
                        ))));
                    }
                }
            }

            EquivalenceRule::Commutation => {
                // P · Q ≡ Q · P, P ∨ Q ≡ Q ∨ P
                match formula {
                    Formula::And(p, q) => {
                        results.push(Formula::And(q.clone(), p.clone()));
                    }
                    Formula::Or(p, q) => {
                        results.push(Formula::Or(q.clone(), p.clone()));
                    }
                    _ => {}
                }
            }

            EquivalenceRule::Association => {
                // (P · Q) · R ≡ P · (Q · R)
                // (P ∨ Q) ∨ R ≡ P ∨ (Q ∨ R)
                match formula {
                    Formula::And(left, r) => {
                        if let Formula::And(p, q) = left.as_ref() {
                            results.push(Formula::And(
                                p.clone(),
                                Box::new(Formula::And(q.clone(), r.clone())),
                            ));
                        }
                    }
                    Formula::Or(left, r) => {
                        if let Formula::Or(p, q) = left.as_ref() {
                            results.push(Formula::Or(
                                p.clone(),
                                Box::new(Formula::Or(q.clone(), r.clone())),
                            ));
                        }
                    }
                    _ => {}
                }
                // Also handle the other direction
                match formula {
                    Formula::And(p, right) => {
                        if let Formula::And(q, r) = right.as_ref() {
                            results.push(Formula::And(
                                Box::new(Formula::And(p.clone(), q.clone())),
                                r.clone(),
                            ));
                        }
                    }
                    Formula::Or(p, right) => {
                        if let Formula::Or(q, r) = right.as_ref() {
                            results.push(Formula::Or(
                                Box::new(Formula::Or(p.clone(), q.clone())),
                                r.clone(),
                            ));
                        }
                    }
                    _ => {}
                }
            }

            EquivalenceRule::Distribution => {
                // P · (Q ∨ R) ≡ (P · Q) ∨ (P · R) (And over Or)
                if let Formula::And(p, right) = formula {
                    if let Formula::Or(q, r) = right.as_ref() {
                        results.push(Formula::Or(
                            Box::new(Formula::And(p.clone(), q.clone())),
                            Box::new(Formula::And(p.clone(), r.clone())),
                        ));
                    }
                }
                if let Formula::Or(left, right) = formula {
                    if let (Formula::And(p1, q), Formula::And(p2, r)) = (left.as_ref(), right.as_ref()) {
                        if p1 == p2 {
                            results.push(Formula::And(
                                p1.clone(),
                                Box::new(Formula::Or(q.clone(), r.clone())),
                            ));
                        }
                    }
                }

                // P ∨ (Q · R) ≡ (P ∨ Q) · (P ∨ R) (Or over And)
                if let Formula::Or(p, right) = formula {
                    if let Formula::And(q, r) = right.as_ref() {
                        results.push(Formula::And(
                            Box::new(Formula::Or(p.clone(), q.clone())),
                            Box::new(Formula::Or(p.clone(), r.clone())),
                        ));
                    }
                }
                if let Formula::And(left, right) = formula {
                    if let (Formula::Or(p1, q), Formula::Or(p2, r)) = (left.as_ref(), right.as_ref()) {
                        if p1 == p2 {
                            results.push(Formula::Or(
                                p1.clone(),
                                Box::new(Formula::And(q.clone(), r.clone())),
                            ));
                        }
                    }
                }
            }

            EquivalenceRule::Contraposition => {
                // P → Q ≡ ~Q → ~P
                if let Formula::Implies(p, q) = formula {
                    results.push(Formula::Implies(
                        Box::new(Formula::Not(q.clone())),
                        Box::new(Formula::Not(p.clone())),
                    ));
                }
                // Also handle double negation cases
                if let Formula::Implies(not_q, not_p) = formula {
                    if let (Formula::Not(q), Formula::Not(p)) = (not_q.as_ref(), not_p.as_ref()) {
                        results.push(Formula::Implies(p.clone(), q.clone()));
                    }
                }
            }

            EquivalenceRule::Implication => {
                // (p ⊃ q) :: (~p ∨ q)
                if let Formula::Implies(p, q) = formula {
                    results.push(Formula::Or(
                        Box::new(Formula::Not(p.clone())),
                        q.clone(),
                    ));
                }
                if let Formula::Or(left, q) = formula {
                    if let Formula::Not(p) = left.as_ref() {
                        results.push(Formula::Implies(p.clone(), q.clone()));
                    }
                }
            }

            EquivalenceRule::Equivalence => {
                // (p ≡ q) :: [(p ⊃ q) · (q ⊃ p)]
                if let Formula::Biconditional(p, q) = formula {
                    // To conjunction of implications
                    results.push(Formula::And(
                        Box::new(Formula::Implies(p.clone(), q.clone())),
                        Box::new(Formula::Implies(q.clone(), p.clone())),
                    ));
                }
                // From conjunction of implications
                if let Formula::And(left, right) = formula {
                    if let (Formula::Implies(p1, q1), Formula::Implies(q2, p2)) =
                        (left.as_ref(), right.as_ref())
                    {
                        if p1 == p2 && q1 == q2 {
                            results.push(Formula::Biconditional(p1.clone(), q1.clone()));
                        }
                    }
                }
            }

            EquivalenceRule::Exportation => {
                // (P · Q) → R ≡ P → (Q → R)
                if let Formula::Implies(left, r) = formula {
                    if let Formula::And(p, q) = left.as_ref() {
                        results.push(Formula::Implies(
                            p.clone(),
                            Box::new(Formula::Implies(q.clone(), r.clone())),
                        ));
                    }
                }
                if let Formula::Implies(p, right) = formula {
                    if let Formula::Implies(q, r) = right.as_ref() {
                        results.push(Formula::Implies(
                            Box::new(Formula::And(p.clone(), q.clone())),
                            r.clone(),
                        ));
                    }
                }
            }

            EquivalenceRule::Tautology => {
                // P ≡ P · P, P ≡ P ∨ P
                // Expansion
                results.push(Formula::And(
                    Box::new(formula.clone()),
                    Box::new(formula.clone()),
                ));
                results.push(Formula::Or(
                    Box::new(formula.clone()),
                    Box::new(formula.clone()),
                ));
                // Contraction
                if let Formula::And(p, q) = formula {
                    if p == q {
                        results.push(p.as_ref().clone());
                    }
                }
                if let Formula::Or(p, q) = formula {
                    if p == q {
                        results.push(p.as_ref().clone());
                    }
                }
            }

            EquivalenceRule::DoubleNegation => {
                // P ≡ ~~P
                results.push(Formula::Not(Box::new(Formula::Not(Box::new(formula.clone())))));
                if let Formula::Not(inner) = formula {
                    if let Formula::Not(inner_inner) = inner.as_ref() {
                        results.push(inner_inner.as_ref().clone());
                    }
                }
            }
        }

        results
    }

    /// Check if the formula can be transformed to the target using this rule
    pub fn can_transform(&self, from: &Formula, to: &Formula) -> bool {
        self.equivalent_forms(from).contains(to)
    }

    /// Apply the rule to a subformula within a larger formula
    pub fn apply_to_subformula(&self, formula: &Formula, target_subformula: &Formula, replacement: &Formula) -> Option<Formula> {
        // Check if the replacement is valid
        if !self.can_transform(target_subformula, replacement) {
            return None;
        }

        // Recursively replace the subformula
        Some(Self::replace_subformula(formula, target_subformula, replacement))
    }

    /// Replace all occurrences of a target subformula with a replacement
    pub fn replace_subformula(formula: &Formula, target: &Formula, replacement: &Formula) -> Formula {
        if formula == target {
            return replacement.clone();
        }

        match formula {
            Formula::Atom(_) | Formula::Contradiction => formula.clone(),
            Formula::Not(inner) => Formula::Not(Box::new(
                Self::replace_subformula(inner, target, replacement),
            )),
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

    /// Get all equivalence rules (9-18 from rules.md)
    pub fn all() -> Vec<EquivalenceRule> {
        vec![
            EquivalenceRule::DoubleNegation,   // 9. DN
            EquivalenceRule::DeMorgan,          // 10. DeM
            EquivalenceRule::Commutation,       // 11. Comm
            EquivalenceRule::Association,       // 12. Assoc
            EquivalenceRule::Distribution,      // 13. Dist
            EquivalenceRule::Contraposition,    // 14. Contra
            EquivalenceRule::Implication,       // 15. Impl
            EquivalenceRule::Exportation,       // 16. Exp
            EquivalenceRule::Tautology,         // 17. Taut
            EquivalenceRule::Equivalence,       // 18. Equiv
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_demorgan_and() {
        let formula = Formula::parse("~(P & Q)").unwrap();
        let expected = Formula::parse("~P | ~Q").unwrap();

        let forms = EquivalenceRule::DeMorgan.equivalent_forms(&formula);
        assert!(forms.contains(&expected));
    }

    #[test]
    fn test_demorgan_or() {
        let formula = Formula::parse("~(P | Q)").unwrap();
        let expected = Formula::parse("~P & ~Q").unwrap();

        let forms = EquivalenceRule::DeMorgan.equivalent_forms(&formula);
        assert!(forms.contains(&expected));
    }

    #[test]
    fn test_commutation() {
        let formula = Formula::parse("P & Q").unwrap();
        let expected = Formula::parse("Q & P").unwrap();

        let forms = EquivalenceRule::Commutation.equivalent_forms(&formula);
        assert!(forms.contains(&expected));
    }

    #[test]
    fn test_implication() {
        let formula = Formula::parse("P -> Q").unwrap();
        let expected = Formula::parse("~P | Q").unwrap();

        let forms = EquivalenceRule::Implication.equivalent_forms(&formula);
        assert!(forms.contains(&expected));
    }

    #[test]
    fn test_contraposition() {
        let formula = Formula::parse("P -> Q").unwrap();
        let expected = Formula::parse("~Q -> ~P").unwrap();

        let forms = EquivalenceRule::Contraposition.equivalent_forms(&formula);
        assert!(forms.contains(&expected));
    }

    #[test]
    fn test_double_negation() {
        let formula = Formula::parse("P").unwrap();
        let expected = Formula::parse("~~P").unwrap();

        let forms = EquivalenceRule::DoubleNegation.equivalent_forms(&formula);
        assert!(forms.contains(&expected));

        // And the reverse
        let forms = EquivalenceRule::DoubleNegation.equivalent_forms(&expected);
        assert!(forms.contains(&formula));
    }

    #[test]
    fn test_exportation() {
        let formula = Formula::parse("(P & Q) -> R").unwrap();
        let expected = Formula::parse("P -> (Q -> R)").unwrap();

        let forms = EquivalenceRule::Exportation.equivalent_forms(&formula);
        assert!(forms.contains(&expected));
    }
    #[test]
    fn test_implication_subformula() {
        let formula = Formula::parse("~(P -> Q)").unwrap();
        let target = Formula::parse("~(~P | Q)").unwrap();

        let mut found = false;
        for sub in formula.subformulas() {
            for equiv in EquivalenceRule::Implication.equivalent_forms(&sub) {
                let transformed = EquivalenceRule::replace_subformula(&formula, &sub, &equiv);
                if transformed == target {
                    found = true;
                    break;
                }
            }
        }
        assert!(found);
    }
}
