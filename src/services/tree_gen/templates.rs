use crate::models::Formula;
use super::super::proof_tree::{ProofNode, ProofTree};

/// Template fallback theorems for when generation fails.
/// These are pre-constructed valid theorems that guarantee proof generation never fails completely.
pub struct FallbackTemplates;

impl FallbackTemplates {
    /// Variant 1: A∨B, A⊃C, B⊃C, C⊃D ⊢ D
    /// Case split to get C, then MP to get D
    pub fn build_case_split_variant_1(a: &Formula, b: &Formula, c: &Formula, d: &Formula) -> ProofTree {
        let a_or_b = Formula::Or(Box::new(a.clone()), Box::new(b.clone()));
        let a_impl_c = Formula::Implies(Box::new(a.clone()), Box::new(c.clone()));
        let b_impl_c = Formula::Implies(Box::new(b.clone()), Box::new(c.clone()));
        let c_impl_d = Formula::Implies(Box::new(c.clone()), Box::new(d.clone()));

        let root = ProofNode::derivation(
            d.clone(),
            "MP",
            vec![
                ProofNode::premise(c_impl_d),
                ProofNode::derivation(
                    c.clone(),
                    "CaseSplit",
                    vec![
                        ProofNode::premise(a_or_b),
                        ProofNode::assumption(a.clone()),
                        ProofNode::derivation(c.clone(), "MP", vec![
                            ProofNode::premise(a_impl_c),
                            ProofNode::assumption(a.clone()),
                        ], None),
                        ProofNode::assumption(b.clone()),
                        ProofNode::derivation(c.clone(), "MP", vec![
                            ProofNode::premise(b_impl_c),
                            ProofNode::assumption(b.clone()),
                        ], None),
                    ],
                    None,
                ),
            ],
            None,
        );
        ProofTree::new(root)
    }

    /// Variant 2: A∨B, A⊃(C∧D), B⊃(C∧D) ⊢ C∧D
    /// Case split with conjunction conclusion
    pub fn build_case_split_variant_2(a: &Formula, b: &Formula, c: &Formula, d: &Formula) -> ProofTree {
        let a_or_b = Formula::Or(Box::new(a.clone()), Box::new(b.clone()));
        let c_and_d = Formula::And(Box::new(c.clone()), Box::new(d.clone()));
        let a_impl_cd = Formula::Implies(Box::new(a.clone()), Box::new(c_and_d.clone()));
        let b_impl_cd = Formula::Implies(Box::new(b.clone()), Box::new(c_and_d.clone()));

        let root = ProofNode::derivation(
            c_and_d.clone(),
            "CaseSplit",
            vec![
                ProofNode::premise(a_or_b),
                ProofNode::assumption(a.clone()),
                ProofNode::derivation(c_and_d.clone(), "MP", vec![
                    ProofNode::premise(a_impl_cd),
                    ProofNode::assumption(a.clone()),
                ], None),
                ProofNode::assumption(b.clone()),
                ProofNode::derivation(c_and_d.clone(), "MP", vec![
                    ProofNode::premise(b_impl_cd),
                    ProofNode::assumption(b.clone()),
                ], None),
            ],
            None,
        );
        ProofTree::new(root)
    }

    /// Variant 3: (A∨B)∧C, A⊃D, B⊃D ⊢ D
    /// Disjunction inside conjunction - need Simp first
    pub fn build_case_split_variant_3(a: &Formula, b: &Formula, c: &Formula, d: &Formula) -> ProofTree {
        let a_or_b = Formula::Or(Box::new(a.clone()), Box::new(b.clone()));
        let conj = Formula::And(Box::new(a_or_b.clone()), Box::new(c.clone()));
        let a_impl_d = Formula::Implies(Box::new(a.clone()), Box::new(d.clone()));
        let b_impl_d = Formula::Implies(Box::new(b.clone()), Box::new(d.clone()));

        let root = ProofNode::derivation(
            d.clone(),
            "CaseSplit",
            vec![
                ProofNode::derivation(a_or_b, "Simp", vec![ProofNode::premise(conj)], None),
                ProofNode::assumption(a.clone()),
                ProofNode::derivation(d.clone(), "MP", vec![
                    ProofNode::premise(a_impl_d),
                    ProofNode::assumption(a.clone()),
                ], None),
                ProofNode::assumption(b.clone()),
                ProofNode::derivation(d.clone(), "MP", vec![
                    ProofNode::premise(b_impl_d),
                    ProofNode::assumption(b.clone()),
                ], None),
            ],
            None,
        );
        ProofTree::new(root)
    }

    /// Variant 4: A∨B, A⊃C, B⊃D, C⊃E, D⊃E ⊢ E
    /// Asymmetric case split - different paths converge
    pub fn build_case_split_variant_4(a: &Formula, b: &Formula, c: &Formula, d: &Formula, e: &Formula) -> ProofTree {
        let a_or_b = Formula::Or(Box::new(a.clone()), Box::new(b.clone()));
        let a_impl_c = Formula::Implies(Box::new(a.clone()), Box::new(c.clone()));
        let b_impl_d = Formula::Implies(Box::new(b.clone()), Box::new(d.clone()));
        let c_impl_e = Formula::Implies(Box::new(c.clone()), Box::new(e.clone()));
        let d_impl_e = Formula::Implies(Box::new(d.clone()), Box::new(e.clone()));

        let root = ProofNode::derivation(
            e.clone(),
            "CaseSplit",
            vec![
                ProofNode::premise(a_or_b),
                // Case A: A → C → E
                ProofNode::assumption(a.clone()),
                ProofNode::derivation(e.clone(), "MP", vec![
                    ProofNode::premise(c_impl_e),
                    ProofNode::derivation(c.clone(), "MP", vec![
                        ProofNode::premise(a_impl_c),
                        ProofNode::assumption(a.clone()),
                    ], None),
                ], None),
                // Case B: B → D → E
                ProofNode::assumption(b.clone()),
                ProofNode::derivation(e.clone(), "MP", vec![
                    ProofNode::premise(d_impl_e),
                    ProofNode::derivation(d.clone(), "MP", vec![
                        ProofNode::premise(b_impl_d),
                        ProofNode::assumption(b.clone()),
                    ], None),
                ], None),
            ],
            None,
        );
        ProofTree::new(root)
    }

    /// CP Variant 1: A⊃B, C⊃D ⊢ (A∧C)⊃(B∧D)
    pub fn build_cp_variant_1(a: &Formula, b: &Formula, c: &Formula, d: &Formula) -> ProofTree {
        let a_impl_b = Formula::Implies(Box::new(a.clone()), Box::new(b.clone()));
        let c_impl_d = Formula::Implies(Box::new(c.clone()), Box::new(d.clone()));
        let a_and_c = Formula::And(Box::new(a.clone()), Box::new(c.clone()));
        let b_and_d = Formula::And(Box::new(b.clone()), Box::new(d.clone()));
        let conclusion = Formula::Implies(Box::new(a_and_c.clone()), Box::new(b_and_d.clone()));

        let root = ProofNode::derivation(
            conclusion,
            "CP",
            vec![
                ProofNode::assumption(a_and_c.clone()),
                ProofNode::derivation(b_and_d, "Conj", vec![
                    ProofNode::derivation(b.clone(), "MP", vec![
                        ProofNode::premise(a_impl_b),
                        ProofNode::derivation(a.clone(), "Simp", vec![ProofNode::assumption(a_and_c.clone())], None),
                    ], None),
                    ProofNode::derivation(d.clone(), "MP", vec![
                        ProofNode::premise(c_impl_d),
                        ProofNode::derivation(c.clone(), "Simp", vec![ProofNode::assumption(a_and_c)], None),
                    ], None),
                ], None),
            ],
            Some(Formula::And(Box::new(a.clone()), Box::new(c.clone()))),
        );
        ProofTree::new(root)
    }

    /// CP Variant 2: A⊃B ⊢ (C∧A)⊃(C∧B)
    pub fn build_cp_variant_2(a: &Formula, b: &Formula, c: &Formula) -> ProofTree {
        let a_impl_b = Formula::Implies(Box::new(a.clone()), Box::new(b.clone()));
        let c_and_a = Formula::And(Box::new(c.clone()), Box::new(a.clone()));
        let c_and_b = Formula::And(Box::new(c.clone()), Box::new(b.clone()));
        let conclusion = Formula::Implies(Box::new(c_and_a.clone()), Box::new(c_and_b.clone()));

        let root = ProofNode::derivation(
            conclusion,
            "CP",
            vec![
                ProofNode::assumption(c_and_a.clone()),
                ProofNode::derivation(c_and_b, "Conj", vec![
                    ProofNode::derivation(c.clone(), "Simp", vec![ProofNode::assumption(c_and_a.clone())], None),
                    ProofNode::derivation(b.clone(), "MP", vec![
                        ProofNode::premise(a_impl_b),
                        ProofNode::derivation(a.clone(), "Simp", vec![ProofNode::assumption(c_and_a)], None),
                    ], None),
                ], None),
            ],
            Some(Formula::And(Box::new(c.clone()), Box::new(a.clone()))),
        );
        ProofTree::new(root)
    }

    /// CP Variant 3: A⊃(B∧C), (B∧C)⊃D ⊢ A⊃D (forces CP, not HS shortcut)
    pub fn build_cp_variant_3(a: &Formula, b: &Formula, c: &Formula, d: &Formula) -> ProofTree {
        let b_and_c = Formula::And(Box::new(b.clone()), Box::new(c.clone()));
        let a_impl_bc = Formula::Implies(Box::new(a.clone()), Box::new(b_and_c.clone()));
        let bc_impl_d = Formula::Implies(Box::new(b_and_c.clone()), Box::new(d.clone()));
        let conclusion = Formula::Implies(Box::new(a.clone()), Box::new(d.clone()));

        let root = ProofNode::derivation(
            conclusion,
            "CP",
            vec![
                ProofNode::assumption(a.clone()),
                ProofNode::derivation(d.clone(), "MP", vec![
                    ProofNode::premise(bc_impl_d),
                    ProofNode::derivation(b_and_c, "MP", vec![
                        ProofNode::premise(a_impl_bc),
                        ProofNode::assumption(a.clone()),
                    ], None),
                ], None),
            ],
            Some(a.clone()),
        );
        ProofTree::new(root)
    }

    /// Basic Variant 1: A, A⊃B, B⊃C ⊢ C
    pub fn build_basic_variant_1(a: &Formula, b: &Formula, c: &Formula) -> ProofTree {
        let a_impl_b = Formula::Implies(Box::new(a.clone()), Box::new(b.clone()));
        let b_impl_c = Formula::Implies(Box::new(b.clone()), Box::new(c.clone()));

        let root = ProofNode::derivation(
            c.clone(),
            "MP",
            vec![
                ProofNode::premise(b_impl_c),
                ProofNode::derivation(b.clone(), "MP", vec![
                    ProofNode::premise(a_impl_b),
                    ProofNode::premise(a.clone()),
                ], None),
            ],
            None,
        );
        ProofTree::new(root)
    }

    /// Basic Variant 2: A∧B, (A∧B)⊃C ⊢ C
    pub fn build_basic_variant_2(a: &Formula, b: &Formula, c: &Formula) -> ProofTree {
        let a_and_b = Formula::And(Box::new(a.clone()), Box::new(b.clone()));
        let ab_impl_c = Formula::Implies(Box::new(a_and_b.clone()), Box::new(c.clone()));

        let root = ProofNode::derivation(
            c.clone(),
            "MP",
            vec![
                ProofNode::premise(ab_impl_c),
                ProofNode::premise(a_and_b),
            ],
            None,
        );
        ProofTree::new(root)
    }

    /// Basic Variant 3: A∨B, ~A, B⊃C ⊢ C
    pub fn build_basic_variant_3(a: &Formula, b: &Formula, c: &Formula) -> ProofTree {
        let a_or_b = Formula::Or(Box::new(a.clone()), Box::new(b.clone()));
        let not_a = Formula::Not(Box::new(a.clone()));
        let b_impl_c = Formula::Implies(Box::new(b.clone()), Box::new(c.clone()));

        let root = ProofNode::derivation(
            c.clone(),
            "MP",
            vec![
                ProofNode::premise(b_impl_c),
                ProofNode::derivation(b.clone(), "DS", vec![
                    ProofNode::premise(a_or_b),
                    ProofNode::premise(not_a),
                ], None),
            ],
            None,
        );
        ProofTree::new(root)
    }
}
