use rand::Rng;
use crate::models::Formula;
use super::super::proof_tree::ProofNode;
use super::super::fragments::Fragment;
use super::super::truth_table::{compute_truth_table, entails};
use super::context::{ConstructionContext, GenerationError};

// ============================================================================
// BACKWARD CONSTRUCTION ALGORITHM
// ============================================================================

/// Main backward construction function.
/// Builds a proof tree by working backward from the goal, validating at each step.
pub fn backward_construct(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    // Base case: depth exhausted
    if ctx.remaining_depth == 0 {
        return make_leaf(goal, ctx, rng);
    }

    // Check if goal is already available (from assumption or premise)
    if ctx.is_available(&goal) {
        // Use available formula - check if it's an assumption or premise
        let tt = compute_truth_table(&goal);
        if ctx.assumptions.iter().any(|a| compute_truth_table(a) == tt) {
            return Ok(ProofNode::assumption(goal));
        }
        // It's a premise - return a premise node
        return Ok(ProofNode::premise(goal));
    }

    // If we can commit goal as premise and have enough depth used already, just do it
    // This prevents over-complication and premise conflicts
    let used_so_far = ctx.atom_pool.len() * 2; // rough estimate of starting depth
    if ctx.remaining_depth <= used_so_far / 2 && ctx.can_commit_premise(&goal) {
        ctx.commit_premise(goal.clone());
        return Ok(ProofNode::premise(goal));
    }

    // Decrement depth for this step
    ctx.remaining_depth = ctx.remaining_depth.saturating_sub(1);

    // Pick a rule based on goal shape and requirements
    let rule = pick_rule_for_goal(&goal, ctx, rng);

    // Apply the rule backward - if it fails, try falling back to make_leaf
    match apply_rule_backward(rule, goal.clone(), ctx, rng) {
        Ok(node) => Ok(node),
        Err(_) => make_leaf(goal, ctx, rng),
    }
}

/// Create a leaf node (premise or assumption) when we can't go deeper
fn make_leaf(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    // First check if available as assumption
    let tt = compute_truth_table(&goal);
    if ctx.assumptions.iter().any(|a| compute_truth_table(a) == tt) {
        return Ok(ProofNode::assumption(goal));
    }

    // Check if already a premise (semantically)
    if ctx.premises.iter().any(|p| compute_truth_table(p) == tt) {
        // Find the matching premise and return it
        return Ok(ProofNode::premise(goal));
    }

    // Try to commit as new premise
    if ctx.can_commit_premise(&goal) {
        ctx.commit_premise(goal.clone());
        return Ok(ProofNode::premise(goal));
    }

    // Can't commit directly - try to find a safe formula to use as premise
    // and derive the goal from it via MP
    let mut atoms: Vec<_> = ctx.atom_pool.iter()
        .map(|a| Formula::Atom(a.clone()))
        .collect();

    // Shuffle for variety
    for i in (1..atoms.len()).rev() {
        let j = rng.gen_range(0..=i);
        atoms.swap(i, j);
    }

    for atom in atoms {
        if ctx.can_commit_premise(&atom) {
            let impl_formula = Formula::Implies(
                Box::new(atom.clone()),
                Box::new(goal.clone()),
            );
            if ctx.can_commit_premise(&impl_formula) {
                ctx.commit_premise(atom.clone());
                ctx.commit_premise(impl_formula.clone());
                return Ok(ProofNode::derivation(
                    goal,
                    "MP",
                    vec![
                        ProofNode::premise(impl_formula),
                        ProofNode::premise(atom),
                    ],
                    None,
                ));
            }
        }
    }

    Err(GenerationError::NoPremiseAvailable)
}

/// Choose which rule to apply backward based on goal shape and requirements
fn pick_rule_for_goal(
    goal: &Formula,
    ctx: &ConstructionContext,
    rng: &mut impl Rng,
) -> Fragment {
    let has_nesting = ctx.has_nesting_budget();

    // If we need CP and haven't used it yet, and goal is implication, prefer CP
    if ctx.required.need_cp && !ctx.required.used_cp {
        if let Formula::Implies(_, _) = goal {
            if has_nesting {
                return Fragment::CP;
            }
        }
    }

    // If we need case split and haven't used it yet, try to introduce one
    if ctx.required.need_case_split && !ctx.required.used_case_split {
        if has_nesting && rng.gen_bool(0.7) {
            return Fragment::CaseSplit;
        }
    }

    // Pick based on goal shape
    match goal {
        Formula::Implies(_, _) => {
            if has_nesting && rng.gen_bool(0.7) {
                Fragment::CP
            } else if rng.gen_bool(0.5) {
                Fragment::HS
            } else {
                Fragment::MP
            }
        }
        Formula::And(_, _) => Fragment::Conj,
        Formula::Or(_, _) => {
            let choice = rng.gen_range(0..3);
            match choice {
                0 => Fragment::Add,
                1 => Fragment::CD,
                _ => Fragment::DS,
            }
        }
        Formula::Not(_) => {
            if has_nesting && rng.gen_bool(0.5) {
                Fragment::NegIntro
            } else {
                Fragment::MT
            }
        }
        _ => {
            // Atoms and other formulas
            let choice = rng.gen_range(0..10);
            match choice {
                0..=4 => Fragment::MP,
                5..=6 => Fragment::DS,
                7..=8 => Fragment::Simp,
                _ if has_nesting => Fragment::CaseSplit,
                _ => Fragment::MP,
            }
        }
    }
}

/// Apply a rule backward to construct a proof of the goal
fn apply_rule_backward(
    rule: Fragment,
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    match rule {
        Fragment::MP => apply_mp_backward(goal, ctx, rng),
        Fragment::MT => apply_mt_backward(goal, ctx, rng),
        Fragment::HS => apply_hs_backward(goal, ctx, rng),
        Fragment::DS => apply_ds_backward(goal, ctx, rng),
        Fragment::Simp => apply_simp_backward(goal, ctx, rng),
        Fragment::Conj => apply_conj_backward(goal, ctx, rng),
        Fragment::Add => apply_add_backward(goal, ctx, rng),
        Fragment::CD => apply_cd_backward(goal, ctx, rng),
        Fragment::CP => apply_cp_backward(goal, ctx, rng),
        Fragment::IP => apply_ip_backward(goal, ctx, rng),
        Fragment::NegIntro => apply_neg_intro_backward(goal, ctx, rng),
        Fragment::CaseSplit => apply_case_split_backward(goal, ctx, rng),
    }
}

// ============================================================================
// RULE BACKWARD APPLICATIONS
// ============================================================================

/// MP backward: goal B needs A and A⊃B
fn apply_mp_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    // Prefer using an atom that can be safely committed as A
    let a = {
        // Try to find a safe atom first
        let mut atoms: Vec<_> = ctx.atom_pool.iter()
            .map(|name| Formula::Atom(name.clone()))
            .collect();

        // Shuffle for variety
        for i in (1..atoms.len()).rev() {
            let j = rng.gen_range(0..=i);
            atoms.swap(i, j);
        }

        // Find one that can be committed (or already is committed/available)
        atoms.into_iter()
            .find(|atom| ctx.is_available(atom) || ctx.can_commit_premise(atom))
            .unwrap_or_else(|| ctx.random_atom(rng))
    };

    let implication = Formula::Implies(Box::new(a.clone()), Box::new(goal.clone()));

    let child_impl = backward_construct(implication, ctx, rng)?;
    let child_a = backward_construct(a, ctx, rng)?;

    Ok(ProofNode::derivation(goal, "MP", vec![child_impl, child_a], None))
}

/// MT backward: goal ~A needs A⊃B and ~B
fn apply_mt_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    match &goal {
        Formula::Not(a) => {
            // Prefer a safe atom for B
            let b = ctx.random_atom(rng);
            let implication = Formula::Implies(a.clone(), Box::new(b.clone()));
            let not_b = Formula::Not(Box::new(b));

            let child_impl = backward_construct(implication, ctx, rng)?;
            let child_not_b = backward_construct(not_b, ctx, rng)?;

            Ok(ProofNode::derivation(goal, "MT", vec![child_impl, child_not_b], None))
        }
        _ => {
            // Fall back to MP for non-negation goals
            apply_mp_backward(goal, ctx, rng)
        }
    }
}

/// HS backward: goal A⊃C needs A⊃B and B⊃C
fn apply_hs_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    match &goal {
        Formula::Implies(a, c) => {
            // Use a simple atom for B to avoid complexity
            let b = Box::new(ctx.random_atom(rng));
            let a_impl_b = Formula::Implies(a.clone(), b.clone());
            let b_impl_c = Formula::Implies(b, c.clone());

            let child1 = backward_construct(a_impl_b, ctx, rng)?;
            let child2 = backward_construct(b_impl_c, ctx, rng)?;

            Ok(ProofNode::derivation(goal, "HS", vec![child1, child2], None))
        }
        _ => apply_mp_backward(goal, ctx, rng),
    }
}

/// DS backward: goal B needs A∨B and ~A
fn apply_ds_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    // Use a simple atom for the "other" part
    let other = ctx.random_atom(rng);
    let disjunction = if rng.gen_bool(0.5) {
        Formula::Or(Box::new(other.clone()), Box::new(goal.clone()))
    } else {
        Formula::Or(Box::new(goal.clone()), Box::new(other.clone()))
    };
    let negated = Formula::Not(Box::new(other));

    let child_disj = backward_construct(disjunction, ctx, rng)?;
    let child_neg = backward_construct(negated, ctx, rng)?;

    Ok(ProofNode::derivation(goal, "DS", vec![child_disj, child_neg], None))
}

/// Simp backward: goal A needs A∧B
fn apply_simp_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    // Use a simple atom for the "other" part
    let other = ctx.random_atom(rng);
    let conjunction = if rng.gen_bool(0.5) {
        Formula::And(Box::new(goal.clone()), Box::new(other))
    } else {
        Formula::And(Box::new(other), Box::new(goal.clone()))
    };

    let child = backward_construct(conjunction, ctx, rng)?;
    Ok(ProofNode::derivation(goal, "Simp", vec![child], None))
}

/// Conj backward: goal A∧B needs A and B
fn apply_conj_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    match &goal {
        Formula::And(a, b) => {
            let child_a = backward_construct((**a).clone(), ctx, rng)?;
            let child_b = backward_construct((**b).clone(), ctx, rng)?;
            Ok(ProofNode::derivation(goal, "Conj", vec![child_a, child_b], None))
        }
        _ => apply_mp_backward(goal, ctx, rng),
    }
}

/// Add backward: goal A∨B needs either A or B
fn apply_add_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    match &goal {
        Formula::Or(a, b) => {
            let prove_this = if rng.gen_bool(0.5) {
                (**a).clone()
            } else {
                (**b).clone()
            };

            let child = backward_construct(prove_this, ctx, rng)?;
            Ok(ProofNode::derivation(goal, "Add", vec![child], None))
        }
        _ => apply_mp_backward(goal, ctx, rng),
    }
}

/// CD backward: goal C∨D needs A∨B, A⊃C, B⊃D
fn apply_cd_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    match &goal {
        Formula::Or(c, d) => {
            // Use simple atoms for A and B
            let a = ctx.random_atom(rng);
            let b = ctx.random_atom(rng);
            let disjunction = Formula::Or(Box::new(a.clone()), Box::new(b.clone()));
            let a_impl_c = Formula::Implies(Box::new(a), c.clone());
            let b_impl_d = Formula::Implies(Box::new(b), d.clone());

            let child_disj = backward_construct(disjunction, ctx, rng)?;
            let child_ac = backward_construct(a_impl_c, ctx, rng)?;
            let child_bd = backward_construct(b_impl_d, ctx, rng)?;

            Ok(ProofNode::derivation(goal, "CD", vec![child_disj, child_ac, child_bd], None))
        }
        _ => apply_mp_backward(goal, ctx, rng),
    }
}

/// CP backward: goal A⊃B needs subproof [assume A, derive B]
/// CRITICAL: Validates that premises don't already entail B (would make CP trivial)
fn apply_cp_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    // Extract antecedent and consequent if goal is an implication
    let (antecedent, consequent) = match &goal {
        Formula::Implies(a, c) => ((**a).clone(), (**c).clone()),
        _ => return apply_mp_backward(goal, ctx, rng),
    };

    // CRITICAL CHECK: Premises alone must NOT entail the consequent
    // If they do, CP is trivial (could just derive B directly, then wrap)
    if entails(&ctx.premises, &consequent) {
        return Err(GenerationError::TrivialCP);
    }

    // Enter subproof with assumption
    let mut subproof_ctx = ctx.enter_subproof(antecedent.clone());

    // Build proof of consequent with assumption available
    let cons_proof = backward_construct(consequent, &mut subproof_ctx, rng)?;

    // Mark CP as truly used
    ctx.required.used_cp = true;

    // Merge technique usage flags from subproof
    // If case split was used inside this CP subproof, mark it
    if subproof_ctx.required.used_case_split {
        ctx.required.used_case_split = true;
        ctx.required.case_split_inside_cp = true;
    }

    // Merge discovered premises from subproof back to main context
    for premise in &subproof_ctx.premises {
        if !ctx.premises.iter().any(|p| compute_truth_table(p) == compute_truth_table(premise)) {
            let _ = ctx.commit_premise(premise.clone());
        }
    }

    Ok(ProofNode::derivation(
        goal,
        "CP",
        vec![ProofNode::assumption(antecedent.clone()), cons_proof],
        Some(antecedent),
    ))
}

/// IP backward: goal A needs subproof [assume ~A, derive ⊥]
fn apply_ip_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    let assumption = Formula::Not(Box::new(goal.clone()));

    // Enter subproof with negation of goal as assumption
    let mut subproof_ctx = ctx.enter_subproof(assumption.clone());

    // Build proof of contradiction
    let contra_proof = build_contradiction_backward(&mut subproof_ctx, rng)?;

    // Mark IP as used
    ctx.required.used_ip = true;

    // Merge premises
    for premise in &subproof_ctx.premises {
        if !ctx.premises.iter().any(|p| compute_truth_table(p) == compute_truth_table(premise)) {
            let _ = ctx.commit_premise(premise.clone());
        }
    }

    Ok(ProofNode::derivation(
        goal,
        "IP",
        vec![ProofNode::assumption(assumption.clone()), contra_proof],
        Some(assumption),
    ))
}

/// NegIntro backward: goal ~A needs subproof [assume A, derive ⊥]
fn apply_neg_intro_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    match &goal {
        Formula::Not(a) => {
            let assumption = (**a).clone();

            // Enter subproof with what we want to negate
            let mut subproof_ctx = ctx.enter_subproof(assumption.clone());

            // Build proof of contradiction
            let contra_proof = build_contradiction_backward(&mut subproof_ctx, rng)?;

            // Merge premises
            for premise in &subproof_ctx.premises {
                if !ctx.premises.iter().any(|p| compute_truth_table(p) == compute_truth_table(premise)) {
                    let _ = ctx.commit_premise(premise.clone());
                }
            }

            Ok(ProofNode::derivation(
                goal,
                "NegIntro",
                vec![ProofNode::assumption(assumption.clone()), contra_proof],
                Some(assumption),
            ))
        }
        _ => apply_ip_backward(goal, ctx, rng),
    }
}

/// CaseSplit backward: goal G needs A∨B and subproofs [A→G], [B→G]
/// CRITICAL: Validates that neither ~A nor ~B is committable as premise (would allow DS instead)
fn apply_case_split_backward(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    // Generate disjuncts using simple atoms
    let atoms: Vec<_> = ctx.atom_pool.iter().map(|a| Formula::Atom(a.clone())).collect();
    let left_idx = rng.gen_range(0..atoms.len());
    let mut right_idx = rng.gen_range(0..atoms.len());
    // Try to pick different atoms
    for _ in 0..3 {
        if right_idx != left_idx {
            break;
        }
        right_idx = rng.gen_range(0..atoms.len());
    }

    let left = atoms[left_idx].clone();
    let right = atoms[right_idx].clone();

    // CRITICAL CHECK: Neither ~left nor ~right should be committable as premise
    // If they are, DS would work instead of case split
    let neg_left = Formula::Not(Box::new(left.clone()));
    let neg_right = Formula::Not(Box::new(right.clone()));

    if ctx.can_commit_premise(&neg_left) || ctx.can_commit_premise(&neg_right) {
        return Err(GenerationError::DSAvailable);
    }

    let disjunction = Formula::Or(Box::new(left.clone()), Box::new(right.clone()));

    // Prove disjunction - this needs to be a premise
    let disj_proof = if ctx.can_commit_premise(&disjunction) {
        ctx.commit_premise(disjunction.clone());
        ProofNode::premise(disjunction)
    } else {
        backward_construct(disjunction.clone(), ctx, rng)?
    };

    // Check if we need to force CP inside the case split branches
    let need_cp_in_branch = ctx.required.need_cp && !ctx.required.used_cp;

    // Case 1: assume left, prove goal
    let mut case1_ctx = ctx.enter_subproof(left.clone());
    let case1_proof = if need_cp_in_branch && case1_ctx.has_nesting_budget() {
        // Force CP inside this branch for proper nesting
        force_cp_in_branch(goal.clone(), &mut case1_ctx, rng)?
    } else {
        backward_construct(goal.clone(), &mut case1_ctx, rng)?
    };

    // Case 2: assume right, prove goal
    let mut case2_ctx = ctx.enter_subproof(right.clone());
    let case2_proof = if need_cp_in_branch && !case1_ctx.required.used_cp && case2_ctx.has_nesting_budget() {
        // Force CP in branch 2 if branch 1 didn't use it
        force_cp_in_branch(goal.clone(), &mut case2_ctx, rng)?
    } else {
        backward_construct(goal.clone(), &mut case2_ctx, rng)?
    };

    // Mark case split as used
    ctx.required.used_case_split = true;

    // Merge technique usage flags from branches
    // If CP was used in either branch, mark it as cp_inside_case_split
    if case1_ctx.required.used_cp || case2_ctx.required.used_cp {
        ctx.required.used_cp = true;
        ctx.required.cp_inside_case_split = true;
    }

    // Merge premises from both cases
    for premise in &case1_ctx.premises {
        if !ctx.premises.iter().any(|p| compute_truth_table(p) == compute_truth_table(premise)) {
            let _ = ctx.commit_premise(premise.clone());
        }
    }
    for premise in &case2_ctx.premises {
        if !ctx.premises.iter().any(|p| compute_truth_table(p) == compute_truth_table(premise)) {
            let _ = ctx.commit_premise(premise.clone());
        }
    }

    Ok(ProofNode::derivation(
        goal,
        "CaseSplit",
        vec![
            disj_proof,
            ProofNode::assumption(left.clone()),
            case1_proof,
            ProofNode::assumption(right.clone()),
            case2_proof,
        ],
        None,
    ))
}

/// Force CP to be used within a case split branch.
/// Creates an intermediate implication that requires CP to prove, then uses MP to get the goal.
fn force_cp_in_branch(
    goal: Formula,
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    // Create an intermediate formula X that we can use as antecedent
    let intermediate = ctx.random_atom(rng);

    // Create the conditional: X ⊃ goal
    let conditional = Formula::Implies(Box::new(intermediate.clone()), Box::new(goal.clone()));

    // Prove the conditional using CP - this MUST use CP
    let cp_proof = apply_cp_backward(conditional.clone(), ctx, rng)?;

    // If CP failed or wasn't used, fall back to regular construction
    if !ctx.required.used_cp {
        return backward_construct(goal, ctx, rng);
    }

    // Prove the antecedent X
    let ant_proof = backward_construct(intermediate.clone(), ctx, rng)?;

    // Combine via MP: (X ⊃ goal), X ⊢ goal
    Ok(ProofNode::derivation(
        goal,
        "MP",
        vec![cp_proof, ant_proof],
        None,
    ))
}

/// Build a proof of contradiction (⊥)
fn build_contradiction_backward(
    ctx: &mut ConstructionContext,
    rng: &mut impl Rng,
) -> Result<ProofNode, GenerationError> {
    // Try to find P and ~P among available formulas
    let available: Vec<Formula> = ctx.premises.iter().chain(ctx.assumptions.iter()).cloned().collect();

    for f in &available {
        let neg = Formula::Not(Box::new(f.clone()));
        let neg_tt = compute_truth_table(&neg);
        if available.iter().any(|a| compute_truth_table(a) == neg_tt) {
            // Found P and ~P
            return Ok(ProofNode::derivation(
                Formula::Contradiction,
                "NegE",
                vec![
                    if ctx.assumptions.iter().any(|a| compute_truth_table(a) == compute_truth_table(f)) {
                        ProofNode::assumption(f.clone())
                    } else {
                        ProofNode::premise(f.clone())
                    },
                    if ctx.assumptions.iter().any(|a| compute_truth_table(a) == neg_tt) {
                        ProofNode::assumption(neg)
                    } else {
                        ProofNode::premise(neg)
                    },
                ],
                None,
            ));
        }

        // Check if f is ~P and P is available
        if let Formula::Not(inner) = f {
            let inner_tt = compute_truth_table(inner);
            if available.iter().any(|a| compute_truth_table(a) == inner_tt) {
                return Ok(ProofNode::derivation(
                    Formula::Contradiction,
                    "NegE",
                    vec![
                        if ctx.assumptions.iter().any(|a| compute_truth_table(a) == inner_tt) {
                            ProofNode::assumption((**inner).clone())
                        } else {
                            ProofNode::premise((**inner).clone())
                        },
                        if ctx.assumptions.iter().any(|a| compute_truth_table(a) == compute_truth_table(f)) {
                            ProofNode::assumption(f.clone())
                        } else {
                            ProofNode::premise(f.clone())
                        },
                    ],
                    None,
                ));
            }
        }
    }

    // No direct contradiction available - need to derive one
    // IMPORTANT: To avoid creating contradictory premises, we need to derive
    // the contradiction using an assumption and a premise that don't conflict.
    // The most reliable way is to use the assumption in this subproof as one half
    // of the contradiction.

    // Clone assumptions to avoid borrow issues
    let assumptions_copy: Vec<Formula> = ctx.assumptions.clone();

    // Check if any assumption can be contradicted by a committable premise
    for assumption in &assumptions_copy {
        let neg_assumption = Formula::Not(Box::new(assumption.clone()));
        if ctx.can_commit_premise(&neg_assumption) {
            ctx.commit_premise(neg_assumption.clone());
            return Ok(ProofNode::derivation(
                Formula::Contradiction,
                "NegE",
                vec![
                    ProofNode::assumption(assumption.clone()),
                    ProofNode::premise(neg_assumption),
                ],
                None,
            ));
        }

        // If assumption is ~P, check if P can be committed
        if let Formula::Not(inner) = assumption {
            if ctx.can_commit_premise(inner) {
                ctx.commit_premise((**inner).clone());
                return Ok(ProofNode::derivation(
                    Formula::Contradiction,
                    "NegE",
                    vec![
                        ProofNode::premise((**inner).clone()),
                        ProofNode::assumption(assumption.clone()),
                    ],
                    None,
                ));
            }
        }
    }

    // Last resort: pick an atom, derive both it and its negation
    // This will likely fail due to premise conflicts, but try anyway
    let p = ctx.random_atom(rng);
    let not_p = Formula::Not(Box::new(p.clone()));

    // Try to make one of them the premise and derive the other
    if ctx.can_commit_premise(&p) {
        ctx.commit_premise(p.clone());
        let child_not_p = backward_construct(not_p.clone(), ctx, rng)?;
        return Ok(ProofNode::derivation(
            Formula::Contradiction,
            "NegE",
            vec![ProofNode::premise(p), child_not_p],
            None,
        ));
    } else if ctx.can_commit_premise(&not_p) {
        ctx.commit_premise(not_p.clone());
        let child_p = backward_construct(p.clone(), ctx, rng)?;
        return Ok(ProofNode::derivation(
            Formula::Contradiction,
            "NegE",
            vec![child_p, ProofNode::premise(not_p)],
            None,
        ));
    }

    Err(GenerationError::CannotProve)
}
