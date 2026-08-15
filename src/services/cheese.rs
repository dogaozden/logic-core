//! Cheese predicates: cheap, pre-prover rejections for degenerate theorems.
//!
//! These are microsecond-class gates — pure truth-table and syntactic checks —
//! that catch specific ways a theorem that already passed `validate_theorem`
//! can still be cheap/uninteresting, before the expensive prover ever runs:
//! - **Tautologous disjunct**: the conclusion (or its consequent, for an
//!   implication-shaped conclusion) is an Or whose disjuncts include one that's
//!   independently a tautology (e.g. `~P > ~P`), letting the whole thing be
//!   proven via Add off an empty subproof — the antecedent is decoration.
//! - **Subformula decoy**: a proper subformula of the antecedent (or of a
//!   premise) already entails the target on its own, meaning the rest of the
//!   antecedent/premise set is unused ballast.
//! - **Disguised identity**: an implication-shaped conclusion `A > B` / `~A v B`
//!   where `A` and `B` are semantically the same formula, just written a small
//!   number of equivalence-rewrites apart — "prove A > B" is secretly "restate
//!   A".
//!
//! None of these are exhaustive proofs of degeneracy — they're heuristic,
//! cheap-to-compute red flags meant to reject candidate theorems before they
//! reach the (much more expensive) prover stage.

use std::collections::HashSet;

use crate::models::rules::equivalence::EquivalenceRule;
use crate::models::Formula;

use super::truth_table::{are_equivalent, entails, is_tautology};

/// Report of cheap cheese checks run against a candidate theorem. Each field
/// is `None` when that particular defect wasn't found; all three checks run
/// independently, so a theorem can be flagged by more than one at once.
#[derive(Debug, Clone)]
pub struct CheeseReport {
    /// The first disjunct (of the conclusion's consequent, or of the
    /// conclusion itself if it isn't implication-shaped) that is
    /// independently a tautology — provable via Add without touching the
    /// antecedent.
    pub tautologous_disjunct: Option<Formula>,
    /// A proper subformula of a premise or of the antecedent that, alone,
    /// already entails the target — the rest of the premise/antecedent is
    /// unused.
    pub subformula_decoy: Option<Formula>,
    /// `Some(d)` if the conclusion is `A > B` / `~A v B` and `A` rewrites to
    /// `B` in `d` equivalence-rule applications (`d <= max_rewrite_distance`).
    pub identity_rewrite_distance: Option<usize>,
}

/// Run all three cheese checks against a candidate theorem.
///
/// `max_rewrite_distance` bounds the disguised-identity search (see
/// `rewrite_distance`); it does not affect the other two checks.
pub fn cheese_check(
    premises: &[Formula],
    conclusion: &Formula,
    max_rewrite_distance: usize,
) -> CheeseReport {
    let parts = implication_parts(conclusion);

    let disjunct_target = match &parts {
        Some((_, consequent)) => consequent.clone(),
        None => conclusion.clone(),
    };
    let tautologous_disjunct = flatten_or(&disjunct_target).into_iter().find(is_tautology);

    let mut subformula_decoy = parts
        .as_ref()
        .and_then(|(antecedent, consequent)| find_decoy(antecedent, consequent));
    if subformula_decoy.is_none() {
        for premise in premises {
            if let Some(decoy) = find_decoy(premise, conclusion) {
                subformula_decoy = Some(decoy);
                break;
            }
        }
    }

    let identity_rewrite_distance = parts
        .as_ref()
        .and_then(|(antecedent, consequent)| rewrite_distance(antecedent, consequent, max_rewrite_distance));

    CheeseReport { tautologous_disjunct, subformula_decoy, identity_rewrite_distance }
}

/// `A > B` -> `Some((A, B))`; `~A v B` -> `Some((A, B))`; anything else ->
/// `None`.
fn implication_parts(f: &Formula) -> Option<(Formula, Formula)> {
    match f {
        Formula::Implies(a, b) => Some((a.as_ref().clone(), b.as_ref().clone())),
        Formula::Or(left, b) => match left.as_ref() {
            Formula::Not(a) => Some((a.as_ref().clone(), b.as_ref().clone())),
            _ => None,
        },
        _ => None,
    }
}

/// Flatten a left/right-nested `Or` chain into its leaf disjuncts, left to
/// right. A non-`Or` formula flattens to the single-element list `[f]`.
fn flatten_or(f: &Formula) -> Vec<Formula> {
    match f {
        Formula::Or(left, right) => {
            let mut disjuncts = flatten_or(left.as_ref());
            disjuncts.extend(flatten_or(right.as_ref()));
            disjuncts
        }
        _ => vec![f.clone()],
    }
}

/// Find a proper subformula of `container` that, alone, already entails
/// `target` — i.e. the rest of `container` is unused ballast.
///
/// Skips `s` when it IS `container` (not a proper subformula) or is
/// semantically equivalent to it, and likewise skips `s` when it IS or is
/// equivalent to `target` itself: an atom buried several levels down that
/// happens to spell out the target verbatim (e.g. the `S` inside `R > S`
/// when the target is bare `S`) trivially "entails" it by reflexivity, which
/// isn't a meaningful decoy — it's just the target's own name showing up in
/// unrelated structure. Without this second skip, any antecedent chain that
/// mentions the target's atom anywhere (routine in ordinary Hypothetical-
/// Syllogism-style theorems, e.g. round9's `P.(R>S).(P>Q).(Q>R) > S`) would
/// false-positive on the atom nested inside `R > S`.
fn find_decoy(container: &Formula, target: &Formula) -> Option<Formula> {
    for s in container.subformulas() {
        if &s == container || are_equivalent(&s, container) {
            continue;
        }
        if &s == target || are_equivalent(&s, target) {
            continue;
        }
        if entails(std::slice::from_ref(&s), target) {
            return Some(s);
        }
    }
    None
}

/// Minimum number of single equivalence-rule applications needed to rewrite
/// `a` into exactly `b` (BFS over the rewrite graph), or `None` if `a` and
/// `b` aren't even semantically equivalent, or if no such path was found
/// within `max` steps / before the node cap was hit.
///
/// Each BFS edge is one `(path, rule, equivalent_forms result)` triple:
/// replace the subformula at `path` with one of its equivalent forms under
/// one rule. Visited formulas are deduped on `ascii_string()` rather than
/// `Formula` equality directly, per the task brief.
pub fn rewrite_distance(a: &Formula, b: &Formula, max: usize) -> Option<usize> {
    if !are_equivalent(a, b) {
        return None;
    }
    if a == b {
        return Some(0);
    }

    // Cap on distinct nodes visited across the whole search (not per depth).
    // If it's hit, we don't know whether `b` is reachable within `max` steps
    // or not — and since a `None` return here just means "disguised-identity
    // cheese not detected," staying permissive (None) rather than guessing is
    // the safe direction: a truncated search must never cause cheese_check to
    // reject a theorem it didn't actually verify is cheesy.
    const NODE_CAP: usize = 20_000;

    let rules = EquivalenceRule::all();
    let mut visited: HashSet<String> = HashSet::new();
    visited.insert(a.ascii_string());
    let mut frontier = vec![a.clone()];
    let mut node_count = 1usize;

    for depth in 1..=max {
        let mut next_frontier = Vec::new();
        for current in &frontier {
            for (path, sub) in current.subformulas_with_paths() {
                for rule in &rules {
                    for form in rule.equivalent_forms(sub) {
                        let candidate = current.replace_at_path(&path, &form);
                        if &candidate == b {
                            return Some(depth);
                        }
                        if visited.insert(candidate.ascii_string()) {
                            node_count += 1;
                            if node_count > NODE_CAP {
                                return None;
                            }
                            next_frontier.push(candidate);
                        }
                    }
                }
            }
        }
        if next_frontier.is_empty() {
            return None;
        }
        frontier = next_frontier;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        Formula::parse(s).unwrap()
    }

    #[test]
    fn round10_has_tautologous_disjunct() {
        let c = f("{[(R > ~P) v (P > P)] . {S > [(Q v ~S) > ~S]}} > [(P > ~R) v (~P > ~P)]");
        let r = cheese_check(&[], &c, 3);
        assert_eq!(r.tautologous_disjunct, Some(f("~P > ~P")));
    }

    #[test]
    fn round11_is_identity_at_distance_2() {
        let c = f("~{{[(~R v ~R) > R] . P} . [(S v S) > (Q v ~S)]} v {{[(R > ~R) > R] . P} . {~(Q v ~S) > ~(S v S)}}");
        let r = cheese_check(&[], &c, 3);
        assert_eq!(r.identity_rewrite_distance, Some(2));
    }

    #[test]
    fn round9_is_clean_of_cheese() {
        let c = f("{P . {(R > S) . [(P > Q) . (Q > R)]}} > S");
        let r = cheese_check(&[], &c, 3);
        assert!(
            r.tautologous_disjunct.is_none()
                && r.subformula_decoy.is_none()
                && r.identity_rewrite_distance.is_none()
        );
    }

    #[test]
    fn single_impl_rewrite_is_distance_1() {
        assert_eq!(rewrite_distance(&f("P > Q"), &f("~P v Q"), 3), Some(1));
        assert_eq!(rewrite_distance(&f("P"), &f("Q"), 3), None); // not even equivalent
    }
}
