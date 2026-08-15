//! Forward move enumeration.
//!
//! `forward_moves` enumerates every mechanically-available next step from a proof
//! state: the eight forward inference rules (MP, MT, DS, Simp, HS, Add is excluded —
//! see below, CD, NegE) plus two terminating normalization rewrites (inward DeMorgan,
//! DN-strip). Rules are hand-rolled per Formula pattern rather than routed through
//! `InferenceRule::all_conclusions` so each rule's iteration (single formula, pair,
//! or CD's triple) stays under direct control.
//!
//! `Conj` and `Add` are intentionally omitted: both require a target formula that
//! isn't derivable from the state alone (Add needs an arbitrary formula to disjoin
//! in; Conj is only useful once you know what conjunction you're building toward).
//! Both are goal-directed and are handled by the provers that consume this module.
//!
//! Every emitted `Move.result` is guaranteed not to already equal a formula in
//! `state` (redundant conclusions are skipped at the source).

use crate::models::Formula;

/// One candidate forward step: apply `rule` to formula(s) at `cited` indices in the
/// state slice passed to `forward_moves`, producing `result`.
#[derive(Debug, Clone)]
pub struct Move {
    pub result: Formula,
    pub rule: &'static str,
    pub cited: Vec<usize>,
}

/// Enumerate every non-redundant forward move available from `state`.
///
/// Moves are emitted in fixed rule-priority order — Simp, DeM, DN, MP, HS, DS, MT,
/// NegE, CD — so callers that want "first move in priority order" can simply take
/// the first (deduped) entry.
pub fn forward_moves(state: &[Formula]) -> Vec<Move> {
    let mut moves = Vec::new();
    let is_new = |state: &[Formula], f: &Formula| !state.contains(f);

    // Simp: p . q ⊢ p, and p . q ⊢ q — every And in state, both conjuncts.
    for (i, f) in state.iter().enumerate() {
        if let Formula::And(left, right) = f {
            if is_new(state, left) {
                moves.push(Move { result: (**left).clone(), rule: "Simp", cited: vec![i] });
            }
            if is_new(state, right) {
                moves.push(Move { result: (**right).clone(), rule: "Simp", cited: vec![i] });
            }
        }
    }

    // DeM (inward only): ~(A . B) ⊢ ~A ∨ ~B ; ~(A ∨ B) ⊢ ~A . ~B.
    // Never the reverse (outward) direction — that would undo normalization.
    for (i, f) in state.iter().enumerate() {
        if let Formula::Not(inner) = f {
            match inner.as_ref() {
                Formula::And(a, b) => {
                    let result = Formula::Or(
                        Box::new(Formula::Not(a.clone())),
                        Box::new(Formula::Not(b.clone())),
                    );
                    if is_new(state, &result) {
                        moves.push(Move { result, rule: "DeM", cited: vec![i] });
                    }
                }
                Formula::Or(a, b) => {
                    let result = Formula::And(
                        Box::new(Formula::Not(a.clone())),
                        Box::new(Formula::Not(b.clone())),
                    );
                    if is_new(state, &result) {
                        moves.push(Move { result, rule: "DeM", cited: vec![i] });
                    }
                }
                _ => {}
            }
        }
    }

    // DN-strip: ~~X ⊢ X. Never the introduction direction.
    for (i, f) in state.iter().enumerate() {
        if let Formula::Not(inner) = f {
            if let Formula::Not(inner2) = inner.as_ref() {
                let result = (**inner2).clone();
                if is_new(state, &result) {
                    moves.push(Move { result, rule: "DN", cited: vec![i] });
                }
            }
        }
    }

    // MP: p ⊃ q, p ⊢ q — every Implies × every matching antecedent elsewhere in state.
    for (i, f) in state.iter().enumerate() {
        if let Formula::Implies(antecedent, consequent) = f {
            for (j, g) in state.iter().enumerate() {
                if i == j {
                    continue;
                }
                if g == antecedent.as_ref() && is_new(state, consequent) {
                    moves.push(Move {
                        result: (**consequent).clone(),
                        rule: "MP",
                        cited: vec![i, j],
                    });
                }
            }
        }
    }

    // HS: p ⊃ q, q ⊃ r ⊢ p ⊃ r — every compatible pair of implications.
    for (i, f) in state.iter().enumerate() {
        if let Formula::Implies(p, q1) = f {
            for (j, g) in state.iter().enumerate() {
                if i == j {
                    continue;
                }
                if let Formula::Implies(q2, r) = g {
                    if q1.as_ref() == q2.as_ref() {
                        let result = Formula::Implies(p.clone(), r.clone());
                        if is_new(state, &result) {
                            moves.push(Move { result, rule: "HS", cited: vec![i, j] });
                        }
                    }
                }
            }
        }
    }

    // DS: p ∨ q, ~p ⊢ q  and  p ∨ q, ~q ⊢ p — both directions.
    for (i, f) in state.iter().enumerate() {
        if let Formula::Or(left, right) = f {
            for (j, g) in state.iter().enumerate() {
                if i == j {
                    continue;
                }
                if let Formula::Not(negated) = g {
                    if negated.as_ref() == left.as_ref() && is_new(state, right) {
                        moves.push(Move {
                            result: (**right).clone(),
                            rule: "DS",
                            cited: vec![i, j],
                        });
                    }
                    if negated.as_ref() == right.as_ref() && is_new(state, left) {
                        moves.push(Move {
                            result: (**left).clone(),
                            rule: "DS",
                            cited: vec![i, j],
                        });
                    }
                }
            }
        }
    }

    // MT: p ⊃ q, ~q ⊢ ~p — every Implies × every matching negated consequent.
    for (i, f) in state.iter().enumerate() {
        if let Formula::Implies(antecedent, consequent) = f {
            for (j, g) in state.iter().enumerate() {
                if i == j {
                    continue;
                }
                if let Formula::Not(negated) = g {
                    if negated.as_ref() == consequent.as_ref() {
                        let result = Formula::Not(antecedent.clone());
                        if is_new(state, &result) {
                            moves.push(Move { result, rule: "MT", cited: vec![i, j] });
                        }
                    }
                }
            }
        }
    }

    // NegE: p, ~p ⊢ ⊥ — every contradictory pair (each pair found exactly once).
    if is_new(state, &Formula::Contradiction) {
        for (i, f) in state.iter().enumerate() {
            for (j, g) in state.iter().enumerate() {
                if i == j {
                    continue;
                }
                if let Formula::Not(negated) = g {
                    if negated.as_ref() == f {
                        moves.push(Move {
                            result: Formula::Contradiction,
                            rule: "NegE",
                            cited: vec![i, j],
                        });
                    }
                }
            }
        }
    }

    // CD: p ∨ q, p ⊃ r, q ⊃ s ⊢ r ∨ s — every disjunction × two matching implications.
    // O(n^3); kept last in priority so it rarely runs against a large state.
    for (i, f) in state.iter().enumerate() {
        if let Formula::Or(p, q) = f {
            for (j, g) in state.iter().enumerate() {
                if j == i {
                    continue;
                }
                if let Formula::Implies(p2, r) = g {
                    if p2.as_ref() != p.as_ref() {
                        continue;
                    }
                    for (k, h) in state.iter().enumerate() {
                        if k == i || k == j {
                            continue;
                        }
                        if let Formula::Implies(q2, s) = h {
                            if q2.as_ref() == q.as_ref() {
                                let result = Formula::Or(r.clone(), s.clone());
                                if is_new(state, &result) {
                                    moves.push(Move {
                                        result,
                                        rule: "CD",
                                        cited: vec![i, j, k],
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    moves
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        Formula::parse(s).unwrap()
    }

    #[test]
    fn simp_emits_both_conjuncts() {
        let state = [f("P & Q")];
        let moves = forward_moves(&state);
        assert!(moves.iter().any(|m| m.rule == "Simp" && m.result == f("P")));
        assert!(moves.iter().any(|m| m.rule == "Simp" && m.result == f("Q")));
    }

    #[test]
    fn demorgan_is_inward_only() {
        // ~(P . Q) -> ~P v ~Q fires.
        let state = [f("~(P & Q)")];
        let moves = forward_moves(&state);
        assert!(moves.iter().any(|m| m.rule == "DeM" && m.result == f("~P | ~Q")));

        // The reverse (outward) direction never fires: ~P v ~Q does NOT produce ~(P.Q).
        let state2 = [f("~P | ~Q")];
        let moves2 = forward_moves(&state2);
        assert!(!moves2.iter().any(|m| m.rule == "DeM"));
    }

    #[test]
    fn dn_strip_is_elimination_only() {
        let state = [f("~~P")];
        let moves = forward_moves(&state);
        assert!(moves.iter().any(|m| m.rule == "DN" && m.result == f("P")));

        // Introduction direction never fires: P alone does not offer ~~P.
        let state2 = [f("P")];
        let moves2 = forward_moves(&state2);
        assert!(!moves2.iter().any(|m| m.rule == "DN"));
    }

    #[test]
    fn mp_and_mt_fire() {
        let state = [f("P"), f("P > Q"), f("~Q")];
        let moves = forward_moves(&state);
        assert!(moves.iter().any(|m| m.rule == "MP" && m.result == f("Q")));
        assert!(moves.iter().any(|m| m.rule == "MT" && m.result == f("~P")));
    }

    #[test]
    fn hs_fires_on_compatible_pair() {
        let state = [f("P > Q"), f("Q > R")];
        let moves = forward_moves(&state);
        assert!(moves.iter().any(|m| m.rule == "HS" && m.result == f("P > R")));
    }

    #[test]
    fn ds_fires_both_directions() {
        let state = [f("P | Q"), f("~P")];
        let moves = forward_moves(&state);
        assert!(moves.iter().any(|m| m.rule == "DS" && m.result == f("Q")));

        let state2 = [f("P | Q"), f("~Q")];
        let moves2 = forward_moves(&state2);
        assert!(moves2.iter().any(|m| m.rule == "DS" && m.result == f("P")));
    }

    #[test]
    fn cd_fires_on_matching_triple() {
        let state = [f("P | Q"), f("P > R"), f("Q > S")];
        let moves = forward_moves(&state);
        assert!(moves.iter().any(|m| m.rule == "CD" && m.result == f("R | S")));
    }

    #[test]
    fn neg_e_fires_on_contradictory_pair() {
        let state = [f("P"), f("~P")];
        let moves = forward_moves(&state);
        assert!(moves.iter().any(|m| m.rule == "NegE" && m.result == Formula::Contradiction));
    }

    #[test]
    fn no_conj_or_add_moves_ever_emitted() {
        let state = [f("P"), f("Q"), f("P | R")];
        let moves = forward_moves(&state);
        assert!(!moves.iter().any(|m| m.rule == "Conj" || m.rule == "Add"));
    }

    #[test]
    fn results_already_in_state_are_skipped() {
        // P & Q with both P and Q already present must not re-offer them.
        let state = [f("P & Q"), f("P"), f("Q")];
        let moves = forward_moves(&state);
        assert!(moves.is_empty(), "expected no moves, got {:?}", moves);
    }
}
