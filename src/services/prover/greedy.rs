//! The greedy forward prover ("the philosopher"): deterministic, fixed-priority,
//! first-productive-move, no backtracking, no search.
//!
//! Its purpose is diagnostic, not competitive: it measures how many Fitch lines a
//! diligent-but-strategically-blind student would need to grind out a theorem, and
//! it flags "hallways" — theorems where the philosopher never faced a real choice
//! (`single_path == true`), counted per-iteration with no cross-iteration dedup.
//!
//! Round 9 is *not* an example of a hallway under this counting (RULED 2026-08-15,
//! see `round9_hallway_greedy_solves_single_path` and task-7-report.md): the
//! tournament record shows two distinct legal 11-line routes (the MP relay and a
//! "double-HS" route), so `single_path == false` there is correct — R9 genuinely
//! had a choice at several steps, even though greedy's fixed priority always took
//! the same one. R9 is still correctly flagged downstream, just by the serve
//! filter's divergence gate (greedy length vs. optimal length: no daylight)
//! instead of this hallway gate. The hallway gate remains meaningful for theorems
//! with literally zero legal alternatives anywhere along the path.

use crate::models::Formula;
use crate::models::rules::technique::ProofTechnique;
use super::moves::{forward_moves, Move};
use std::collections::HashSet;

/// One line of a found proof.
///
/// `cited` indices are positions in the flat `premises ++ steps` transcript: an
/// index `k < premises.len()` refers to `premises[k]`; otherwise it refers to
/// `steps[k - premises.len()]`.
#[derive(Debug, Clone)]
pub struct ProofStep {
    pub formula: Formula,
    pub rule: String,
    pub cited: Vec<usize>,
}

/// A completed proof: its line-by-line transcript and the Fitch line count.
#[derive(Debug, Clone)]
pub struct FoundProof {
    pub steps: Vec<ProofStep>,
    pub line_count: usize,
}

impl FoundProof {
    pub fn rules_used(&self) -> HashSet<String> {
        self.steps.iter().map(|s| s.rule.clone()).collect()
    }
}

/// Result of a greedy proof attempt.
#[derive(Debug, Clone)]
pub struct GreedyOutcome {
    pub proof: Option<FoundProof>,
    pub branch_points: usize,
    pub single_path: bool,
}

/// Run the greedy ("philosopher") policy against `goal` from `premises`.
///
/// Deterministic and non-backtracking: at each step it takes the highest-priority
/// productive mechanical move (`forward_moves`, priority order Simp/DeM/DN/MP/HS/
/// DS/MT/NegE/CD). When no mechanical move is productive, it falls back to exactly
/// one goal-directed structural attempt, chosen by the goal's shape — CP for an
/// Implies goal, Add for an Or goal with a disjunct already in hand, Conj for an And
/// goal with both conjuncts in hand, or (once, as the universal last resort) IP. If
/// that single structural attempt doesn't pan out, the call fails — the philosopher
/// never reconsiders or tries a second structural strategy for the same goal.
///
/// `max_lines` bounds the total number of Fitch lines this call (and everything it
/// recurses into) may add; CP/IP recursion reserves 2 of its remaining budget for
/// the assumption and discharge lines that wrap the subproof.
pub fn greedy_prove(premises: &[Formula], goal: &Formula, max_lines: usize) -> GreedyOutcome {
    let mut state: Vec<Formula> = premises.to_vec();
    let mut transcript: Vec<ProofStep> = Vec::new();
    let mut branch_points: usize = 0;
    let mut tried_ip = false;

    loop {
        if state.iter().any(|f| f == goal) {
            let single_path = branch_points == 0;
            return GreedyOutcome {
                proof: Some(FoundProof { line_count: transcript.len(), steps: transcript }),
                branch_points,
                single_path,
            };
        }

        if transcript.len() >= max_lines {
            return GreedyOutcome { proof: None, branch_points, single_path: branch_points == 0 };
        }

        // Mechanical candidates, already filtered against `state` by forward_moves.
        // Dedup by result formula, keeping the first (highest-priority) occurrence —
        // identical results from different rules must not inflate branch_points.
        let candidates = forward_moves(&state);
        let mut productive: Vec<&Move> = Vec::new();
        for mv in &candidates {
            if !productive.iter().any(|p| p.result == mv.result) {
                productive.push(mv);
            }
        }

        if !productive.is_empty() {
            branch_points += productive.len() - 1;
            let chosen = productive[0];
            state.push(chosen.result.clone());
            transcript.push(ProofStep {
                formula: chosen.result.clone(),
                rule: chosen.rule.to_string(),
                cited: chosen.cited.clone(),
            });
            continue;
        }

        // Stuck: exactly one goal-directed structural attempt, chosen by goal shape.
        let progressed = if let Formula::Implies(a, c) = goal {
            try_subproof(&mut state, &mut transcript, &mut branch_points, max_lines, ProofTechnique::ConditionalProof, a, c)
        } else if let Formula::Or(l, r) = goal {
            if state.contains(l.as_ref()) || state.contains(r.as_ref()) {
                try_add(&mut state, &mut transcript, max_lines, goal, l, r)
            } else if !tried_ip {
                tried_ip = true;
                try_ip(&mut state, &mut transcript, &mut branch_points, max_lines, goal)
            } else {
                false
            }
        } else if let Formula::And(l, r) = goal {
            if state.contains(l.as_ref()) && state.contains(r.as_ref()) {
                try_conj(&mut state, &mut transcript, max_lines, goal, l, r)
            } else if !tried_ip {
                tried_ip = true;
                try_ip(&mut state, &mut transcript, &mut branch_points, max_lines, goal)
            } else {
                false
            }
        } else if !tried_ip {
            tried_ip = true;
            try_ip(&mut state, &mut transcript, &mut branch_points, max_lines, goal)
        } else {
            false
        };

        if progressed {
            continue;
        }
        return GreedyOutcome { proof: None, branch_points, single_path: branch_points == 0 };
    }
}

/// Attempt a CP (Conditional Proof) subproof toward an `Implies(a, c)` goal: assume
/// `a`, recurse to prove `c`, and on success splice [assumption, sub.steps...,
/// discharge] into the caller's transcript. On failure, `state`/`transcript` are
/// left untouched (the recursive call never mutates the caller's copies).
fn try_subproof(
    state: &mut Vec<Formula>,
    transcript: &mut Vec<ProofStep>,
    branch_points: &mut usize,
    max_lines: usize,
    technique: ProofTechnique,
    a: &Formula,
    c: &Formula,
) -> bool {
    if transcript.len() + 2 > max_lines {
        return false;
    }
    let mut inner_premises = state.clone();
    inner_premises.push(a.clone());
    let sub_budget = max_lines - transcript.len() - 2;
    let sub = greedy_prove(&inner_premises, c, sub_budget);
    *branch_points += sub.branch_points;

    let Some(sub_proof) = sub.proof else { return false };

    let assumption_index = state.len();
    state.push(a.clone());
    transcript.push(ProofStep {
        formula: a.clone(),
        rule: format!("A{}", technique.abbreviation()),
        cited: vec![],
    });
    for step in sub_proof.steps {
        state.push(step.formula.clone());
        transcript.push(step);
    }
    let last_index = state.len() - 1;
    let conclusion = technique
        .get_conclusion(a, c)
        .expect("CP conclusion is always defined for an Implies goal");
    state.push(conclusion.clone());
    transcript.push(ProofStep {
        formula: conclusion,
        rule: technique.abbreviation().to_string(),
        cited: vec![assumption_index, last_index],
    });
    true
}

/// Attempt an IP (Indirect Proof) subproof toward `goal`: assume `~goal`, recurse to
/// derive a contradiction, and on success splice the subproof in exactly as CP does.
fn try_ip(
    state: &mut Vec<Formula>,
    transcript: &mut Vec<ProofStep>,
    branch_points: &mut usize,
    max_lines: usize,
    goal: &Formula,
) -> bool {
    if transcript.len() + 2 > max_lines {
        return false;
    }
    let assumption = Formula::Not(Box::new(goal.clone()));
    let mut inner_premises = state.clone();
    inner_premises.push(assumption.clone());
    let sub_budget = max_lines - transcript.len() - 2;
    let sub = greedy_prove(&inner_premises, &Formula::Contradiction, sub_budget);
    *branch_points += sub.branch_points;

    let Some(sub_proof) = sub.proof else { return false };

    let assumption_index = state.len();
    state.push(assumption.clone());
    transcript.push(ProofStep {
        formula: assumption.clone(),
        rule: "AIP".to_string(),
        cited: vec![],
    });
    for step in sub_proof.steps {
        state.push(step.formula.clone());
        transcript.push(step);
    }
    let last_index = state.len() - 1;
    let conclusion = ProofTechnique::IndirectProof
        .get_conclusion(&assumption, &Formula::Contradiction)
        .expect("IP conclusion is always defined once a contradiction is derived");
    state.push(conclusion.clone());
    transcript.push(ProofStep {
        formula: conclusion,
        rule: "IP".to_string(),
        cited: vec![assumption_index, last_index],
    });
    true
}

/// Attempt Add toward an `Or(l, r)` goal, given at least one disjunct is in `state`.
fn try_add(
    state: &mut Vec<Formula>,
    transcript: &mut Vec<ProofStep>,
    max_lines: usize,
    goal: &Formula,
    l: &Formula,
    r: &Formula,
) -> bool {
    if transcript.len() + 1 > max_lines {
        return false;
    }
    let cited_index = if let Some(idx) = state.iter().position(|f| f == l) {
        idx
    } else {
        state.iter().position(|f| f == r).expect("caller verified a disjunct is present")
    };
    state.push(goal.clone());
    transcript.push(ProofStep { formula: goal.clone(), rule: "Add".to_string(), cited: vec![cited_index] });
    true
}

/// Attempt Conj toward an `And(l, r)` goal, given both conjuncts are in `state`.
fn try_conj(
    state: &mut Vec<Formula>,
    transcript: &mut Vec<ProofStep>,
    max_lines: usize,
    goal: &Formula,
    l: &Formula,
    r: &Formula,
) -> bool {
    if transcript.len() + 1 > max_lines {
        return false;
    }
    let li = state.iter().position(|f| f == l).expect("caller verified left conjunct is present");
    let ri = state.iter().position(|f| f == r).expect("caller verified right conjunct is present");
    state.push(goal.clone());
    transcript.push(ProofStep { formula: goal.clone(), rule: "Conj".to_string(), cited: vec![li, ri] });
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        Formula::parse(s).unwrap()
    }

    // RULED (2026-08-15): single_path=false is correct, not a counting bug. The
    // tournament record shows Round 9 had two distinct legal 11-line routes (the MP
    // relay and the "double-HS" route), so choice-existence along the way is real —
    // the spec's literal "hallway = zero legal alternatives anywhere" definition
    // fails its own motivating example here. branch_points counting stays as
    // per-iteration, undeduped (see the trace in task-7-report.md). Round 9 is
    // still correctly rejected downstream — by the serve filter's divergence gate
    // (greedy 11 vs optimal ~11 → no daylight), not by the hallway gate. The
    // hallway gate remains meaningful for theorems with literally zero choice.
    #[test]
    fn round9_hallway_greedy_solves_single_path() {
        // 11 in tournament play; greedy reproduces it: 1 ACP + 6 Simp + 3 MP + 1 CP.
        let goal = f("{P . {(R > S) . [(P > Q) . (Q > R)]}} > S");
        let out = greedy_prove(&[], &goal, 40);
        let proof = out.proof.expect("greedy must solve the hallway");
        assert_eq!(proof.line_count, 11, "got {}", proof.line_count);
        assert!(!out.single_path, "R9 legitimately has route choices — tournament record: MP relay vs double-HS");
        assert!(out.branch_points > 0);
    }

    #[test]
    fn mp_chain_solves() {
        let premises = [f("P"), f("P > Q"), f("Q > R")];
        let out = greedy_prove(&premises, &f("R"), 10);
        assert_eq!(out.proof.unwrap().line_count, 2); // MP, MP
    }

    #[test]
    fn branching_detected() {
        // two independently-productive moves available → not single-path
        let premises = [f("P . Q"), f("R . S")];
        let out = greedy_prove(&premises, &f("P"), 10);
        assert!(!out.single_path);
    }

    #[test]
    fn unprovable_returns_none() {
        assert!(greedy_prove(&[f("Q")], &f("P"), 10).proof.is_none());
    }

    #[test]
    fn demorgan_unpack_is_mechanical() {
        // normalization, not strategy: ~(P v Q) → ~P . ~Q → ~P
        let out = greedy_prove(&[f("~(P v Q)")], &f("~P"), 10);
        assert_eq!(out.proof.unwrap().line_count, 2); // DeM, Simp
    }
}
