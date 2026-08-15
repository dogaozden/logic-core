//! Forward proof search: move enumeration and the greedy ("philosopher") policy.
//!
//! The philosopher simulates a diligent-but-strategically-blind prover: deterministic,
//! fixed rule priority, first productive move, no backtracking, no search. It measures
//! the honest grind length of a theorem and detects "hallways" (`single_path == true`)
//! where every move along the way was forced (no equally-productive alternative existed).

pub mod moves;
pub mod greedy;

pub use moves::{Move, forward_moves};
pub use greedy::{ProofStep, FoundProof, GreedyOutcome, greedy_prove};
