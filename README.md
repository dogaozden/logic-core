# logic-core

The propositional and predicate logic proof engine behind
[PropBench](https://github.com/dogaozden/prop-bench) and
[Logic Proof Trainer](https://github.com/dogaozden/logic-proof-trainer).

Formula representation and parsing, natural-deduction inference and equivalence
rules, conditional and indirect proof, proof verification, truth tables, and
theorem generation by difficulty tier.

No UI and no application code — both products build their own layer on top.

## Predicate logic and set theory (v0.4)

Formulas also have predicates `F(a)`, `R(a, b)`, identity `a = b` / `a ≠ b`, membership
`a ∈ b` / `a ∉ b`, inclusion `a ⊆ b`, and quantifiers `∀x φ`, `∃x φ` (ASCII `\A x`, `\E x`,
or Hurley's `(x)φ`, `(∃x)φ`). Terms are names (a lowercase letter plus digits or primes),
`f(t)`, and the set-theory operators `∅`, `{a}`, `{a, b}`, `⟨a, b⟩`, `a ∪ b`, `a ∩ b`,
`a − b`, `℘(a)`, `⋃a`. A name is a variable where a quantifier binds it.

| Rule | Hurley | Form | Strictness |
|------|--------|------|-----------|
| ∀E | UI | ∀x φ ∴ φ[t/x] | one term for every free x; no capture |
| ∀I | UG | φ[c/x] ∴ ∀x φ | c in no premise or open assumption; every c generalized |
| ∃I | EG | φ[t/x] ∴ ∃x φ | replaces some or all occurrences of t; no capture |
| ∃E | EI | ∃x φ, [φ[c/x] … ψ] ∴ ψ | subproof; c new (not in ∃x φ, premises, open assumptions); c may not escape into ψ |
| =I | Id | ∴ t = t | |
| =E | Id | a = b, φ ∴ φ′ | some free a ↔ b; no capture |
| QN | QN | ~∀xφ :: ∃x~φ, ~∃xφ :: ∀x~φ | replacement, anywhere |
| Def | | unfold/fold ⊆ ∅ {a} {a,b} ∪ ∩ − ℘ ⋃ ⟨a,b⟩ | replacement, anywhere |

Replacement results are compared up to the names of bound variables. The new rules are not in
`InferenceRule::all()` / `EquivalenceRule::all()`, so propositional generation, proving and
benchmarks behave exactly as before. `models::set_theory` holds the ZFC axioms in the order
Halmos's *Naive Set Theory* introduces them and a 49-exercise track; every exercise has a
verified solution in `tests/halmos_track.rs`.

## Use

```toml
[dependencies]
logic-core = { git = "https://github.com/dogaozden/logic-core", tag = "v0.4.0" }
```

```rust
use logic_core::models::Formula;
use logic_core::services::ProofVerifier;
```

## Layout

- `models/` — formulas, proofs, scopes, theorems, statistics, and the rule set
- `services/` — verification, generation, proof search, truth tables, obfuscation

## Tests

```bash
cargo test
```

Generation is seedable via `generate_with_rng` for deterministic tests and
reproducible benchmark sets.
