# logic-core

The propositional logic proof engine behind
[PropBench](https://github.com/dogaozden/prop-bench) and
[Logic Proof Trainer](https://github.com/dogaozden/logic-proof-trainer).

Formula representation and parsing, natural-deduction inference and equivalence
rules, conditional and indirect proof, proof verification, truth tables, and
theorem generation by difficulty tier.

No UI and no application code — both products build their own layer on top.

## Use

```toml
[dependencies]
logic-core = { git = "https://github.com/dogaozden/logic-core", tag = "v0.1.0" }
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

Note: `services::tree_gen::builder::tests::test_multiple_generations` is
flaky. It generates proof trees from an unseeded RNG and fails on roughly
40% of runs. This predates the extraction of this crate.
