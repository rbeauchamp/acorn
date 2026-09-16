# Guarantee owners and evidence


The workflow below speaks of theorems, typed invariants, refinements, and
audit mutations. In this repository those categories have concrete owners:

| Owning artifact | Where it lives | How to run or probe it |
|---|---|---|
| Universal Lean theorem | `lean/`, axiom-audited in `Axioms.lean` | `./scripts/verify.sh` — source/compiled policy, execution links, native routes and dependent-axiom inventory; provision Mathlib separately |
| Typed invariant / compiler refinement | current proof-bearing Lean state, private construction and typed admission | `./scripts/lean.sh build acorn-core acorn-viewer`; the complete suite checks every discovered module |
| Deterministic audit mutation | `Acorn.Host.AuditPins` and printed pin/checksum pairs | explicit `./scripts/verify.sh diagnostics` runs the derived, annealed and differential arms; a moved digest on a semantics-preserving change is a finding, not a re-pin |
| Gate tamper-sensitivity | actual changed Lean gate owner | use a disposable missing-owner, bypass or stale-dependency mutation where it bears on the changed admission contract; restore before the final pass |
| Constant identity | direct imports of owning constants; `AcornVerif.CurrentConstants` for the stated rational and dimensional interface | the complete Lean compiler and axiom checks; current constants have no cross-language emitter |

Prospective scientific evidence follows
[CONTRIBUTING](../../../../CONTRIBUTING.md#scientific-evidence), including protocol
revisions, run identities, source/configuration provenance, observation retention,
uncertainty and negative or inconclusive results. Supporting mathematical definitions establish contracts over explicit inputs
and hypotheses.
The complete local merge command is `./scripts/verify.sh`. Optional mutation
diagnostics use `./scripts/verify.sh diagnostics`; neither substitutes for proofs
or constitutes a scientific study. Both modes retain the hard 360-second budget.
Record compiler-backed theorem counts with their scope when proofs or gates
change. A count is not a correctness score. Inspect check output; retain failure
diagnostics only while they help resolve an open problem.

Use the [proof-review scoring standard](../../proof-review/references/proof-standard.md)
to translate test-shaped findings into missing guarantees.

For prior-art changes, review the relevant change against the
[canonical admission standard](../../../../docs/prior-art-review.md#admission-standard).
Review the material adaptation rationale and semantic composition alongside
formal owners. The fresh-context refutation must attack those claims, without
adding benchmark replication or whole-agent convergence as admission gates.
