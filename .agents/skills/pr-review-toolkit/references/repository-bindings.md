# Guarantee owners and evidence


The workflow below speaks of theorems, typed invariants, refinements, and
audit mutations. In this repository those categories have concrete owners:

| Owning artifact | Where it lives | How to run or probe it |
|---|---|---|
| Universal Lean theorem | `lean/`, axiom-audited in `Axioms.lean` | `./scripts/verify-lean.sh` — offline source/compiled policy, execution links, native routes, dependent-axiom inventory; the private profile also checks preserved-record integrity; provision Mathlib separately |
| Typed invariant / compiler refinement | current proof-bearing Lean state, private construction and typed admission | `./scripts/lean.sh build acorn-core acorn-viewer`; the complete suite checks every discovered module |
| Deterministic audit mutation | `Acorn.Host.AuditPins` and printed pin/checksum pairs | explicit `./scripts/verify.sh diagnostics` runs the derived, annealed and differential arms; a moved digest on a semantics-preserving change is a finding, not a re-pin |
| Gate tamper-sensitivity | actual changed Lean gate owner | use a disposable missing-owner, bypass or stale-dependency mutation where it bears on the changed admission contract; restore before the final pass |
| Constant identity | direct imports of owning constants; `AcornVerif.CurrentConstants` for the retained model interface | the complete Lean compiler and axiom checks; current constants have no cross-language emitter |

Prospective scientific evidence follows
[CONTRIBUTING](../../../../CONTRIBUTING.md#scientific-evidence), including protocol
revisions, run identities, source/configuration provenance, observation retention,
uncertainty and negative or inconclusive results. Ordinary verification includes
no historical study archive or reproduction command. Shared schema and pure
analysis definitions establish contracts over inputs, not observed evidence.
The complete local merge command is `./scripts/verify.sh`. Optional mutation
diagnostics use `./scripts/verify.sh diagnostics`; neither substitutes for proofs
or constitutes a scientific study. Both modes retain the hard 300-second budget.
Record compiler-backed theorem counts with their scope when proofs or gates
change. A count is not a correctness score. Inspect check output; retain failure
diagnostics only while they help resolve an open problem.

There are no scenario tests in this repository — not missing ones, forbidden
ones. A gap in guarantee coverage is closed by strengthening an owner from
this table, never by adding a test. Scoring follows the repo-local
`proof-review` skill (`.agents/skills/proof-review/SKILL.md`), whose invalid-findings list rejects anything test-shaped
whatever lens raised it, and whose "rationale yes, changelog no" rule governs
every doc and comment finding.

For prior-art changes, review the relevant change against the
[canonical admission standard](../../../../docs/prior-art-review.md#admission-standard).
Review the material adaptation rationale and semantic composition alongside
formal owners. The fresh-context refutation must attack those claims, without
adding benchmark replication or whole-agent convergence as admission gates.
