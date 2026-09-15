---
name: proof-review
description: Review Acorn diffs and PRs against proofs, typed invariants, and compiler contracts. Supplies the repository scoring standard; never requests scenario tests.
---

# Proof review

Use this standard for Acorn reviews. When `pr-review-toolkit` loads it as a
scoring standard, apply these criteria inside that workflow; do not launch a
second review or simplification cycle.

## Scoring and relevant context

Read [references/proof-standard.md](references/proof-standard.md) for proof
admission, compute-frugality, and invalid findings. Apply `AGENTS.md` and the
relevant guarantees in `docs/verification.md`. Load dossier and prior-art
standards when the reviewed change touches those contracts.

- Close a guarantee at the highest applicable layer: type → derivation →
  closed-domain exhaustion → proof → derived guard → irreducibly empirical
  measurement. Within proof, prefer structural/analytic arguments to static
  `decide`, and reflection last, with the required cost/owner decision.
- No scenario tests. Counterexamples diagnose; permanent closure is universal
  or makes the illegal state or bypass uninhabitable. A few Lean examples or
  hand-listed open-domain values do not establish that closure.
- Credit the actual mechanism. A pinned digest detects dynamics changes; it
  does not establish correctness. Use the proof standard's questions for changed and relied-upon guarantees,
  including inherited owners.
  Distinguish proven, observed, assumed, bounded, and unresolved.
- Keep comments about present guarantees and rationale. Preserve learned-only
  provenance, observer isolation, historical evidence, and admission versus
  default qualification. Do not weaken a guarantee to simplify its prose.

## Standalone review

1. Establish the requested diff, review scope, and whether fixes are authorized.
   Read [references/review-lenses.md](references/review-lenses.md) and run the
   applicable prompts against the actual diff. Inspect only the owners
   and supporting context relevant to their assigned guarantees. Validate each
   finding against its source and report all dispositions; scope belongs to the
   owner, and findings must not be silently deferred.
2. A report-only request ends with findings. With authorized fixes, close each
   accepted finding at the highest layer that reaches it and name that layer.
3. After fixes, read [references/repair-and-verification.md](references/repair-and-verification.md).
   Simplify the repaired surface, preserving refinement types, exhaustive matches,
   private fields, proof/gate owners, and useful rationale. Run the prescribed
   verification for the affected guarantees; do not infer behavior preservation
   from reading the diff or re-pin an unintended dynamics change.

The verification requirements in `AGENTS.md` remain authoritative. For proof, compiler or verification-documentation changes, report the observed
compiler-backed Lean theorem counts with their scope. Missing required
verification leaves the work incomplete; CI is not evidence that local proofs ran.

Report concrete findings with location, reason and needed correction, plus
material verification limits. No separate review ledger or evidence record is
required. Use one independent reviewer for a PR; further reviewers or repair
passes need a specific unresolved question. Successful scratch output is disposable.
Maintain this skill under `.agents/skills/`.
