---
name: proof-review
description: Review Acorn diffs and PRs against proofs, typed invariants, and compiler contracts. Supplies the repository scoring standard; never requests scenario tests.
---

# Proof review

Use this standard for Acorn reviews. When `pr-review-toolkit` loads it as a
scoring standard, apply these criteria inside that workflow; do not launch a
second review or simplification cycle. A referee assigned under the review
protocol uses it as [referee's review](#referees-review) below says.

## Scoring and relevant context

Read [AGENTS](../../../AGENTS.md) for the engineering policy and
[references/proof-standard.md](references/proof-standard.md) for the review
questions and invalid findings. Apply the relevant guarantees in
docs/verification.md and use the prior-art and scientific evidence guidance when
the changed behavior touches those contracts. Credit the actual mechanism;
distinguish proven, observed, assumed, bounded and unresolved claims.

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
material verification limits. For a review that the author runs, no separate
review ledger or evidence record is required, and one independent reviewer
serves a PR; further reviewers or repair passes need a specific unresolved
question. Successful scratch output is disposable.

## Referee's review

A referee whom the maintainers assign under the
[review protocol](../../../CONTRIBUTING.md#review-protocol) applies this
standard report-only and adversarially. For each claim of the pull request,
look for the cheapest way it could be false, or weaker than the pull request
says, while every check passes. Read the Lean statements themselves, with
their binders, hypotheses and the definitions they unfold, not their names or
the description. Read the claims against the issue's contract. Ask the two
questions on [credit to learning](references/proof-standard.md#credit-to-learning)
of every claim that the agent learned something. Read the pull request's list
of computations against
[what counts as a run](../../../CONTRIBUTING.md#what-counts-as-a-run). Do not
repair the work.

File the report as a comment on the pull request, in the form the protocol
gives: the head commit read; what is claimed; what is established, claim by
claim, with the statement read; what must change, each finding with its place,
its reason and the correction it needs; and a verdict of accept, revise or
reject. A report that restates the gate's result is no report. The report is
kept with the pull request.

Maintain this skill under `.agents/skills/`.
