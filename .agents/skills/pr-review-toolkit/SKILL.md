---
name: pr-review-toolkit
description: Review and fix an Acorn diff or PR using its proof standards and proportionate independent review. Use for review-and-fix or pre-PR quality passes, not read-only reviews.
---

# Review and fix

Use the repository [proof-review standard](../proof-review/SKILL.md). Correctness
comes from the actual types, executable definitions and proofs; no scenario tests.
Apply current `AGENTS.md` for verification, merge authority and record retention.

1. Identify the intended diff, relevant callers and claimed behavior. Preserve
   unrelated changes. Follow changed guarantees to their actual enforcement and
   execution, including assumptions and admission/write paths. Read
   [repository bindings](references/repository-bindings.md) when those domains apply.
2. Use one independent read-only reviewer for the PR. Give it the diff, user intent
   and relevant instructions, without steering it toward expected findings.
   Cover correctness, proof adequacy, documentation and error paths together.
   Add a specialist only for a named question the review cannot resolve; do not
   run a fixed set of agents or repeated full passes.
3. Validate concrete findings, fix authorized defects and verify affected owners.
   Have the reviewer recheck a substantial or uncertain repair; a routine edit
   needs proportionate verification, not another full review. Disclose unresolved
   findings or larger scope choices instead of silently deferring them.
4. Simplify the changed code while fixing it: reuse existing owners, remove dead
   work and needless indirection, preserve invariants and useful rationale. This
   is part of implementation/review, not a separate trio of review jobs.
5. Run the local checks required by `AGENTS.md`. Report what changed, meaningful
   verification and any material limits in the PR. Do not create a charter,
   coverage matrix, ledger, attestation, transcript or verification archive.

Missing proof/checks or unresolved blocking defects leave the PR unready. A clean
review is not a universal correctness claim. Git and the PR are the engineering
record; scratch and successful raw logs are disposable. Maintain this skill
under `.agents/skills/`.
