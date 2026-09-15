---
name: ux-review
description: Review Acorn viewer UX against docs/viewer-ux.md. Use for requested viewer UX reviews and whenever viewer UX or its normative spec changes, not for general documentation or code review. Read-only unless fixes are requested.
---

# UX review

Review the viewer whenever its presentation, displayed-data semantics, controls,
lifecycle behavior, or normative specification (`docs/viewer-ux.md`) changes.
Unrelated documentation, code comments, plans, handoffs, and skill edits do not
trigger this workflow. Review their accuracy under the applicable code or
proof-review lens.

A newcomer from Sutton, Javed, and the Oak Lab team should see within ten seconds
what the system is, what it is trying to do, and how it is doing.
Code correctness alone does not establish this.

## Standard and evidence

`docs/viewer-ux.md` is normative for the viewer. Read its relevant clauses and
[references/review-standard.md](references/review-standard.md) for repository
invariants and design references. A violated spec or repository rule is a defect;
a preference where both are silent is explicitly design judgment.

Inspect the actual rendered build and the states/geometries affected by the
change. Read [capture guidance](references/capture-evidence.md) when using browser
evidence and [review prompts](references/review-workflow.md) for the relevant UX
questions. One reviewer can cover them together; there is no fixed nine-agent
review, capture manifest or repeated full pass.

Validate findings against the rendering, DOM and applicable spec. Distinguish a
spec violation from design judgment. If fixes are authorized, make them and
recheck the affected rendering and gates. Report concrete findings, remaining
uncertainty and useful screenshots in the PR; successful capture scratch is
disposable. A read-only request ends with the findings.

The viewer may supervise lifecycle as INV-1 permits, but must not influence
agent decisions. Preserve unknown values and named windows, source traceability,
fault visibility, and the spec's timer inventory. Do not introduce scenario tests,
new studies, or a visual-regression harness to close a UX review.

Maintain this skill under `.agents/skills/`.
