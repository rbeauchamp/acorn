---
name: create-issue
description: Draft or publish an Acorn GitHub issue with mission context, evidence and verifiable completion criteria. Use for issue-writing requests, not implementation or PR creation.
---

# Create an Acorn issue

Produce an issue a contributor can complete from a fresh session. Capture the
reasoning and constraints that affect decisions; scale detail to the work. A
small defect may need only a few paragraphs. For research, cross-module work or
an explicitly comprehensive handoff, read [handoff guidance](references/handoff.md).

## Establish the work

Confirm the target repository from the checkout/remote and the user's request.
Inspect relevant existing issues and PRs to avoid duplicating work; distinguish
an existing issue to update from a related one with different scope. Resolve
only consequential ambiguity with the user. An issue-writing request authorizes
its requested publication, not implementation, a study or additional issues.
Honor draft-only requests.

Explain the concrete mission contribution: continual learning, representation,
prediction, control, planning, or an enabling correctness/resource requirement.
Use current [design](../../../docs/design.md), [frontier](../../../docs/frontier.md)
and [admission register](../../../docs/prior-art-review.md) only where relevant.
Prefer one bounded issue; propose a split or project when independently
completable outcomes or dependencies justify it. Do not create them unasked.

## Ground and bound the issue

Inspect the actual source/proof owners behind decision-bearing claims. Record the
baseline commit and durable source links. Separate implemented facts, observed
behavior, deductions, hypotheses and unknowns. Read theorem hypotheses and
execution linkage; a name or passing check does not establish the intended
property. Verify paper citations against primary sources, with precise sections
or equations where the algorithm depends on them. If evidence is unavailable,
name the gap instead of inventing a diagnosis or citation.

Define the outcome, scope, remaining design decisions, relevant owners and
observable completion criteria. Preserve the user's accepted constraints and
rationale without requiring the prior conversation. Link canonical repository
policy rather than copying it; include the concrete verification obligations
that determine this issue's completion. Follow current [AGENTS](../../../AGENTS.md)
and [scientific evidence guidance](../../../CONTRIBUTING.md#scientific-evidence).
Do not solve the implementation or run a learning campaign to write the issue.

## Publish and finish

Check the draft as a fresh-session handoff: can the next contributor locate the
evidence, tell facts from open questions, choose the permitted next action and
recognize completion? Remove irrelevant headings, repeated policy and speculative
requirements. Review the body for private material before publishing.

Use the available GitHub connector or CLI; prefer `gh-axi` when installed, with
`gh` as a fallback. Send multiline Markdown through a structured body argument
or a UTF-8 body file. Apply only justified, existing metadata. Read back the
published issue and verify its repository, title, full body and requested
metadata. If creation returns ambiguously, look for the created issue before
retrying; if unresolved, retain the draft and report the uncertainty rather
than risk duplicates. Finish with the issue link, or the complete draft when
publication was not requested. Stop before starting the issue's work.
