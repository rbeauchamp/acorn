# Comprehensive issue handoffs

Use these decision prompts for substantive research or implementation issues.
They are not a mandatory heading template. Include what a fresh contributor
needs; omit inapplicable sections. A request for complete context calls for
complete reasoning, not a list of every possible engineering activity.

## Problem, evidence and causal understanding

State the intended outcome, mission relevance, baseline revision and relevant
current behavior. Tie key claims to pinned source links and named definitions.
For a defect, give the expected/actual relation and known causal chain. For an
open research question, identify what has not been established. Keep a suspected
root cause distinct from a demonstrated one, and explain why existing contracts
do or do not answer the question.

Include the smallest reproduction or inspection procedure that establishes the
reported observation or recovers the structural argument. A research uncertainty
may have no runtime reproducer. Do not invent a failing run, turn diagnostic
examples into scenario-test requirements, or assume checkpoint legality implies
reachability through learning. Record empirical evidence's run/configuration and
limits when it is actually available and authorized for publication.

## Semantics, design and work boundaries

Identify relevant state, invariants, semantic domains, assumptions and resource
bounds. For proof-bearing work, connect proposed claims to executed definitions
and their construction, update and restore boundaries. Distinguish machine words
from mathematical values, safety from progress, finite from unbounded guarantees,
and technical admission from demonstrated learning benefit. Progress assumptions
must be substantive and non-circular, not the desired conclusion restated.

Preserve accepted design decisions and their rationale; leave unresolved choices
open with decision criteria. Use phases when findings determine later work:
characterize → choose the smallest justified design → implement and verify.
Allow a justified no-change result for characterization tasks. If evidence points
to materially broader work, specify the decision/follow-up needed; do not label
an unresolved diagnosis or deferred repair as completed implementation.

State inclusions, exclusions, dependencies and authority boundaries. Capture
relevant operational constraints without copying stale branch, visibility or
session instructions. Revalidate mutable facts. Do not turn one issue's incident,
workaround or preferred design into a universal rule.

## Deliverables and completion

Name the implementation and proof owners to inspect, the intended deliverables,
and the evidence that will satisfy each acceptance criterion. Define completion
through the applicable delivery path, including independent review, local
`./scripts/verify.sh`, CI on the exact proposed head, signed commits and protected
merge when implementation is included. Preserve the current AGENTS.md hard
360-second verification deadline and full admission coverage. Issue creation
itself requires publication readback, not running that implementation suite.

For the affected scope, account for necessary refactoring, removal of newly dead
code, ownership/gate updates, persistence compatibility and documentation of
changed semantics. Consider skill or CI updates only when a concrete reusable
gap requires one; do not mandate changes merely to populate a checklist. Point
to the relevant canonical docs and shipped review skill instead of duplicating
whole policies. Keep source comments about current meaning, and the PR/issue
about the decision and verified result.

State what the resulting proofs/checks will not establish. An irreducibly
empirical quantity stays UNKNOWN with an explanation of why deduction cannot
settle it. If a study is within explicitly authorized scope, use the prospective
protocol requirements in CONTRIBUTING.md; otherwise identify it as separate
work. Avoid adding a study, default promotion or new infrastructure as an
implicit acceptance gate.
