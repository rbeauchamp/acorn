# Contributing

Questions, research criticism, documentation improvements and code contributions
are welcome. Open an [issue](https://github.com/rbeauchamp/acorn/issues) with the
question or problem and links to the relevant text, equation or source. You do
not need a proposed fix or Lean expertise to report something unclear.

For a substantial implementation or empirical study, discuss the research need
and scope before starting. For a focused code change, explain its intended
semantics, assumptions and implementation owner in the pull request. Use
[SECURITY](SECURITY.md) for private vulnerability reports.

## Working on code and proofs

Read [AGENTS](AGENTS.md), [the learned-only binding](docs/learned-only-binding.md)
and the relevant [prior-art contract](docs/prior-art-review.md). For a bug, identify
all state construction, restoration and update boundaries. Prefer types,
derivation and universal proofs over sampled examples. Scenario tests are not the
correctness policy of this repository. Counterexamples diagnose a missing
contract; close the whole class at its actual implementation owner.

Keep proofs linked to executed definitions. Identify the machine-word or
mathematical domain and hypotheses. Preserve signal provenance, admission at
every write, observer isolation, notices and documented research limitations.
Paper-based mechanisms require verified citations and justified material
adaptations, including semantic compatibility in composition. Technical admission
and promotion to a default are distinct decisions.

Run `./scripts/verify.sh` in the actual checkout. Do not bypass its 300-second
limit or remove required checks. CI must pass for the exact proposed head. Use
one independent review under the shipped proof-review skill; use ux-review for
viewer or normative viewer-spec changes. The skills under `.agents/skills/`
publish the repository's review standards for contributors and coding assistants.

Describe what changed, why, the actual checks and their limits in the PR. Sign
commits. Resolve review conversations and honor required status/signature/PR
protections; never bypass them. Benchmark reruns, new studies, releases and
external publication need their own scope and authorization. Do not upload
local run state, credentials, private records or proprietary material.

## Scientific evidence

Ordinary engineering needs implementation, proofs, useful documentation and a
concise PR, not a scientific dossier. Do not run a study to replace an unresolved
proof obligation. Scientific execution requires explicitly authorized scope.

### Deliverable placement

Shared algorithms and proofs belong in maintained modules. A future study owns
its protocol, original observations, canonical results and necessary source
identity. Preserve original bytes separately from semantic presentations. Never
rewrite an original observation to improve a claim or replay archived experience
into an agent. This source release includes no empirical study data.

### Protocol and evidence

Before observation, specify the semantic question, estimands, accepted/refuted
claims, initialization, stream, held-out population and prior access, comparisons,
exclusions, missing/failed-run treatment, stopping rules, resource budget and
uncertainty method. Distinguish confirmatory from exploratory analysis and report
negative and inconclusive results. For continual learning, account for adaptation,
lifetime memory/latency and the actual meaning of each ablation.

Use immutable protocol revisions and distinct run identities. Record exact source,
configuration and environment with each run. A content hash establishes integrity,
not preregistration, independent timing or scientific truth. Additional independent
timestamps serve only a stated requirement. Disclose access, deviations and
historical timing/authenticity limitations explicitly.

Every empirical citation must identify study, protocol revision, run and
comparison. Canonical calculations must resolve to the retained observations and
executed calculator owner. Preserve negative/inconclusive records. Qualification
requires the separate [promotion standard](docs/prior-art-review.md#default-promotion-and-demotion).
No positive result follows from a formally well-typed record or analysis formula.
