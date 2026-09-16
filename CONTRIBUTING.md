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

[AGENTS](AGENTS.md) is the engineering and review policy: proof-first correctness,
learned-only boundaries, prior-art admission, and delivery requirements. Follow
its [review and delivery](AGENTS.md#review-and-delivery) section for checks,
signed commits and independent review. The shipped skills under .agents/skills
provide the review workflow and proof-specific questions.

For each change, explain the intended behavior, its implementation and proof
owners, and any assumptions in the PR. Run `./scripts/verify.sh` from the checkout
and report its actual result and material limits.

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
