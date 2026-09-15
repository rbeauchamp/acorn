# Research frontier and limitations

These are the main open questions in Acorn, with the implementation constraints
and next steps for investigating them.

Start with [the learning loop](design.md#the-learning-loop) for terminology.
The F labels identify research questions, D labels identify authored departures,
and PAR labels identify mechanism contracts.

## F1 · Option-model quality

**Do the learned models predict useful consequences of executing an option?**

Model accuracy under changing policies and representations is an open question.
Extensions must preserve shared units, target alignment and age semantics.

*Refutation attempt.* Challenge whether the executed target denotes the claimed
quantity; then assess a prospective, isolated quality/benefit comparison.

## F2 · Planning benefit

**Do model-based updates improve decisions enough to justify their cost?**

The comparison must account for model error, planning cost and the decisions
affected by the backups.

*Refutation attempt.* Check target/backup compatibility before attributing a
measured effect to planning.

## F3 · Representation and retirement

**Can the agent replace features safely, autonomously and usefully?**

Retirement preserves its conditional safety contract. The open questions are
whether its guard becomes reachable and whether replacement helps the agent.
Only imprint features are retired; input channels and tile features remain
authored. General learned agent state is a further extension.

*Refutation attempt.* Trace every admission/write boundary and characterize
reachability analytically before measuring turnover.

## F4 · Continuing control and exploration

**Which control and exploration mechanisms help over a continuing stream?**

Differential control is selectable with `--criterion average-reward`. Its
qualification status is recorded below. Exploration duration remains authored
([D3](learned-only-binding.md#d3--exploration-duration--step-9)). General GVFs,
the complete OaK feedback loop and learned prediction questions are not supplied
by this implementation.

*Refutation attempt.* Check units, gain/return identities, support and composition
hypotheses, then define the comparison needed to assess continuing performance.

See [design](design.md), [departures](learned-only-binding.md) and
[admission/promotion](prior-art-review.md). Proposals should first identify the
claim and its strongest available mathematical argument. Empirical work needs
the scoped protocol described in [Contributing](../CONTRIBUTING.md#scientific-evidence).

## Research status and limitations

The core requires an explicit research profile. The
[qualification register](prior-art-review.md#current-default-qualification) records
the current decisions: discounted control awaits qualification; differential
control remains **demoted** and ineligible for default use.

| Property | Executed/checked boundary | Remaining limit |
|---|---|---|
| State legality | Indexed value domains and checked construction/restoration | Hypotheses and machine domains belong to each theorem. |
| Learned-only separation | Declared provenance plus source/compiled quarantine | Review checks the declared origin against the producing code. |
| Persistence | Admitted format, dimensions, criterion and identity; refusing writes on invalid restore | Learner state resumes; world and transient process state restart. Filesystem guarantees depend on native IO and the OS. |
| Viewer | One-way telemetry and lifecycle-only stop | Designed for a single local operator on loopback. |
| Resources | Source/IR-linked structural contracts and bounded stored updates | Physical latency and memory costs depend on the workload and platform. |
| Learning quality | Explicit research selection and promotion rules | Prospective qualification remains open. |
| C-AC5 | Derived arm `829aef890c81afaf`, checksum `b1a076b6ac5884f0`; annealed arm `d41d9d77b74b9858`, checksum `4b15707c76a9191a`; differential arm `bb1d5b590fad9933`, checksum `47a82981b9a9ee2d` | The fixed audit arms are compared through these paired values. |

See [verification](verification.md), [performance priorities](performance-engineering.md) and
[prior-art admission/promotion](prior-art-review.md).
