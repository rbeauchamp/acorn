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

Retirement preserves its conditional transaction and singleton-prediction
contracts. `CurrentReplacement` connects exposure obstructions to the actual
agent: a primitive action never selected since cold initialization retains an
initial reader that vetoes every unit. This holds for arbitrary finite ordinary
input paths, including attempt requests and stop, excluding clear/restore. Every
cold action prefix shorter than nine decisions therefore records zero
replacements; longer omitted-action prefixes satisfy the same result. It does
not establish that a primitive action remains omitted forever.

Repeated one-action option invocations have a further obstruction: terminal
weight credit executes, but the model's meta-gradient is cleared before it can
change initial beta. The actual begin/terminal callback proof covers finite
rewards within the prediction envelope and at most 1900 active initiation
features; a default-size patch without food/deer channels has at most 1712.
The complete short-invocation scheduling argument and its admitted-input domain
are stated in PAR-11. It does not assert that the endogenous world always
produces short invocations. Retaining sensitivity across boundaries would require
a derived reset/pruning/support contract before changing the learner.

Structural restoration restarts option models cold, so it cannot by itself
enable immediate retirement even when primary weights and step sizes satisfy
the predicate. First-match selection permanently excludes later units sharing
an earlier unit's hashed slot. The separate lifetime history admits at most
`config.units.count` total events (512 for the default bank), including repeated
replacement of one unit. Strict timestamp order and the saturating UInt64 clock
can refuse earlier; advancing or restoring does not replenish capacity.

Positive complete-reader reachability after sufficient exposure remains
**UNRESOLVED**. Small weights and minimum step sizes do not prove sufficient
evaluation or utility. Improved learning from replacement is **UNKNOWN**:
coupled representation changes alter future experience, and the safety contracts
do not determine learning benefit. Only imprint projections are replaced; input
channels and tile features remain authored.

*Refutation attempt.* The execution-linked obstruction, alias result and local
success condition are specified in
[PAR-11](prior-art-review.md#par-11--bounded-disruption-retirement). A positive
learning argument must account for all receiving storage, rounded adaptation,
reset interference and remaining history/clock capacity. The direct-write
predicate-inhabitation theorem supplies none of those trajectory premises.

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
