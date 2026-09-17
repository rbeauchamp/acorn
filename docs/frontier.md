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
a derived reset/pruning/support contract before changing the learner. The local
`episode_sensitivity_anchor` identity specifies how aligned `h`/`hTemp` reach
the next meta-gradient in the existing binary32 second loop. It supplies no
complete-reader progress window. PAR-11 records the candidate boundary contract
and why neither unexcited no-food observations nor independently prescribed
signed targets realize that window through the coupled callbacks.

A pending free dispatch that changes at least two complete skill assignments
also refuses its ensuing scan (`act_two_refresh_changes`). In the actual
discounted callback, at most one newly initialized model receives option credit;
the other stays cold through completion and vetoes every hashed slot before
retirement. This requires no feature-count or reward-magnitude bound. Its
premises compare actual assignment identities and observe the returned
meta-decision; occurrence along initialized native execution remains unproved.
It does not cover a sole changed assignment selected in that dispatch.

`ZeroKnowledge` now proves the initialized numerical zero-weight/update-lag
sector is preserved by actual zero-target SwiftTD credit, without finite-trace
assumptions. Discounted continuation models stay in that sector through actual
skill begin/step and zero-meta-value close, even with positive reward credit.
Shared-error control now preserves the zero sector through its actual snapshot,
draw, credit and restart order. The close target is derived from that controller's
stored rows. Actual Demon-0 credit preserves zero ranking on zero-reward callbacks;
refreshing already-neutral skills then preserves their complete storage.
Both discounted model learners preserve zero knowledge under zero reward and
zero terminal meta value. Their fresh targets make actual scalar planning an
identity on the controller. Deferred reward accumulation stays zero at every
stored gap age, and neutral option termination consumes the produced old meta
snapshot under an explicit false previous-potential premise.
`ZeroNeutralSkill` connects neutral construction, actual begin/first action,
continuing-token credit and old-meta termination across the policy and both
model learners. Begin and continuing steps return false previous potential;
the continuing snapshot is derived from its actual decision producer.
`ZeroSkillState` lifts those endpoints through actual table installation, meta
dispatch, continuing phase updates and retained/discarded-owner close. It covers
all stored skills and the active option's previous coordinate, while other
learners remain outside this invariant.
`ZeroRankedState` joins that skill sector with both controllers, Demon-0 and
the deferred meta reward. `zero_ranked_initial` establishes the join from the
actual public ranked discounted constructor for every feature configuration,
dimension and planning selection. The other ten demons remain unrestricted.
`zero_ranked_prepare` preserves the join through actual selection preparation
for arbitrary features and signed-zero reward. `zero_ranked_draw_credit` preserves
it through consecutive actual meta draw/credit, using that snapshot and owed gap.
`zero_ranked_refresh`, `zero_ranked_plan` and `zero_ranked_dispatch` join neutral
refresh, concrete configured planning and actual produced meta dispatch.
`zero_ranked_boundary` composes the successful ordinary boundary with no pending
close. `zero_ranked_selection` now composes preparation and every successful
selection branch: served exploration retains priority, continuing credit consumes
the actual token, and discounted ending uses the old pre-close meta snapshot.
`zero_ranked_finish` joins actual primitive and Demon-0 credit;
`zero_ranked_step` composes successful selection and completion.
`zero_ranked_aligned_step` uses the actual wrapper's existing success/alignment
contract. `zero_ranked_retire` preserves the join through both refusal and actual
receiver-bound replacement. `zero_ranked_act` composes clock advancement, the
current-bank encoding, local step and retirement for one zero-reward action.
`zero_ranked_initial_survival` now covers every successful first-survival attempt
prefix through the goal-producing action, using the actual cold/world constructors,
sensing, callback choice, world transition and accounting. The reward is derived
from the bounded physical clock, not supplied as a zero stream. This conditional
result does not prove the existence of a nonempty successful prefix or a
subsequent positive callback.
The next callback, if admitted, consumes the terminal reward under the next goal;
achievement advances goals rather than repeating the successful attempt.
The first-positive goal-action owner and later continuation bootstrap remain
unresolved. A final campaign boundary performs no additional learning callback.
`CurrentRunner.survival_plan_exists` derives actual admission for requests with
at least 200 steps and two goals; the actual initial and achievement cursors
select survival then wood collection. Standard configuration and body/spawn
coordinate admissions are checked in `CurrentWorld`. Its `standard_octave_scales`
proves finite positive scales through all four actual multiplications, and
`coordinate_quotient_bound` bounds the executed signed conversion/division for
coordinate magnitude at most `2^32` and finite scale at least four. These bounds
still need composition through floor, signed cast and checked lattice neighbors.
`standard_terrain_of_samples` composes the actual octave folds but assumes sample
success. Unconditional terrain success and world traversal composition still
block a proved nonempty completion prefix; configuration admission alone does
not establish successful world construction.

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

The Boolean callback family in PAR-11 separates input admission from joint
progress: its actual signals and 1656-slot encoding bound are specified through
the existing encoder, and finite lists follow `Agent.runPrefix`. Neutral stopping
and terminal-error order contracts retain their finite-arithmetic hypotheses.
The actual begin/first-action policy composition preserves every stored weight,
saves the drawn action's pre-update prediction and retains a zero accumulator.
These facts do not supply the missing initialized complete-reader eligibility window.
Longer invocations remain open; the one-action obstruction does not settle them.

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
