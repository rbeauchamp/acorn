# Research frontier and limitations

These are the main open questions in Acorn, with the implementation constraints
and next steps for investigating them.

Start with [the learning loop](design.md#the-learning-loop) for terminology.
The F labels identify research questions, D labels identify authored departures,
and PAR labels identify mechanism contracts. The
[baseline assessment](baseline-assessment.md) compares the implementation with
the published OaK and Alberta Plan designs and orders the conformance work that
the [roadmap](https://github.com/users/rbeauchamp/projects/10) tracks.

## F1 · Option-model quality

**Do the learned models predict useful consequences of executing an option?**

Each option has an expectation model over a ranked subset of feature slots
([PAR-13](prior-art-review.md#par-13--option-expectation-models)): a reward part,
a transition part that predicts which ranked slots are active when the option
stops, and a shared residual with one deviation per meta action for the value the
ranked slots do not carry. Model accuracy under changing policies and
representations is an open question, as are the share of an outcome's value the
ranked slots carry and the accuracy of the per-action deviations. A refresh keeps the model of every
option whose unit stays ranked, and every free boundary keeps, within each
model, the row of every slot that stays ranked and its weights from the other
retained slots; models restart only
when their subtask's unit leaves the ranking or is replaced. Extensions must
preserve shared units, target alignment and age semantics.

*Refutation attempt.* Challenge whether the executed target denotes the claimed
quantity; then assess a prospective, isolated quality/benefit comparison. The
[baseline assessment](baseline-assessment.md#f-b--the-option-model-is-a-value-estimator-so-planning-cannot-plan)
records why the earlier scalar continuation estimated a value rather than a
transition.

## F2 · Planning benefit

**Do model-based updates improve decisions enough to justify their cost?**

Planning backs up each option's value from its expectation model with the
current value weights, at the current feature vector and at one stored recent one
per decision boundary
([PAR-14](prior-art-review.md#par-14--background-planning)). The comparison must
account for model error, planning cost and the decisions affected by the backups.
Search control beyond a fixed sweep over the stored vectors is separate work.

*Refutation attempt.* Check target/backup compatibility before attributing a
measured effect to planning.

## F3 · Representation and retirement

**Does generate-and-test turnover improve the agent's representation?**

The [PAR-11](prior-art-review.md#par-11--generate-and-test-tester) tester replaces
the least useful eligible imprint units at the declared
[D7](learned-only-binding.md#d7--feature-tester-schedule--step-2) rate, so
turnover is reachable by construction: over any run the number replaced is
exactly ⌊(c₀ + Σₜ nₜ)/period⌋ for eligible counts nₜ. The generator reads the
tile-kind patch and the task words, so generated units can conjoin task and
layout. Only imprint features are replaced; input channels and tile features
remain authored. General learned agent state is a further extension.

Whether turnover at the declared rate improves prediction and control is
UNKNOWN: it depends on the stream and on how quickly useful conjunctions are
found, which no derivation from the tester's own state settles.

*Refutation attempt.* Check that utilities measure contributions the readers
actually use and that replacement preserves every admission boundary before
measuring any benefit. The
[baseline assessment](baseline-assessment.md#f-e--the-retirement-tester-works-against-turnover)
records why the earlier guard worked against turnover.

## F4 · Continuing control and exploration

**Which control and exploration mechanisms help over a continuing stream?**

Differential control is selectable with `--criterion average-reward`. Its
qualification status is recorded below. Exploration duration and rate remain
authored ([D3](learned-only-binding.md#d3--exploration-duration--step-9),
[D6](learned-only-binding.md#d6--exploration-rate--step-9)). General GVFs,
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
| C-AC5 | Declared-rate arm `b1f613d0b887e2ec`, checksum `82e22258e9546064`; annealed arm `44b12a4ace91e72e`, checksum `566c46a5a2f8212e`; differential arm `6eeee57dda0ec1a0`, checksum `32ca6c444488d470` | The fixed audit arms are compared through these paired values. All three pins record the generate-and-test tester and task-reading generator (PAR-11, D7), off-policy option learning (PAR-17) and option expectation models with planning under the current values (PAR-13, PAR-14); the declared-rate and differential pins also record the stable, sign-correct subtask (#8) and declared-rate (D6) dynamics decisions. |

See [verification](verification.md), [performance priorities](performance-engineering.md) and
[prior-art admission/promotion](prior-art-review.md).
