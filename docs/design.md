# Design and scope

Acorn studies how an agent can keep learning predictions, representations and
temporally extended behavior from a single stream of experience. This page
introduces the running system; the [prior-art review](prior-art-review.md) gives
the detailed assumptions and adaptations of each mechanism.

## The learning loop

OaK's architecture is introduced in Richard Sutton's
[RLC 2025 talk](https://oaklab.ai/posts/the-oak-architecture). The
[Amii overview](https://www.amii.ca/videos/oak-architecture-rich-sutton-rlc2025)
describes the FC-STOMP progression: feature construction, subtasks, options,
models and planning. Acorn provides an experimental implementation of selected
parts of that progression, with the limitations below.

The host environment supplies an observation and task reward. The agent turns
the observation into features, updates its predictions and action values, and
chooses an action. That action changes the world and supplies the next experience.
Learning continues across task attempts without replaying past observations.

In the `ranked` configuration, these mechanisms work together:

1. **Features** encode properties of the observation for the learners. Acorn
   combines authored input channels with a bank of generated projections.
2. **Predictions** estimate future signals such as task reward. A **general value
   function (GVF)** specifies a signal to predict, a policy and a horizon; Acorn
   uses a fixed collection of on-policy questions.
3. **Subtasks** attach goals to candidate behaviors. Ranked learned feature
   weights supply a proxy for choosing them; this proxy is not established as
   useful subtask discovery.
4. **Options** are policies that can act over several steps. A higher-level
   controller chooses between primitive control and an option, and can interrupt
   an option using learned value estimates.
5. **Models and planning** estimate option outcomes and use those estimates to
   update the higher-level action values without replaying stored experience.

This is an orientation to the components, not a claim that every component
runs in this numbered order on every step. Exact update order belongs to
[the agent driver](../lean/Acorn/Handcrafted/Agent.lean). The complete OaK
feedback loop, general learned state and learned prediction questions remain
outside this implementation; see [the frontier](frontier.md).

### The demonstration world

The world supplies a local 11 × 11 sensory patch, energy, inventory and a task
description. Its nine actions are four directions, wait, harvest, craft axe,
craft boat and eat. The authored curriculum combines survival, collection,
navigation and crafting goals. Task reward is 1 on achievement and 0 otherwise.
The task description does not provide an action-effect model to the learner.
See [observations](../lean/Acorn/Host/Observation.lean),
[actions](../lean/Acorn/Host/Task.lean), and
[the curriculum](../lean/Acorn/Host/Curriculum.lean).

## Implementation scope

The [Alberta Plan](https://arxiv.org/abs/2208.11173v3), by Sutton, Bowling and
Pilarski (2023), supplies the roadmap, not a claim that Acorn completes it.
The focus column paraphrases its twelve steps; the status column describes Acorn.

| Step | Focus | Acorn's implementation scope |
|---|---|---|
| 1 | Fixed-feature learning | Learning machinery with per-weight step-size adaptation. |
| 2 | Representation search | Generated projection features and conditional retirement; authored input channels remain. |
| 3 | Predictive questions | On-policy specialization with fixed questions. |
| 4 | Choosing actions | Declared Sarsa substitution for the plan's actor-critic direction. |
| 5 | Long-run prediction | General average-reward GVFs are absent. |
| 6 | Continuing decisions | Differential-control research integration. |
| 7 | Planning with differential values | Approximate option planning. |
| 8 | Integrated model-based prototype | Models and planning components are present. |
| 9 | Exploration and search choices | Derived exploration rate; duration remains prescribed. |
| 10 | Abstraction through STOMP | Ranked subtasks, options, models and planning. |
| 11 | Complete OaK | Absent; the full utility-feedback loop is not implemented. |
| 12 | Assisting other intelligences | Out of scope. |

An **imprint** here is one of Acorn's generated projection features. Retiring
one replaces it and clears its dependent learned state, subject to the checked
retirement conditions; it does not retire the authored input channels or tile
features. See [PAR-4](prior-art-review.md#par-4--generate-and-test) and
[PAR-11](prior-art-review.md#par-11--bounded-disruption-retirement) for the exact
construction and its relation to prior art.

Here, **implemented** means the mechanism has an executable owner.
**Admitted** means it meets the stated technical integration contract.
**Qualified for default use** would mean the complete configuration has a
supported benefit under declared conditions and an explicit promotion decision.
No current agent configuration has that qualification. Proofs of individual
properties do not establish that the combined agent learns effectively.

The register labels are navigation aids: **PAR** identifies a prior-art or local
mechanism entry, **D** an authored departure from the learned-only discipline,
and **F** an unresolved research question.

## Agent configurations

The [launcher](../scripts/start.sh) supplies the walkthrough settings. You do
not need to select these flags to use it; this section is for investigating the
configuration or running the core directly.

A **research profile** is a named combination of agent mechanisms, selected with
`--research-profile`. It does not select a dataset, trained model or saved run.
An **option** is a policy that can choose actions over several steps; a
**subtask** gives such a policy a goal. **Credit assignment** determines which
predictions or action values receive an update from experience.

The `acorn-core demo` command accepts these five profiles:

| Profile | Configuration | Checkpoints |
|---|---|---|
| `ranked` | Hierarchical control with subtasks chosen from ranked learned features, primitive-action value credit each learning step, and exploration rates derived separately for each learner. | Supported |
| `primitive` | Chooses primitive actions without the option hierarchy. | Unsupported |
| `boundary-credit` | Uses the ranked hierarchy but accumulates primitive-action credit across option spans and applies it at the primitive controller's next own decision. | Unsupported |
| `annealed` | Uses the ranked hierarchy with a prescribed exploration-rate schedule. | Unsupported |
| `spatial` | Uses the hierarchy with hand-authored spatial subtasks instead of learned subtask selection. | Unsupported |

The four alternatives are comparison configurations. Their presence does not
establish that a mechanism helps or hurts learning. The examples use `ranked` to
expose the implemented hierarchy; this is an example selection, not a claim that
it is the best-performing agent. Omitting the profile is an error.
The credit-policy comparison concerns primitive-action values; it does not
defer all prediction updates or make higher-level control update every step.

### Learning objective

The core's `--criterion` flag is independent of the profile:

- `discounted` weights future rewards by a discount factor. This is the default
  criterion when the flag is omitted.
- `average-reward` uses differential control: updates account for reward relative
  to a learned average reward per step. It is an experimental alternative with
  unresolved qualification; see [research limitations](frontier.md).

For example, to select both explicitly in a bounded terminal run:

```sh
lean/.lake/build/bin/acorn-core demo --research-profile ranked --criterion discounted --side 64 --steps 250 --attempts 1 --goals 1 --cycles 1
```

Checkpoint files carry their learner criterion and must pass compatibility checks
before restore. Changing the criterion does not convert an existing checkpoint.

### Viewer support

The viewer's built-in launch accepts only `--research-profile ranked` and uses
the discounted criterion. It does not accept the core's `--criterion` flag or the
other four profiles. Use the terminal command above to explore core configuration
choices. The viewer's advanced `--cmd` option runs an operator-supplied command;
it has different checkpoint ownership and disables the ordinary Clear operation.

The authoritative definitions are [profile selection](../lean/Acorn/Host/Runner.lean),
[mechanism mapping](../lean/Acorn/Host/TemporalProfile.lean),
[core arguments](../lean/Acorn/Host/Cli.lean), and
[viewer launch](../lean/Acorn/Host/Viewer/Options.lean).

### Run controls

An **attempt** gives the current task a step budget. A **cycle** visits the
requested goals of the curriculum. Learner state carries across attempts;
these boundaries do not restart its learned weights.

| Core flag | Meaning |
|---|---|
| `--seed` | Seed for the generated world; default 42. |
| `--side` | Side length of the square world. |
| `--steps` | Maximum environment steps per attempt. |
| `--attempts` | Maximum attempts per goal. |
| `--goals` | Number of curriculum entries to visit per cycle; the standard curriculum has 13 entries. |
| `--cycles` | Number of curriculum cycles; `0` continues until stopped. |
| `--checkpoint PATH` | Load/save compatible learner state; supported for `ranked`. Omission keeps the terminal run in memory. |
| `--csv PATH` | Stream attempt outcomes to a new CSV file; cannot be combined with `--checkpoint`. |

These are core flags, not viewer flags. See
[the CLI definition](../lean/Acorn/Host/Cli.lean) for the full accepted domain.

After building with the launcher, a short terminal example is:

```sh
lean/.lake/build/bin/acorn-core demo --research-profile ranked --side 64 --steps 250 --attempts 1 --goals 1 --cycles 1
```

This runs one attempt at the first goal, which asks the agent to survive for
200 steps. The 250-step cap permits that goal to finish. The terminal reports
achievement or timeout, followed by a campaign summary and diagnostic checksum.
Timeout is a task outcome, not an execution error. This short demonstration is
not a learning evaluation.

## Reading the viewer

The viewer is an observation tool for the active run:

- **World and goals:** what the agent has observed and which assigned goals it
  has achieved within the attempt budgets. The map is not information supplied
  back to the learner.
- **Predictions:** estimates for the fixed prediction questions. Predictive
  agreement compares predictions with settled finite returns; it is not a
  percentage of all knowledge or evidence of general intelligence.
- **Behavior and options:** action values, option selections, boundaries and
  learned model estimates. An estimated value is not an observed outcome.
- **Learning and resources:** step sizes, feature activity, planning updates and
  execution diagnostics. Activity alone does not establish useful learning.

An empty or pending measure has insufficient data; it is not a zero score.
Goal outcomes describe this run, not improvement over a comparison agent.
The [viewer specification](viewer-ux.md) is the detailed contributor reference
for fields, rendering, process lifecycle and persistence.

## Mechanism owners

- [PAR-1](prior-art-review.md#par-1--swifttd): SwiftTD, [Acorn.SwiftTd](../lean/Acorn/SwiftTd.lean).
- [PAR-2](prior-art-review.md#par-2--swift-sarsa): Swift-Sarsa, [Acorn.Sarsa](../lean/Acorn/Sarsa.lean).
- [PAR-3](prior-art-review.md#par-3--horde): Horde, [Acorn.Demon](../lean/Acorn/Demon.lean).
- [PAR-4](prior-art-review.md#par-4--generate-and-test): Generate and test, [Acorn.Features](../lean/Acorn/Features.lean).
- [PAR-5](prior-art-review.md#par-5--reward-respecting-subtasks): Reward-respecting subtasks, [Acorn.Options](../lean/Acorn/Options.lean).
- [PAR-6](prior-art-review.md#par-6--potential-based-shaping): Potential-based shaping, [Acorn.Options](../lean/Acorn/Options.lean).
- [PAR-7](prior-art-review.md#par-7--options-and-interruption): Options and interruption, [Acorn.Temporal](../lean/Acorn/Temporal.lean).
- [PAR-8](prior-art-review.md#par-8--temporally-extended-exploration): Temporally extended exploration, [Acorn.Exploration](../lean/Acorn/Exploration.lean).
- [PAR-9](prior-art-review.md#par-9--intra-option-value-learning): Intra-option value learning, [Acorn.Handcrafted.TemporalControl](../lean/Acorn/Handcrafted/TemporalControl.lean).
- [PAR-10](prior-art-review.md#par-10--derived-exploration-rate): Derived exploration rate, [Acorn.Exploration](../lean/Acorn/Exploration.lean).
- [PAR-11](prior-art-review.md#par-11--bounded-disruption-retirement): Bounded-disruption retirement, [Acorn.FeatureLifecycle](../lean/Acorn/FeatureLifecycle.lean).
- [PAR-12](prior-art-review.md#par-12--ranked-learned-subtasks): Ranked learned subtasks, [Acorn.FeatureRanking](../lean/Acorn/FeatureRanking.lean).
- [PAR-13](prior-art-review.md#par-13--option-models): Option models, [Acorn.Models](../lean/Acorn/Models.lean).
- [PAR-14](prior-art-review.md#par-14--background-planning): Background planning, [Acorn.Planning](../lean/Acorn/Planning.lean).
- [PAR-15](prior-art-review.md#par-15--differential-control): Differential control, [Acorn.Average](../lean/Acorn/Average.lean).

## Boundaries

Types constrain stored words and receiver-bound state. Restored and functionally
updated values must satisfy the same admission as initial construction. Learned
code cannot import host/handcrafted owners except at explicit composition roots.
A provenance witness declares an origin; review must assess whether it is honest.
The viewer receives telemetry and requests lifecycle stop only.

No configuration is recommended as a qualified default; callers must select a
research profile. Differential control remains available only as a research
alternative and is not approved for default use. Prior-art identities retain their hypotheses;
changing policies, projected values and approximate models do not inherit
unqualified convergence or optimality results. See the detailed source comments,
[learned-only binding](learned-only-binding.md) and [verification](verification.md).
