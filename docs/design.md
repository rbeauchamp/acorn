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
models and planning. Acorn implements the components described below.

A world supplies an observation and a reward. The agent turns the observation
into features, updates its predictions and action values, and chooses an action.
That action changes the world and supplies the next experience. Learning continues
across task attempts without replaying past observations.

In the `ranked` configuration, these mechanisms work together:

1. **Features** encode properties of the observation for the learners. Acorn
   combines authored input channels with a bank of generated projections.
2. **Predictions** estimate future signals such as task reward. A **general value
   function (GVF)** specifies a signal to predict, a policy and a horizon; Acorn
   uses a fixed collection of questions about the policy it follows. Each option
   also asks the same questions about its own policy and learns them off-policy,
   from the steps on which the agent chose as that option would; nothing reads
   those answers yet.
3. **Subtasks** attach goals to candidate behaviors. Ranked learned feature
   weights supply the ranking used to choose them.
4. **Options** are policies that can act over several steps. A higher-level
   controller chooses between primitive control and an option, and can interrupt
   an option using learned value estimates. An exploratory run that an option's
   own draw begins also interrupts it. An option that is not executing
   still learns its policy from each action the agent takes, and its model from
   the steps on which the agent chose as that option would.
5. **Models and planning.** Each option's model predicts the reward the option
   collects and which of a small ranked set of features will be active when it
   stops. Planning applies the current higher-level action values to those
   predicted features and moves the option's value toward the result, at the
   current feature vector and at recently seen ones, without replaying stored
   experience.

Exact update order belongs to
[the agent driver](../lean/Acorn/Handcrafted/Agent.lean). The complete OaK
feedback loop, general learned state and learned prediction questions remain
outside this implementation; see [the frontier](frontier.md).

### The interface between the agent and a world

The agent is written against an **interface**, not against one world. An interface
is what a world fixes ([`Interface`](../lean/Acorn/Interface.lean)): the shape of the
symbol array the feature generator samples; which prediction signals the world
supplies and at which horizons; how many primitive actions it accepts; and how many
words one observation carries at most. Everything the agent stores is sized by these.
The interface also declares the first channel of the agent's prediction feedback
words.

Each step the world delivers one **percept**: a **frame** and the reward of the
preceding transition. A frame has three parts, one for each kind of learner input:

- **words**, opaque pairs of a channel and a 64-bit value, which the coder hashes
  into features;
- **symbols**, an array of 64-bit codes that the generated projection features
  sample. Every interface declares its shape and every frame fills it. The
  interface design's requirement R1, that a world may supply no symbol array, is
  deferred until an instance needs it and its feature-construction semantics is
  decided; [issue #70](https://github.com/rbeauchamp/acorn/issues/70) tracks the
  interface work. A world with only words can lay those words' codes over symbol
  positions, as the grid world does with its task context;
- **signals**, one number per prediction question the world declares.

A frame also carries the world's declared subtask potentials, which only the
`spatial` comparison reads, and whether the preceding transition achieved the
installed goal, which ends an executing option. Nothing else reaches a learner.
The agent answers with one action, a number below the interface's action count
([`Agent.act`](../lean/Acorn/Handcrafted/Agent.lean)).

The modules that compose the agent import no world: the boundary audit refuses a
world-independent agent module that imports a host module. In every world one
frame activates at most a number of features fixed by the interface and the
feature configuration (`Agent.frame_length`). The timing of a step, the split of
acting from learning, and an exact saved image are not part of the interface yet;
the grid world waits for the agent.

The agent adds its own prediction feedback words, one per prediction question, on
consecutive channels from the one the interface declares. A frame cannot carry a
word on one of those channels: the frame type holds a proof that none of its words
does, so each world's adapter proves it where it builds a frame. No word of a world
then shares a channel with a feedback word (`Agent.words_disjoint`). This separates
channels, not features: two words on different channels can still hash to one
feature slot, as any two hashed words can.

### The demonstration world

The grid world is one instance of the interface
([`Grid.interface`](../lean/Acorn/Handcrafted/GridWorld.lean)): a symbol array of
131 positions, ten signals after the agent's own reward question, nine actions, at
most 381 words and feedback channels from `0x50`. Its adapter builds each percept
from the host's observation and the preceding result. `Agent.grid_inputs` in
[the host binding](../lean/Acorn/Host/AgentInterface.lean) states, for every
agent state, observation and reward word, that the coder's words and symbols, the
prediction signals and the declared potentials the agent receives are exactly the
values of the host's channel, signal and potential definitions, and
`Agent.callbacks_act` that the host's step is the interface agent's step on that
percept. `Grid.sensorWords_clear` discharges the feedback-channel condition for
every grid frame.

[The correspondence proofs](../lean/AcornVerif/GridCorrespondence.lean) compare the
grid instance with the agent as it was composed directly over the host observation.
They keep that composition as a frozen reference that no executing module imports:
the definitions of commit `d3bc6e0` for construction, the encoding frame, the local
transition, the full decision, the host's step and restoration. `act_eq` and
`callback_eq` state that, for every agent state, observation, reward word and
achievement flag, the host's step returns the same action, decision and next state
as the reference; `initial_eq` and `restore_eq` state the same for construction and
restoration. The reference does not freeze the storage beneath the composition. The
core types take the action count as a parameter that the grid sets to nine, where
they held the constant nine before, and the reference calls the executed selection,
option, model and planning definitions.

The world supplies a local 11 × 11 sensory patch, energy, inventory and a task
description. Its nine actions are four directions, wait, harvest, craft axe,
craft boat and eat. The authored curriculum combines survival, collection,
navigation and crafting goals. Task reward is 1 on achievement and 0 otherwise.
The task description does not provide an action-effect model to the learner.
See [observations](../lean/Acorn/Host/Observation.lean),
[actions](../lean/Acorn/Host/Task.lean), and
[the curriculum](../lean/Acorn/Host/Curriculum.lean).

### What the world guarantees

A world is one output of the generator: the seed fixes the terrain, the two
reach targets and every pseudo-random stream. The properties below are proved
of the executed definitions, for every seed, side, world and action, under the
hypotheses each row names. None of them shows that a goal can be achieved.

| Property | What is proved | Theorems |
|---|---|---|
| Where the reach targets are | Goals 3 and 7 are the reach goals. Each target lies in a fixed square window around the center of the box: within the near radius (12 to 40 tiles) for goal 3 and the far radius (24 to 120 tiles) for goal 7. The generator places them by a hash of the seed and never reads the terrain. | `reach_targets` |
| The goal box is inside the world | A reach goal is met within three tiles of its target on both axes. For a side of at least 54, every such position is inside the box the body moves in; the standard configuration admits sides from 64. | `goal_box_in_world`, `standard_goal_boxes` |
| One target coordinate over seeds | Each value of a window is one target coordinate on ⌊2⁶⁴ / m⌋ or one more of the 2⁶⁴ seeds, where m is the window's width. This counts seeds: it is a distribution only for a seed drawn uniformly, and it says nothing about two coordinates jointly. | `coordinate_seed_count`, `hash2_injective` |
| Reaching reads position only | A reach goal is satisfied exactly when the body is in the goal box, whatever the inventory and the time. | `reach_satisfied_iff`, `reach_goal_iff` |
| Survive goals do not depend on the policy | From a goal's installation, every action sequence whose steps the world accepts satisfies a survive goal exactly when its length has reached the required duration. For every agent, each tick of an attempt that acts reports completion exactly when the attempt's step count has reached that duration. An attempt acts only below its cap, so one whose cap is below the duration never reports completion. That an attempt with a sufficient cap ends achieved at exactly that step is argued from these per-step statements and the attempt's stopping rule; no theorem composes them over the attempt loop. Assumes that the 64-bit clock does not wrap. | `survive_actions`, `survive_tick` |
| Tools and gold are never lost | No world step removes an owned axe or boat or lowers gold. A craft goal or a gold goal achieved once is therefore reported achieved by the first world step of every later visit, whatever was done in between. Wood, stone and food can be spent, so the other collect goals have no such guarantee. | `step_retains`, `absorbing_revisit` |
| Energy | Of any N steps, at most (4N + 2000) / 24 are exhausted: steps on which the body cannot pay for its action and rests. Of any N successive moves at most (2N + 21) / 22 are, so at least 2727 of 3000 moves are paid for. That a move is paid for does not show that the body changed position. | `trace_exhausted`, `moves_exhausted`, `moves_paid_at_cap` |
| Passability is static | Whether the body may enter a tile depends on the tile's generated terrain and on the boat, and on nothing else: not harvesting, regrowth or time. A mountain tile is never enterable, and a water tile exactly when the body owns a boat. No step moves the body onto a mountain, or onto water without a boat. | `enterable_static`, `mountain_closed`, `water_needs_boat`, `step_terrain` |
| The spawn | The spawn search follows a spiral whose schedule contains every tile of the box, and one application of its rule reports an early exit only at a walkable tile with two trees within four tiles. Either the spawn is a walkable tile whose trees plus stone within four tiles are at least two; or no tile of the box is walkable with two trees within four tiles, and the spawn is a walkable tile whose trees-plus-stone score no scored tile of the box exceeds, or the center of the box when no tile is walkable. The first case holds whenever some tile of the box is walkable with two trees within four tiles; it bounds trees plus stone, so two trees near the spawn are not guaranteed. A scored tile is a walkable one whose two counts were not refused. Holds whenever the search returns a spawn. | `selectSpawn_post`, `spawn_of_rich`, `spawn_walkable`, `spiral_covers`, `considerSpawn_contract`, `countKindNear_eq` |

Not proved: that the spawn search returns a spawn rather than a refusal; that
a goal box can be entered or reached; that the walkable terrain is connected;
and any bound on the distance from the spawn to a target. The owners are the
[step proofs](../lean/AcornVerif/CurrentStep.lean),
[goal proofs](../lean/AcornVerif/CurrentGoals.lean),
[curriculum proofs](../lean/AcornVerif/CurrentCurriculum.lean) and
[spawn proofs](../lean/AcornVerif/CurrentSpawn.lean).

## Implementation scope

The [Alberta Plan](https://arxiv.org/abs/2208.11173v3), by Sutton, Bowling and
Pilarski (2023), supplies the roadmap.
The focus column paraphrases its twelve steps; the status column describes Acorn.

| Step | Focus | Acorn's implementation scope |
|---|---|---|
| 1 | Fixed-feature learning | Learning machinery with per-weight step-size adaptation. |
| 2 | Representation search | Generated projection features over the kind patch and task words, replaced by a published generate-and-test tester at a declared rate; authored input channels remain. |
| 3 | Predictive questions | Fixed questions, on-policy about the agent's behaviour and off-policy about each option's policy. |
| 4 | Choosing actions | Declared Sarsa substitution for the plan's actor-critic direction. |
| 5 | Long-run prediction | General average-reward GVFs are absent. |
| 6 | Continuing decisions | Differential-control research integration. |
| 7 | Planning with differential values | Approximate option planning. |
| 8 | Integrated model-based prototype | Option expectation models over a ranked feature subset, planned with the current values. |
| 9 | Exploration and search choices | Declared εz-greedy rate and duration; planning sweeps a bounded store of recent feature vectors. |
| 10 | Abstraction through STOMP | Ranked subtasks, options that learn off-policy on every step, option expectation models and planning. |
| 11 | Complete OaK | Absent; the full utility-feedback loop is not implemented. |
| 12 | Assisting other intelligences | Out of scope. |

An **imprint** here is one of Acorn's generated projection features. The tester
replaces the least useful eligible imprints at a declared rate; a replacement
draws a new projection, zeroes its outgoing weight in every reader and clears its
dependent learned state. It does not replace the authored input channels or tile
features. See [PAR-4](prior-art-review.md#par-4--generate-and-test) and
[PAR-11](prior-art-review.md#par-11--generate-and-test-tester) for the exact
construction and its relation to prior art.

Here, **implemented** means the mechanism has an executable owner.
**Admitted** means it meets the stated technical integration contract.
**Qualified for default use** would mean the complete configuration has a
supported benefit under declared conditions and an explicit promotion decision.
Current decisions are recorded in the
[qualification register](prior-art-review.md#current-default-qualification).

The register labels are navigation aids: **PAR** identifies a prior-art or local
mechanism entry, **D** an authored departure from the learned-only discipline,
and **F** an unresolved research question.

## Agent configurations

The [launcher](../scripts/start.sh) supplies the walkthrough settings. You do
not need to select these flags to use it; this section is for investigating the
configuration or running the core directly.

A **research profile** is a named combination of agent mechanisms, selected with
`--research-profile`.
An **option** is a policy that can choose actions over several steps; a
**subtask** gives such a policy a goal. **Credit assignment** determines which
predictions or action values receive an update from experience.

The `acorn-core demo` command accepts these five profiles:

| Profile | Configuration | Checkpoints |
|---|---|---|
| `ranked` | Hierarchical control with subtasks chosen from ranked learned features, primitive-action value credit each learning step, and the declared εz-greedy exploration rate for every learner. | Supported |
| `primitive` | Chooses primitive actions without the option hierarchy. | Unsupported |
| `boundary-credit` | Uses the ranked hierarchy but accumulates primitive-action credit across option spans and applies it at the primitive controller's next own decision. | Unsupported |
| `annealed` | Uses the ranked hierarchy with a prescribed exploration-rate schedule. | Unsupported |
| `spatial` | Uses the hierarchy with hand-authored spatial subtasks instead of learned subtask selection. | Unsupported |

The four alternatives vary particular mechanisms for comparison. The examples
use `ranked` to expose the hierarchy. The core requires an explicit profile.
The credit-policy comparison concerns primitive-action values; it does not
defer all prediction updates or make higher-level control update every step.

### Learning objective

The core's `--criterion` flag is independent of the profile:

- `discounted` weights future rewards by a discount factor. This is the default
  criterion when the flag is omitted.
- `average-reward` uses differential control: updates account for reward relative
  to a learned average reward per step. See [continuing control](frontier.md#f4--continuing-control-and-exploration)
  for the research questions around this criterion.

For example, to select both explicitly in a bounded terminal run:

```sh
lean/.lake/build/bin/acorn-core demo --research-profile ranked --criterion discounted --side 64 --steps 250 --attempts 1 --goals 1 --cycles 1
```

Checkpoint files carry their learner criterion and must pass compatibility checks
before restore. Changing the criterion does not convert an existing checkpoint.

### Planning selection

The core accepts `--planning expectation` (the default) or `--planning none`
independently of the research profile and criterion. `expectation` backs up every
option's value from its expectation model, at the current feature vector and at
one stored recent feature vector per decision boundary. Both streaming and ANSI
runs carry this selection into the full agent. `none` suppresses model-based
meta-controller planning updates while retaining model learning, ordinary
control learning, the hierarchy and the selected exploration rules. Profiles
without the hierarchy do not perform these planning updates under either choice.

Startup diagnostics, the streaming campaign summary and the persistent ANSI
header line report the effective `planning=none` or `planning=expectation` selection.
CSV output includes the same constructor-derived value in a comment after the
column header. The selection belongs to the current run; it does not change
checkpoint admission or convert stored learner state. Comparisons should
specify fresh initialization or their actual checkpoint history explicitly.

This enables a planning comparison; it does not establish a benefit. Future
states and random-draw consumption can diverge after changed planning values.
Equal attempt caps do not imply equal executed steps or compute cost. Scientific
execution still requires the separately authorized prospective protocol in
[Contributing](../CONTRIBUTING.md#scientific-evidence).

### Viewer support

The viewer's built-in launch accepts only `--research-profile ranked` and uses
the discounted criterion with expectation planning. It does not accept the core's
`--criterion` or `--planning` flags or the other four profiles. Use the terminal
command above to explore core configuration choices. The viewer's advanced
`--cmd` option runs an operator-supplied command; it has different checkpoint
ownership and disables the ordinary Clear operation.

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
| `--planning` | `expectation` (default) or `none`; selects model-based planning updates. |
| `--side` | Side length of the square world. |
| `--steps` | Maximum environment steps per attempt. |
| `--attempts` | Maximum attempts per goal. |
| `--goals` | Number of curriculum entries to visit per cycle; the standard curriculum has 13 entries. |
| `--cycles` | Number of curriculum cycles; `0` continues until stopped. |
| `--checkpoint PATH` | Load/save compatible learner state; supported for `ranked`. Omission keeps the terminal run in memory. |
| `--csv PATH` | Stream attempt outcomes to a new [outcome CSV](#outcome-csv) file; cannot be combined with `--checkpoint`. |
| `--baseline` | After the campaign, run the random-policy comparator over the same campaign and print both achieved counts; cannot be combined with `--control-stdin` or with `--cycles 0`: command admission refuses either before the agent runs. |

These are core flags, not viewer flags. See
[the CLI definition](../lean/Acorn/Host/Cli.lean) for the full accepted domain.

After building with the launcher, a short terminal example is:

```sh
lean/.lake/build/bin/acorn-core demo --research-profile ranked --side 64 --steps 250 --attempts 1 --goals 1 --cycles 1
```

This runs one attempt at the first goal, which asks the agent to survive for
200 steps. The 250-step cap permits that goal to finish. The terminal reports
achievement or timeout, followed by a campaign summary and diagnostic checksum.
Timeout means the attempt used its step budget before achieving the goal.

### Outcome CSV

`--csv PATH` writes one row for each attempt the agent completes, as the attempt
ends. A line that starts with `#` is a comment; a reader of the rows skips it.

```text
index,attempt,tier,steps,achieved,reward,demon_error,epsilon,mean_alpha,x,y
# planning=<expectation or none>
<one row per agent attempt>
# baseline cycle=<cycle> index=<goal> attempt=<attempt> steps=<steps> achieved=<0 or 1> x=<x> y=<y>
# seed=<seed> side=<side> weights=<count> total_steps=<steps> behavior=<hex> checksum=<hex> wall_ms=<ms> steps_per_sec=<rate> retire_count=<count> retire_last=<event> imprint_distinct_abs=<counts>
```

| Column | Meaning |
|---|---|
| index | Position of the goal in the curriculum, from 0. |
| attempt | Attempt number at this goal, from 0. |
| tier | Difficulty tier of the goal. |
| steps | Actions executed in the attempt: the steps to achievement when the goal was achieved, otherwise the cap. |
| achieved | 1 when the attempt achieved its goal, otherwise 0. |
| reward | Sum of the attempt's rewards, in step order. |
| demon_error, epsilon, mean_alpha | The learner's mean absolute prediction error, exploration rate and mean step size when the attempt ended. |
| x, y | The body's position after the attempt's last step; x grows to the east and y to the south. |

The comment after the header names the planning selection. The last line is a
footer of `key=value` fields for the whole run, including the action
fingerprint (`behavior`), the agent checksum and the observed wall time.

The **comparator** is the random-policy diagnostic that `--baseline` selects. It
draws each action from its own seeded stream and from nothing else, and follows
the campaign the agent follows in a second copy of the initial world, which it
carries from attempt to attempt: the same requested goals, attempts per goal,
cycles and step cap. With `--csv`, each of its attempts is recorded in a comment
line before the footer, in campaign order, in the form shown above. `cycle` is
the cycle of the attempt, from 0; the other fields mean what the columns of the
same names mean. The line has no tier, reward or learner field: the comparator
has no learner and keeps no reward total, and a goal's tier is the one in the
agent's rows at the same index. An agent row holds no cycle: rows are written
in campaign order, so with one attempt per goal the row numbered r from 0
belongs to cycle ⌊r / goals⌋. These lines are written only when the
comparator's campaign completed. A campaign
with `--cycles 0` never completes, so it has no comparator record: command
admission (`Cli.demo` in [the CLI definition](../lean/Acorn/Host/Cli.lean))
refuses `--baseline` with `--cycles 0` before the agent runs.

The two arms follow one campaign. The comparator admits its plan from the same
arguments with the agent's own admission and asks the agent's own boundary
function what follows each attempt. `boundary_single_attempt` proves that with
one attempt per goal the next attempt does not depend on the outcome, so both
arms make the same attempts in the same order. `start_corresponds`,
`tick_corresponds`, `idle_corresponds` and `outcome_corresponds` prove that the
arms' attempts correspond at goal installation, at each step and at the outcome
row. That whole attempts therefore agree is argued, not machine-checked: no
theorem composes these steps over the comparator's attempt loop or the agent's
native loop. On that argument an attempt is the same function of the world and
the action sequence in both arms: it stops at the first step that satisfies the
goal or at the cap, and reports the same steps, completion flag and position.
`baseline_finishes` proves that the record of a bounded campaign is never cut
short. `baseline_action_code`,
`action_word_interval` and `action_word_count` give the comparator's action
law: each action is selected by 2 049 638 230 412 172 401 or one more of the
2⁶⁴ stream outputs
([comparator](../lean/Acorn/Host/Baseline.lean),
[runner proofs](../lean/AcornVerif/CurrentRunner.lean)).

Recording does not change either arm. An outcome row is a value handed to the
reporter, which returns nothing. `Attempt.finish_position` proves that the
stream continuing past an attempt is the attempt's own state with the attempt
recorded, and that the recorded position is that state's body position.
`foldOutcome_position` and `addOutcomeSteps_position` prove that the audit
digest and the step total do not read the position. The comparator is a pure
function of the world configuration, the seed and the campaign arguments, and
it runs after the agent's campaign has returned
([attempt protocol](../lean/Acorn/Host/Attempt.lean),
[metrics](../lean/Acorn/Host/Metrics.lean),
[comparator](../lean/Acorn/Host/Baseline.lean)).

## Reading the viewer

The viewer is an observation tool for the active run:

- **World and goals:** what the agent has observed and which assigned goals it
  has achieved within the attempt budgets. The viewer retains the map from
  telemetry; the learner receives its local observation.
- **Predictions:** estimates for the fixed prediction questions. Predictive
  agreement compares predictions with settled finite returns.
- **Behavior and options:** action values, option selections, boundaries and
  learned model estimates.
- **Learning and resources:** step sizes, feature activity, planning updates and
  execution diagnostics.

An empty or pending measure is waiting for sufficient data. Goal outcomes
describe the selected run and its attempt budgets.
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
- [PAR-10](prior-art-review.md#par-10--derived-exploration-rate): Derived exploration rate, [Acorn.Policy](../lean/Acorn/Policy.lean).
- [PAR-11](prior-art-review.md#par-11--generate-and-test-tester): Generate-and-test tester, [Acorn.FeatureLifecycle](../lean/Acorn/FeatureLifecycle.lean).
- [PAR-12](prior-art-review.md#par-12--ranked-learned-subtasks): Ranked learned subtasks, [Acorn.FeatureRanking](../lean/Acorn/FeatureRanking.lean).
- [PAR-13](prior-art-review.md#par-13--option-expectation-models): Option expectation models, [Acorn.Models](../lean/Acorn/Models.lean) over [Acorn.RankedFeatures](../lean/Acorn/RankedFeatures.lean).
- [PAR-14](prior-art-review.md#par-14--background-planning): Background planning, [Acorn.Planning](../lean/Acorn/Planning.lean).
- [PAR-15](prior-art-review.md#par-15--differential-control): Differential control, [Acorn.Average](../lean/Acorn/Average.lean).
- [PAR-16](prior-art-review.md#par-16--floatlib-rounding-theory): FloatLib rounding theory, a proof dependency, [AcornVerif.FloatLibBridge](../lean/AcornVerif/FloatLibBridge.lean).
- [PAR-17](prior-art-review.md#par-17--off-policy-option-learning): Off-policy option learning, [Acorn.Temporal](../lean/Acorn/Temporal.lean).
- [PAR-18](prior-art-review.md#par-18--off-policy-questions): Off-policy questions, [Acorn.OffPolicy](../lean/Acorn/OffPolicy.lean).

## Boundaries

Types constrain stored words and receiver-bound state. Restored and functionally
updated values must satisfy the same admission as initial construction. Learned
code cannot import host/handcrafted owners except at explicit composition roots.
A provenance witness declares an origin; review must assess whether it is honest.
The viewer receives telemetry and requests lifecycle stop only.
[Acorn.Decisions](../lean/Acorn/Decisions.lean) registers the admissions, parsers
and validity tests of the executing library whose direction is proved, with the
direction each proof establishes, and lists the decisions it does not register;
the [Regula audit](verification.md#regula-audit) requires a contract of every
registered function.

Core calls select an explicit research profile. The [prior-art register](prior-art-review.md#current-default-qualification)
records qualification decisions. Each proof states its hypotheses, including
conditions on policies, value projection and models. See the source comments,
[learned-only binding](learned-only-binding.md) and [verification](verification.md).
