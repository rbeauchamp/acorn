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
words, and the world's [timing](#the-time-a-world-declares).

Each step the world delivers one **percept**: a **frame** and the reward of the
preceding transition. A frame has three parts, one for each kind of learner input:

- **words**, opaque pairs of a channel and a 64-bit value, which the coder hashes
  into features;
- **symbols**, an array of 64-bit codes that the generated projection features
  sample. Every interface declares its shape and every frame fills it. The
  interface design's requirement R1, that a world may supply no symbol array, is
  deferred until its feature-construction semantics is decided;
  [issue #95](https://github.com/rbeauchamp/acorn/issues/95) tracks it. A world with
  only words can lay those words' codes over symbol positions, as the grid world does
  with its task context. The Microduck world's symbols are its depth zones, and for a
  body with no depth sensor its frames fill every position with one constant, so every
  generated unit is constant there;
- **signals**, one number per prediction question the world declares.

A frame also carries the world's declared subtask potentials, which only the
`spatial` comparison reads, and whether the preceding transition achieved the
installed goal. That achievement event is departure
[D8](learned-only-binding.md#d8--achievement-event--step-10): it forces an
option's stopping decision to end, for the executing option and for the stored
off-policy trajectory of every other option, and the coder does not read it.
Nothing else is in a percept.
The agent answers with one action, a number below the interface's action count
([`Agent.act`](../lean/Acorn/Handcrafted/Agent.lean)).

The modules that compose the agent import no world: the boundary audit refuses a
world-independent agent module that imports a host module. In every world one
frame activates at most a number of features fixed by the interface and the
feature configuration (`Agent.frame_length`).

### The two parts of a step

A step has two parts ([definitions](../lean/Acorn/Handcrafted/StepParts.lean)).
`Agent.choose` advances the clock, encodes the percept's frame and selects; its
result holds the decision. `Chosen.learn` completes the step from that result:
off-policy learning of the options that are not executing, primitive credit, the
prediction demons, every option's questions and the tester. A **step order**
([`StepOrder`](../lean/Acorn/Timing.lean)) is part of an agent's construction and
selects one of three steps.

Under `learn-then-act`, the default, both parts run before the world receives the
action. `Agent.act_parts` proves that the two parts then compose to `Agent.act`,
for every agent state and percept, in every world.

Under `plan-after-act` the host releases the action after the first part, and the
second part runs after the world's transition. Selection runs no planning, and
the planning of a free boundary is the first work of the second part
(`TemporalControl.planAfter`): the same planning function, on the meta-controller
after that decision's on-policy credit. This is a different step
([PAR-19](prior-art-review.md#par-19--planning-after-the-action)). It differs from
the default at a free dispatch only: a step whose decision records no meta
decision is the executed step, with the same next agent and the same decision
(`Agent.actOrdered_undrawn`), and every free dispatch records one
(`TemporalControl.atBoundary_meta`).

Under `act-then-learn` the host also releases the action after the first part, and
the first part makes every draw of the step and takes no reward word
([definitions](../lean/Acorn/Handcrafted/DrawFirst.lean)). Its dispatch,
`TemporalControl.drawFirst`, has no reward parameter, so two percepts with one
frame and two reward words give the same decision, the same temporal state and
the same record of owed writes (`Agent.choose_reward`): no draw reads a learner
write of the reward. The first part does read the frame's achievement event
([D8](learned-only-binding.md#d8--achievement-event--step-10)), on which an
executing option ends, and in the grid world the reward word is a function of
that event (`StepResult.reward_completion`); so the action is not independent of
the event. The second part makes the
writes of selection that read the reward, from that record
(`TemporalControl.settle`): the owed meta reward and, on a served step whose run
held no option, the advance of the deferred meta clock; or the terminal credit of
an option that closes, the on-policy credit of the meta decision, and the
settlement, the start and the first credit of an option that starts; or the
credit of a continuing option. Then it plans, as under `plan-after-act`, and makes the
updates that follow selection in every order. This is a third step
([PAR-20](prior-art-review.md#par-20--acting-before-learning)). It is the step of
`plan-after-act`, with the same next agent and decision, on every percept whose
decision starts no option, unless an option closes at a free dispatch under the
discounted criterion (`AcornVerif.DrawFirst.actThenLearn_planAfterAct`). It
can differ in those two cases and in no other. Both executed dispatches are one
specification, `AcornVerif.DrawFirst.dispatchForm`, which reads its mode in two
places, for every state, frame and reward word
(`AcornVerif.DrawFirst.selectWithOperations_form`,
`AcornVerif.DrawFirst.drawFirst_form`). The two orders need not differ at each
instance of those cases: in a frozen profile a free dispatch that starts an
option gives one result in both (`AcornVerif.DrawFirst.boundaryForm_frozen`).
The two places:

- An option that starts draws its first action from its own frozen policy as the
  preceding step left it, after the assignment refresh
  (`AcornVerif.DrawFirst.drawBoundary_start`). Under the other orders it draws
  after the terminal credit, the meta credit, the settlement and the invocation
  start (`AcornVerif.DrawFirst.dispatchMeta_start`). The writes of the start are
  one function in every order, `TemporalControl.startOption`
  (`TemporalControl.settle_started`), and the drawn decision is the input that
  this difference changes.
- Under the discounted criterion the terminal credit of an option that closes
  follows the assignment refresh, as it does under the differential criterion in
  every order. The refresh has to precede the draws, and the credit reads the
  reward. The refresh retains the original owner of a slot that it replaces, and
  that owner takes no credit. Where the closing option is kept and the meta draw
  selects it again, the state that `TemporalControl.startOption` is given can
  differ as well, by this difference.

What each draw of the first part reads, by the operation that makes it:

| Draw | What it reads | Statement |
|---|---|---|
| A served exploration step | Its action repeats the action of its run and consumes no draw. The values the decision reports are read from the controllers | `TemporalControl.serve_frame` |
| A primitive draw | The persistent draw from the primitive controller, with the weights the agent held before the percept and the exploration rate this step's schedule has advanced to | `TemporalControl.choosePrimitive_snapshot`, `TemporalControl.select_keeps` |
| A continuing option | The option's own policy, frozen at the decision's frame from the option the agent held before the percept; selection writes no learner and no objective before it | `Skill.decide_policy`, `Skill.step_drawn`, `TemporalControl.prepare_lifecycle` |
| The meta draw of a free dispatch, `learn-then-act` | The meta-controller after the assignment refresh and after this frame's planning | `TemporalControl.atBoundary_meta` |
| The meta draw of a free dispatch, `plan-after-act` | The meta-controller after the assignment refresh and before this frame's planning | `TemporalControl.atBoundary_unplanned` |
| The meta draw of a free dispatch, `act-then-learn` | The meta-controller after the assignment refresh and before this frame's planning; no write that reads the reward precedes it | `AcornVerif.DrawFirst.drawBoundary_meta`, `AcornVerif.DrawFirst.drawBoundary_unplanned` |
| The first action of an option that starts, `learn-then-act` and `plan-after-act` | The option's own policy after the terminal credit and the settlement that this percept causes | `Skill.beginTemporal_policy`, `AcornVerif.DrawFirst.dispatchMeta_start` |
| The first action of an option that starts, `act-then-learn` | The option's own frozen policy in the state after the assignment refresh and the meta draw, before every write that reads the reward | `AcornVerif.DrawFirst.drawBoundary_start` |

Each row names statements about the operation that makes the draw. Which operation
a step calls is the definition of selection; `TemporalControl.select_keeps` and
`TemporalControl.select_unplanned` are the statements here about every branch of
it. Under `act-then-learn` the rows of the served step, the primitive draw and
the continuing option hold as they do under `plan-after-act`, on every step whose
decision starts no option and that does not close an option at a free dispatch
under the discounted criterion: there the draw-first dispatch followed by the
owed writes is selection (`AcornVerif.DrawFirst.selectWithOperations_settle`).
On the other steps those draws are made by the same operations, which is read
from `TemporalControl.drawFirst` and `TemporalControl.drawBoundary` and is not a
theorem.

The next paragraphs compare `learn-then-act` with `plan-after-act`. Under
`act-then-learn` the meta draw reads what it reads under `plan-after-act`
(`AcornVerif.DrawFirst.drawBoundary_unplanned`), and each write these paragraphs
place in the first part is in the second part, after the action. The first action
of an option that starts is the exception these paragraphs do not cover for
`act-then-learn`: the list above gives what it reads.

The meta draw is the one draw that reads the meta-controller, and the order
changes what it reads. The decision keeps the frozen snapshot that the draw was
made from, and the order changes every later read of that snapshot. The first
part has three:

- the settlement of an option that starts takes its stopping estimate from the
  snapshot (`TemporalControl.dispatchMeta`, `Skill.settleTemporal`);
- under the differential criterion, the terminal credit of the option that
  closes takes the snapshot's value of the drawn meta action
  (`TemporalControl.atBoundary`, `TemporalControl.closeOption`);
- the on-policy credit of the meta decision forms its error and stores its lag
  from that same value (`TemporalControl.learnMeta`, `Controller.policyStep`);
  the paragraph below that begins "The deferred planning has a consequence"
  gives the consequence of the lag.

The second part has one: the off-policy learning of every option that is not
executing compares against a stopping estimate that is read from the snapshot
(`TemporalControl.stoppingEstimate`, `TemporalControl.followOptions`,
`Skill.followTemporal`). The decision also reports the snapshot's values and
probabilities to an observer (`Agent.observe`). Two closings in the first part
read the meta-controller itself, as the current value function, which under
`plan-after-act` holds no planning of this frame: the model of the option that
closes under the differential criterion (`Skill.endTemporal`) and the model of a
stored trajectory that the settlement stops (`Skill.stopFollowing`).
`TemporalControl.takeoverValue` uses the same stopping estimate on a served step
only. That step records no meta decision (`TemporalControl.serve_undrawn`), so
the estimate is read from the decision's own meta values and the current rate,
and the two orders are one step there (`Agent.actOrdered_undrawn`).

So the first action of an option that starts can read different weights under
the two orders, also when the meta draw selects the same option. For an option
that is not executing, the stopping decision of its stored trajectory and the
stopping value that a stop credits to its policy (`Skill.stopFollowing`) can
differ under the two orders at a frame that records a meta decision. No theorem
states the difference of one of these reads: each follows from the definitions
named, with the two statements of the snapshot (`TemporalControl.atBoundary_meta`,
`TemporalControl.atBoundary_unplanned`).

The deferred planning has a consequence for the next credit of the
meta-controller. The on-policy credit of a decision stores the value of the drawn
meta action, read from the decision's snapshot, as the controller's lag
(`Controller.valuesStep_lag`). Planning writes weights and leaves the lag
unchanged (`planning_lags`), and the next credit forms its error from the lag.
Under `learn-then-act` this frame's planning precedes the snapshot the lag is
read from. Under `plan-after-act` it follows, at the same feature vector, so the
next credit's error is formed from a value that planning has since changed.

The assignment refresh precedes the draws in every order; with learned subtasks it
is a function of the Demon-0 weights and the objectives the step started from, and
of no part of the percept (`TemporalControl.select_assigns` for selection,
`AcornVerif.DrawFirst.drawFirst_assigns` for the draw-first dispatch). Under
`plan-after-act` the first action of an option that starts still reads weights
that this percept's reward has changed, so that order is not a complete "act,
then learn". `act-then-learn` is: the option learner has a credit that takes the
drawn decision as an input (`Skill.optionCredit`, `Skill.creditTemporal`, with
`Skill.optionStep_credit` and `Skill.stepTemporal_credit`), and the terminal
credit and the settlement follow the action.

In every order the first part writes neither the primitive controller nor a
prediction demon (`Agent.choose_keeps`), so the reward of a percept reaches those
two in the second part. The second part draws nothing from the action generator
(`Chosen.learn_rng`); its tester draws from the feature generator's own stream.

The host protocol releases the action between the parts as one pass
([definitions](../lean/Acorn/Host/Attempt.lean)). For every callback and input,
that pass gives what both parts followed by the release give: on acceptance the
same committed stage, and on a refusal the same refusal with the same learned
stage (`DecisionInput.chooseOwned_release`). The two native loops of an attempt
are proved against one pure fold, `Attempt.complete`, which applies the whole
step of the callbacks once for each pass, in order, and ends at the first
refusal: every value that either loop returns, from every world token, agrees
with the fold in its run state and outcome, or in its refusal
(`runAttemptSteps_complete`, `runReleasedSteps_complete`,
`runAttempt_complete`). A refusal of an action holds the stage of the refused
pass, and the agreement fixes it. The fold reaches the attempt of that pass from
the start in accepted passes (`Attempt.Reaches`), that attempt is not finished
and senses an input, and the stage is the whole step of the callbacks, the first
part and then the second, applied once to that input
(`Attempt.complete_learned`). A refusal of an observation holds no stage. So the
second part runs exactly once on a refused pass in both loops. These are
statements of partial correctness: they concern the values a loop returns, and
they use no hypothesis on the clock or the observer. The order of effects, the
observer's own effects, the terminal frame, the resource counters and the
reported durations are outside them. A campaign reports the error of a refusal
and returns no agent, in every order.

### The time a world declares

A world declares its **timing** in its interface
([`Timing`](../lean/Acorn/Timing.lean)). A `synchronized` world takes one transition
for each action and waits for it. A `wallClock` world moves while the agent
computes, and declares the length of one **action cycle** and a **latency**, a
positive number of cycles. The grid world declares `synchronized`
(`Grid.interface_timing`), and its attempt loops take each transition as one call
of the world's step function.

For a wall-clock world the two numbers get their meaning from functions of the
declaration, of an origin and of instants. An instant is a reading of a host's
monotonic clock in nanoseconds, a natural number, so the arithmetic is exact; it is a
type of its own, so a count of cycles cannot stand where an instant is expected.
Cycle `index` starts at `Pace.boundary origin index`. The deadline of the action of
the percept of that cycle is `Pace.deadline origin index`, the start of the cycle
`latency` cycles later. `Pace.meets` is the verdict on the instant an action is
released at: true exactly when the release falls in a cycle before the one the
deadline starts (`Pace.meets_index`), which is when no cycle from that one on has
begun at the release (`Pace.meets_begun`). `Pace.first` is the first cycle that
starts at or after an instant (`Pace.first_starts`, `Pace.first_least`), and less
than one cycle after an instant that is not before the origin (`Pace.first_within`).

**A missed deadline is a fault during which the preceding action holds, until it
lapses.** A `Force` is an action in force, with the instant from which the world's
default replaces it, if the world has one: its **lapse**. A world whose actions stay
in force until the next release has no lapse. A `Standing` is what a host of a
wall-clock world holds between two events: the force of the last release and the
percept, if any, whose action is not released yet. `Pace.outcome` gives what holds
at an instant for a standing, in a world with a declared default: the action that
the force names at the instant, which is its action before the lapse and the default
from it (`Pace.outcome_action`, `Force.named_lapse`), and whether a fault holds. A
fault holds exactly while a percept awaits its action at or after its deadline
(`Pace.outcome_fault`). For one step, in which a percept is sensed with a preceding
force and its action is released at some instant (`Standing.during`; an action is in
force after the instant of its release):

- a fault holds exactly from the deadline to the release (`Pace.step_fault`);
- at every instant of the fault at which the preceding force has not lapsed, the
  preceding action is in force (`Pace.step_holds`). A force with no lapse has lapsed
  at no instant, so in a world whose actions do not lapse the preceding action holds
  through the whole fault;
- from the lapse of the preceding force, the fault has the world's default
  (`Pace.step_lapsed`);
- after the release the outcome follows the chosen force: its action until its lapse,
  and the default from it (`Pace.step_action`);
- no instant has a fault exactly when the release meets the deadline
  (`Pace.step_faultless`).

These hold for every instant of release, so in that step the force of a late action
is the one that counts after its late release. With a cycle of 200 ms, a latency of one cycle, the action
of cycle 0 released at 250 ms and no lapse, the fault holds from 200 ms to 250 ms
with the preceding action in force, and the chosen action is in force after 250 ms.

When the earlier of two actions is released at or after the start of its percept's
cycle and the later one meets its deadline, for percepts `span` cycles apart, the
later release is less than `span + latency` cycles after the earlier one
(`Pace.met_gap`).

These are statements about the functions. No executing loop keeps a standing or
reads a cycle or a latency, and no executing world declares a wall clock. A host of a
wall-clock world computes its verdicts with `Pace.outcome`; the pure transitions of the
Microduck's host do, and no executing loop calls them yet. Nothing here states that a
world keeps in force the action that a standing names.

Operation in real time needs three more parts, and none is built:

- a host loop for a world on a wall clock, which reads the declared timing and
  counts a missed deadline as a fault
  ([issue #95](https://github.com/rbeauchamp/acorn/issues/95));
- a bound of the work of each part of a step;
- the exact save and restore of the agent. An exact saved image of the agent is
  not part of the interface yet.

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
most 381 words, feedback channels from `0x50` and the timing `synchronized`. Its adapter builds each percept
from the host's observation and the preceding result. `Agent.grid_inputs` in
[the host binding](../lean/Acorn/Host/AgentInterface.lean) states, for every
agent state, observation and reward word, that the coder's words and symbols, the
prediction signals and the declared potentials the agent receives are exactly the
values of the host's channel, signal and potential definitions, and
`Agent.callbacks_act` that under the default step order the host's step is the
interface agent's step on that percept. `Grid.sensorWords_clear` discharges the feedback-channel condition for
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
reach targets and every pseudo-random stream. Its properties come in two tiers.
A universal property is a theorem about the generator, true for every seed. A
selecting property is a fact about one seed's world that is not a theorem about
every seed: it may hold for one seed and fail for another. A certificate decides
it for a given seed, as
[the next section](#what-a-certificate-establishes-about-one-seed) describes.

The properties below are universal: proved of the executed definitions, for
every seed, side, world and action, under the hypotheses each row names. None of
them shows that a goal can be achieved.

| Property | What is proved | Theorems |
|---|---|---|
| Where the reach targets are | Goals 3 and 7 are the reach goals. Each target lies in a fixed square window around the center of the box: within the near radius (12 to 40 tiles) for goal 3 and the far radius (24 to 120 tiles) for goal 7. The generator places them by a hash of the seed and never reads the terrain. | `reach_targets` |
| The goal box is inside the world | A reach goal is met within three tiles of its target on both axes. For a side of at least 54, every such position is inside the box the body moves in; the standard configuration admits sides from 64. | `goal_box_in_world`, `standard_goal_boxes` |
| One target coordinate over seeds | Each value of a window is one target coordinate on ⌊2⁶⁴ / m⌋ or one more of the 2⁶⁴ seeds, where m is the window's width. This counts seeds: it is a distribution only for a seed drawn uniformly, and it says nothing about two coordinates jointly. | `coordinate_seed_count`, `hash2_injective` |
| Reaching reads position only | A reach goal is satisfied exactly when the body is in the goal box, whatever the inventory and the time. | `reach_satisfied_iff`, `reach_goal_iff` |
| Survive goals do not depend on the policy | From a goal's installation, every action sequence whose steps the world accepts satisfies a survive goal exactly when its length has reached the required duration. For every agent, each tick of an attempt that acts reports completion exactly when the attempt's step count has reached that duration. An attempt acts only below its cap, so one whose cap is below the duration never reports completion. That an attempt with a sufficient cap ends achieved at exactly that step is argued from these per-step statements and the attempt's stopping rule; no theorem composes them over the attempt loop. Assumes that the 64-bit clock does not wrap. | `survive_actions`, `survive_tick` |
| Tools and gold are never lost | No world step removes an owned axe or boat or lowers gold. A craft goal or a gold goal achieved once is therefore reported achieved by the first world step of every later visit, whatever was done in between. Wood, stone and food can be spent, so the other collect goals have no such guarantee. | `step_retains`, `absorbing_revisit` |
| Energy | Of any N steps, at most (4N + 2000) / 24 are exhausted: steps on which the body cannot pay for its action and rests. Of any N successive moves at most (2N + 21) / 22 are, so at least 2727 of 3000 moves are paid for. That a move is paid for does not show that the body changed position. | `trace_exhausted`, `moves_exhausted`, `moves_paid_at_cap` |
| Where the terrain refuses | The generator refuses a position exactly when, at one of its four octave scales (the base scale doubled zero to three times), the binary32 quotient of a coordinate of the position by the scale is positive infinity or a finite value of at least 2⁶³ − 1. The saturating signed 64-bit cast of that quotient's floor then produces the last coordinate, which has no successor. The seed enters no refusal. The effective kind of a tile and an entry into it are refused at exactly the same positions. | `terrain_isOk`, `tileKind_isOk`, `enterable_isOk` |
| Which paid actions are refused | A paid action reads the terrain of at most one tile. A move reads the tile one step ahead when that tile is in the box, a harvest reads the tile that the body faces, in the box or not, and waiting, crafting and eating read none. The effect of the action is refused exactly when the terrain refuses that tile, and the paid action exactly when, in addition, the energy pays the cost of the action; an action that the energy does not pay for rests the body and is accepted. A move never overflows a coordinate, because the body is in the box. | `performAction_isOk`, `payAndAct_isOk` |
| Passability is static | Whether the body may enter a tile depends on the tile's generated terrain and on the boat, and on nothing else: not harvesting, regrowth or time. A mountain tile is never enterable, and a water tile exactly when the body owns a boat. A step leaves the body where it is or moves it one tile in one of the four directions, never onto a mountain and never onto water without a boat. | `enterable_static`, `mountain_closed`, `water_needs_boat`, `step_adjacent`, `step_terrain` |
| The spawn | The spawn search follows a spiral whose schedule contains every tile of the box, and one application of its rule reports an early exit only at a walkable tile with two trees within four tiles. Either the spawn is a walkable tile whose trees plus stone within four tiles are at least two; or no tile of the box is walkable with two trees within four tiles, and the spawn is a walkable tile whose trees-plus-stone score no scored tile of the box exceeds, or the center of the box when no tile is walkable. The first case holds whenever some tile of the box is walkable with two trees within four tiles; it bounds trees plus stone, so two trees near the spawn are not guaranteed. A scored tile is a walkable one whose two counts were not refused. Holds whenever the search returns a spawn. | `selectSpawn_post`, `spawn_of_rich`, `spawn_walkable`, `spiral_covers`, `considerSpawn_contract`, `countKindNear_eq` |

Not proved for every seed: that the spawn search returns a spawn rather than a
refusal; that a goal box can be entered or reached; that the walkable terrain is
connected; and any bound on the distance from the spawn to a target. No theorem
states that a goal box can be reached for every seed: the generator places each
target by a hash of the seed without reading the terrain, so nothing in its
construction relates a target to the terrain around it. For a given seed, an
accepted blocked certificate of mountains alone proves the reach goal infeasible
at every cap (`blocked_infeasible`). The owners of the table's theorems are the
[step proofs](../lean/AcornVerif/CurrentStep.lean),
[terrain proofs](../lean/AcornVerif/CurrentTerrain.lean),
[goal proofs](../lean/AcornVerif/CurrentGoals.lean),
[curriculum proofs](../lean/AcornVerif/CurrentCurriculum.lean),
[spawn proofs](../lean/AcornVerif/CurrentSpawn.lean) and
[action proofs](../lean/AcornVerif/CurrentActions.lean).

### What a certificate establishes about one seed

A selecting property is decided for one seed by a **certificate**: a small piece
of data that an executable **checker** accepts or rejects. Each checker is a
decision over the executed world definitions, and a theorem states what its
acceptance establishes. The theorems are sound and not complete: an accepted
certificate proves its row below, and a rejected or missing one proves nothing.
The checkers are in [the certificate module](../lean/Acorn/Host/Certificate.lean)
and the theorems in
[the certificate proofs](../lean/AcornVerif/CurrentCertificates.lean).
[AcornVerif.Decisions](../lean/AcornVerif/Decisions.lean) registers each checker
as a Regula contract that states what its acceptance establishes.

| Certificate | The checker accepts when | What acceptance proves | Theorems |
|---|---|---|---|
| Replay: an action list, for a start world, a goal and a cap | The list is nonempty and no longer than the cap, and replaying it through the executed step from the start world with the goal installed succeeds and ends in a world that satisfies the goal (`replayCertified`). | The goal is feasible from that start world within that cap (`CurrentCertificates.Feasible`): some run of at least one and at most that many executed steps ends satisfying the goal, and its last step reports completion. For a reach goal the run ends with the body in the goal box; for a collect goal it ends holding the count. | `replay_feasible`, `feasible_done`, `reach_path`, `collect_path` |
| Blocked: a finite set of tiles, for a reach target and a start tile | The start tile is outside the set, every in-box tile of the goal box is in it, and each tile of the set is impassable or has all its in-box neighbors in the set (`regionBlocked`). Impassable means mountain, or mountain and water when the certificate is for a body without a boat. | From any world whose body is on the start tile, no run of steps and goal installations in any order puts the body in the goal box, so the reach goal is never satisfied. A set that counts water covers only the runs that end without a boat. A set of mountains alone makes the reach goal infeasible at every cap. Assumes each step succeeds. | `blocked_outside`, `blocked_unsatisfied`, `blocked_infeasible` |
| Stance: a tile and a facing direction, for an item | The tile the stance faces has static terrain that yields the item, the stance tile is walkable, and the tile behind the stance is in the box and walkable (`stanceCertified`). | In every world, a paid move in the facing direction from the tile behind the stance puts the body on the stance facing the resource, and a paid harvest from the stance adds the item: three wood with an axe, one item otherwise. A wood stance needs its tree standing; stone and ore have no such condition, since no step depletes them. Assumes each step succeeds. | `stance_enter`, `stance_harvest`, `stance_approach` |

What these do not establish:

- A replay certificate speaks of the start world it was checked from. The tool
  below checks from the spawn of the generated world, before any step. A campaign
  begins a later goal's attempt from the world its earlier attempts left, which
  the certificate does not describe.
- `CurrentCertificates.Feasible` is a statement about runs of the executed world
  step. No theorem here composes it with the attempt loop that an agent drives.
  For the grid world of the kernel, `feasible_iff_certificate` shows it
  equivalent to `Kernel.Feasible`, the feasibility of
  [the next section](#what-a-class-of-worlds-can-and-cannot-show).
- A blocked certificate that counts water says nothing about a body that builds
  a boat.
- A stance certificate does not show that the stance can be reached from the
  spawn. A replay certificate for collecting one item, checked from the spawn,
  shows that a run from the spawn within the cap ends holding the item
  (`collect_path`). It names no stance and does not show that a certified stance
  was reached.

**The certificate tool.** `world-certificates` generates the standard world of
each listed seed, proposes certificates and prints what the checkers accepted:

```sh
./scripts/lean.sh exe world-certificates SIDE CAP SEED [SEED ...]
```

For each seed it prints the spawn, one line for each of the two reach goals, and
for wood, stone and gold a stance line and a line for collecting one item from
the spawn. A line carries its certificate: the action list as one digit per
action index, the tiles of a blocked region, or the stance tile and direction. A
verdict of feasible, blocked or certified is printed only from a certificate its
checker accepted. A blocked line names its scope: any body, or a body without a
boat. A verdict of uncertified means that no proposed certificate was accepted
and establishes nothing about the seed.

The search that proposes certificates is
[unverified](../lean/Acorn/Host/CertificateSearch.lean): it explores the tiles
enterable without a boat, breadth first from the spawn. It does not propose a
replay that builds a boat, although the replay checker would accept such a list.

When no replay is accepted for a reach goal, the tool proposes a blocked region:
the goal box, every tile connected to it through tiles that are not impassable,
and their impassable neighbors, first with mountains alone impassable and then
with mountains and water. A proposal holds at most 4096 tiles, the region budget
set in [the tool](../lean/Acorn/Host/CertificateDriver.lean), because the
checker's work is quadratic in the region size. The line reads blocked only when
the checker accepts a proposed region. Otherwise it reads uncertified, which
establishes nothing: a goal box that the search cannot walk to from the spawn is
reported blocked for a body without a boat only when the region around it fits
that budget.

The boundary audit refuses an import, direct or transitive, of the agent
composition, the campaign runner or the random-policy comparator by the tool's
modules, so the tool cannot construct or run any of them. The tool's import
closure does hold the attempt protocol and campaign admission, which it reaches
through the curriculum module. Its code starts no attempt, and no audit enforces
that. Its only world steps replay candidate action lists: each candidate once
while the search settles it, and at most once more by the replay checker. A
candidate the checker rejects, for instance one longer than the cap, has been
replayed and is not printed.

A study can fix its class of worlds before any run by naming a printed verdict,
for example the seeds for which the far reach line reads `verdict=feasible`,
together with the universal theorems it uses. The summary counts are over the
listed seeds only. A fraction of the 2⁶⁴ seeds that have a property is an
estimate from a sample of seeds, never a certified fact; a certificate certifies
its own seed. Running the tool at a seed is access to that seed's world: do not
run it at the seeds of a registered study before that study has recorded its
result, and record any such access in the study.

### What a class of worlds can and cannot show

The properties above concern one generated world. A claim that learning is
needed is a claim about a class of worlds, and three modules state what such a
claim can rest on. [The interaction kernel](../lean/AcornVerif/Kernel.lean)
defines a world and an agent over the executing interface: an action is an index
below the interface's count, a percept is the executed frame with the reward
word of the preceding transition, a world is a deterministic state machine that
delivers one percept at each state, and an agent turns its memory and one
percept into an action and its next memory, the shape of the executed decision.
[The world-class layer](../lean/AcornVerif/WorldClass.lean) defines an attempt
goal: a predicate on states with a step cap, met when some state at step 1 to
the cap satisfies it. A goal is feasible from a start state when some action
sequence meets it within the cap (`Kernel.Feasible`), and an agent achieves it
when the agent's own closed loop does. A class of worlds is a family of worlds
with a start state each, and an agent solves a member when it achieves that
member's goal from that member's start state. A class of agents is a predicate
on agents, and an agent is admitted when it satisfies the predicate. A need
bound of k for a class of agents says that every admitted agent solves at most k
members of the class of worlds (`Need`). In one world a need of zero says that
no admitted agent achieves the goal. [The grid
instance](../lean/AcornVerif/CurrentGridWorld.lean) builds the grid world of the
kernel from the executed step, observation and percept adapter. A step the host
refuses leads to an absorbing refused state, where no goal is satisfied.

Three kinds of agent are distinguished. An experience-free agent's memory
advances without reading percepts, though its action may read the current one.
An open-loop agent reads no percept at all. A reactive agent's action is a
function of the latest percept alone.

[Issue #69](https://github.com/rbeauchamp/acorn/issues/69) asks for need against
frozen within-envelope agents, the uniform-random comparator included. That
class is the experience-free agents within a memory width with room for the step
counter (12 bits at a cap of 3000): what such an agent retains does not depend
on what it has perceived. `experienceFree_iff_infeasible` covers it. The
comparator is open-loop, so it is experience-free
(`comparator_openLoop`). No width is proved for its stream, and the equivalence
needs none for it: an infeasible goal is achieved by no agent.

| Property | What is proved | Theorems |
|---|---|---|
| The grid instance is the executed world | The kernel world's state under a list of actions holds the world of the executed action fold, and is refused exactly when that fold is. A goal is feasible in the kernel world (`Kernel.Feasible`) exactly when the executed fold of some list of one to cap host actions ends in a world that reports the installed goal satisfied. From a host world with a goal installed, that is exactly when the goal is feasible in the sense of the certificate section (`CurrentCertificates.Feasible`), which an accepted replay certificate proves and a blocked certificate of mountains alone refutes. | `foldl_world`, `feasible_iff_replay`, `feasible_iff_certificate` |
| The step has two parts in the closed loop | A two-part agent is a kernel agent given as a first part that selects and a second part that learns from what the first returned. The executed agent of the default step order in that form is the executed kernel agent. The executed agent of `plan-after-act` or of `act-then-learn` in that form is the kernel agent of `Agent.actOrdered`; no theorem states that it equals or differs from the default one. `plan-after-act` and the default take the same step wherever the decision records no meta decision. A moving world also changes while the agent computes; it is a model that no executing world implements. The model takes one two-part agent and a position of the world's transition: after both parts, or between them. From one state and memory, one interaction takes the same action and keeps the same memory at both positions, and with the transition after both parts the action lands on a state that has also moved during the second part; over a run the two positions can then diverge. Two statements are derived for the loop at either position and for every assignment of work to the parts. The memory before a time is the fold of the two parts over that loop's own percepts before it, in order, so each percept is learned exactly once. When the world waits, the loop is the loop of the kernel, so the position changes no state, percept, memory or action. One interaction is also the same at both positions when the world's own change commutes with its transitions. | `executedParts_agent`, `memory_parts`, `Moving.interact_landing`, `Moving.landing_learn`, `Moving.interact_memory`, `Moving.loop_memory`, `Moving.loop_waits`, `Moving.interact_commutes` |
| The executed decision is a kernel agent | The executed agent's decision function is an agent of the kernel over its own interface, so every statement about all agents covers it. Where the host observes, the host's callback of the default step order returns that agent's action and next memory on the kernel world's percept. The callback of another order is the two parts of that order on the grid percept (`Agent.callbacks_ordered`); no theorem links it to the kernel world's percept. | `executedAgent`, `executed_callback` |
| In one world, need is infeasibility | A clocked script is an agent whose memory is a step counter and whose action at a count is the corresponding action of a fixed sequence. It reads no percept, and its counter fits ⌈log₂ (cap + 1)⌉ bits: 12 bits at a cap of 3000. A goal is feasible from a start state exactly when the clocked script of some sequence achieves it. So, for every class of agents that admits the clocked scripts, no admitted agent achieves a goal exactly when the goal is infeasible. The experience-free agents within a memory width with room for the counter are such a class. | `feasible_iff_script`, `script_openLoop`, `script_memory_clog`, `script_fits_attempt`, `need_iff_infeasible`, `experienceFree_iff_infeasible`, `need_single_iff_infeasible` |
| The comparator is open-loop | The uniform-random comparator's action and next stream are functions of its stream alone. Its action sequence is therefore the same in every world over the grid interface from every start state, and its action is the executed draw. | `comparator_openLoop`, `comparator_actions`, `comparator_action` |
| Against open-loop agents, need is coverage | An agent is blind on a class when its actions do not depend on the member until that member's goal is met; every open-loop agent is blind on every class. If each single action sequence meets the goal of at most k members, every blind agent solves at most k members, and for open-loop agents the two bounds are equivalent. | `openLoop_blind`, `need_of_covered`, `covered_iff_need` |
| The dynamics do not read the goal | A world step without the installed goal succeeds exactly when the step with it does, and reaches the same world apart from the goal. From one world, the body follows the same walk under one action sequence whichever reach target is installed, and each step moves it at most one tile along one axis. | `step_physical`, `path_physical`, `step_near` |
| Reach targets one action sequence can meet | A walk of n moves comes within three tiles of at most 49 + 7n lattice points. So from every host world, for every terrain, one action sequence meets the reach goal of at most 49 + 7n targets in n steps, and so does every agent that is blind on the class of targets, the comparator included. At a cap of 3000 steps that is 21049 targets. A far window of radius 120, which every side from 720 has, holds 57600 target tiles, so at least 36551 of them are outside every set of window targets one sequence meets: it meets under 36.6 percent. | `card_swept`, `reach_covered`, `reach_need`, `comparator_reach`, `far_window_unsolved`, `farRadius_large` |

What these theorems do not establish:

- **Need in one generated world.** In one world a goal is either infeasible or
  achieved by a clocked script that learns nothing. Need against the comparator's
  class can only be stated about a class of worlds, about what the agent is not
  told. A reactive clocked script takes one action throughout
  (`script_reactive_constant`), so a class of reactive agents admits only
  constant scripts and the equivalence says nothing about it.
- **A bound for agents that read the displacement.** The reach bound holds for
  agents whose actions do not depend on the target until it is reached, and does
  not apply to an agent whose actions read the displacement. Acorn's observation
  gives the exact displacement to the target, and the frame carries it to the
  agent, which makes that dependence possible. The executed agent is not shown
  blind on the class of targets, so the theorem supplies no bound for it; that
  its actions do depend on the target is not proved either. A fixed rule that
  steps toward the target needs no experience. No theorem here gives a goal
  whose solution the observation does not show.
- **A bound over seeds.** The reach bound counts target positions for one host
  world. The generator ties the target to the seed, so reading it as a fraction
  of seeds assumes that the seed hash places targets independently of the walk
  (assumed).
- **A bound for the near window.** The near window has at most 6400 tiles, fewer
  than 21049, so the count excludes no near target.
- **That any reach goal is feasible.** The bound is an upper bound. It does not
  show that a target can be reached.
- **That the kernel loop is the host's run.** The grid instance covers one
  attempt's steps from a state with its goal installed. Goal installation
  between attempts and the host's accounting callbacks are outside it. An
  accounting callback changes neither the next decision nor the learners after
  it (`act_accounting`, [below](#the-oak-picture-and-the-executed-agent)), but
  no theorem composes that along a run, so no theorem shows that the host's run
  and the kernel's closed loop take the same actions. Where the host refuses to
  observe, the kernel world delivers a blank percept that no executed run
  delivers.
- **Work and time.** The kernel has a memory axis and no axis for an agent's work
  per step or for the time a decision takes.

The counting argument is [the coverage proof](../lean/AcornVerif/Coverage.lean).

### An embodied world: the Microduck

The first world after the grid world is a small biped, Pollen Robotics' Microduck.
Its simulator runs the control daemon and the client interface of the robot. That
interface was observed in one run of the simulator; the record of its commands,
skills and timing is in
[a comment of issue 95](https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6046235895).
A client sends **intents**, never a joint command: a velocity, or a skill by name.
The daemon replaces a velocity by zero when it is 500 ms old, a skill runs for
0.5 to 2.8 s and is not interrupted, a command can be refused, and nothing waits
for the client. Six parts of this world are built, as pure definitions:
[the action table](../lean/Acorn/Host/Microduck/Action.lean),
[the bridge's state](../lean/Acorn/Host/Microduck/Bridge.lean),
[what the body senses](../lean/Acorn/Host/Microduck/Sensing.lean), kept as bounded
integers through [a conversion from decimal text](../lean/Acorn/Host/Microduck/Decimal.lean)
with its reader of one JSON number,
[the readers of a line of the daemon and the line of each command](../lean/Acorn/Host/Microduck/Wire.lean),
as JSON,
[what a host holds between two events](../lean/Acorn/Host/Microduck/Session.lean) with
its transitions,
[the pure core of the host's loop](../lean/Acorn/Host/Microduck/Loop.lean),
and [the interface value with the frame of a reading](../lean/Acorn/Handcrafted/Microduck.lean).
No driver of the loop and no transport exist yet, so no code of Acorn reaches the simulator and no executing code
builds a percept of this world
([issue #95](https://github.com/rbeauchamp/acorn/issues/95)).

**The daemon's networks are the world's actuation interface.** Every intent is
executed by a network inside the daemon, which holds the only write handle to the
motors. This is not a departure from the
[learned-only binding](learned-only-binding.md). The action path of that binding ends
at an action of the declared interface, and what executes an action belongs to the
world, as the grid world's step function does. Acorn authors none of these networks.
What it authors is on its own side of the boundary: the finite table of intents,
which is the interface's action set, with the commands of each action, its declared
duration and the rule that keeps a velocity alive. The table has no count of cycles
for an action: `Action.next` computes the cycle of the next percept from the instant
of the release. The classification has three consequences, which limit every result
obtained in this world:

- a primitive action is a pretrained behaviour of up to three seconds;
- nothing below an intent is learned: gait, balance and each skill are the world's;
- a result is a result about control over intents, and says nothing about learning
  to walk.

The daemon and the interface are the same in the simulator and on a robot. The
networks need not be: the vendor's simulator script loads one walking network and
one standing network, and the record says a stock robot defaults to another.

**Ten actions.** Each has an intent: a velocity, a skill, or a posture. The magnitudes
are the ones that moved the body in the observed run, with the networks of the
simulator script; forward at 0.15 m/s and every backward command up to 0.3 m/s did
not. The durations are the observed lengths of the skills with a margin.

| Action | Intent | Declared duration |
|---|---|---|
| `still` | zero velocity | none |
| `forward` | 0.3 m/s forward | none |
| `turnLeft`, `turnRight` | 1.5 rad/s to the left, to the right | none |
| `kickLeft`, `kickRight` | the kick skills | 0.6 s |
| `sit`, `stand` | the posture: sitting, standing | 1.2 s |
| `roll` | the forward roll | 1.4 s |
| `pick` | the pick from the ground | 3.0 s |

**No percept falls inside a running skill.** The declared pace is an action cycle of
200 ms and a latency of one cycle. The cycle of the percept after an action is
computed from the instant the action is released at, whether that release was timely
or late: `Action.next` (`Bridge.next` for a bridge's state) is the first cycle that starts no earlier than the release
plus the action's declared duration and a transit allowance, and it is after the
action's own cycle. `Action.next_covers` states the first property with no
hypothesis on the release, and `Action.next_least` that no earlier cycle after the
action's own has it. With the pick of cycle 0 released late, at 1 s, the next percept
is of cycle 21, which starts at 4.2 s, after the 4.01 s at which the declared
duration and the allowance have passed. A fixed number of cycles from the action's
own percept would not do: counted from cycle 0 it can end inside the skill. A host
owes that it senses the next percept at that cycle and no earlier. Nothing in the
bridge's state refuses an earlier release.

**The commands.** `Command` is everything a bridge can send: enable the policy, one
of the table's four velocities, one of five skills. It is a closed finite type. It
has no constructor for cutting power, shutting down or rebooting, the enable command
takes no argument, so no value asks to disable the policy, and no value carries a
velocity outside the table (the daemon does not clamp a velocity). `Command.line` is
the line of JSON of one send of a command: a request with the method and the
parameters of the record, and an identifier that the caller gives for each send, so
that an answer names one send and not a kind of command. Each magnitude of a velocity
is a numeral of a table, proved to write the thousandths of the action table over a
thousand exactly (`spelling_twist`). A line is the text of a request value, and the
parser of this repository reads the text of every such value back as the value
(`parse_request`, the first theorem about that parser on a family of texts), so for
every identifier and command it reads the line as the request, with exactly its
members and its parameters and no other (`Command.line_asked`); that a daemon reads
them so is not stated. The release of an action sends velocities and skills
only (`Action.commands_powered`), so the enable command is the bridge's own. Every
release sends a velocity first (`Action.commands_head`): a skill and a posture are
released with the zero velocity. The daemon exposes sitting and standing as one
toggle. `sit` and `stand` are two actions, and a release takes the posture of the
body as its caller states it: the toggle is sent exactly when the action asks for
the other posture (`Action.commands_toggle`).

**Keeping a velocity alive, for a bounded time.** A `Bridge` holds the record of the
last release (the action, the stated posture, the cycle of the action's percept and
the instant of the release) and the instant the action's velocity was last sent at.
A release gives a state that depends on no earlier state (`Bridge.release_state`).
The cycle of the next percept and the end of the hold are not stored: `Bridge.next`
and `Bridge.ends` are functions of the release record, so no state holds a next
cycle or an end that its release does not give, and `Bridge.next_covers` holds of
every state. The hold ends a declared number of cycles, the grace, after the
deadline of the next percept's action (`Bridge.ends_held`), so a next release that
meets its deadline is inside the hold (`Bridge.ends_covers`). `Bridge.tick` is one
reading of the clock between two releases: it sends the action's velocity again when
that velocity is not zero, the last send has reached the declared resend age and the
hold has not ended, and it changes nothing but the instant of the last send
(`Bridge.tick_keeps`). A zero velocity is not sent again, because the daemon's
expiry gives zero.

**A longer fault ends the held action on purpose.** The daemon's expiry is the
vendor's protection against a client that has stopped. A bridge that sent a velocity
again without end, for an agent that does not answer, would remove it, and a robot
that walks on while its agent hangs is the worse failure. So the hold is bounded,
and the deadline rule says what this world then does. The world declares a default,
the action that stands still (`Declared.rest`, `rest_declared`), and the force of a
bridge's state is its action with the end of the hold as its lapse (`Bridge.force`).
During a fault the action in force is the preceding action up to the end of its
hold, and the default from it (`Bridge.fault_named`). With forward released at 0 for
cycle 0 and the next release at 2 s, the next percept is of cycle 1, its deadline is
400 ms and the hold ends at 800 ms: the fault names forward from 400 ms and
standing still from 800 ms.

The bound is a time under one hypothesis, that the release is not before the start
of its percept's cycle:
`(pace.boundary origin bridge.index).nanoseconds ≤ bridge.released.nanoseconds`.
The hold then ends no later than the release plus the action's declared duration,
the transit allowance and `1 + latency + grace` cycles (`Bridge.ends_bounded`):
810 ms after the release of a velocity with the declared numbers. The hypothesis is
what a host owes: the state takes the cycle of the percept as an argument and does
not check it against the instant of the release.

What the bridge sends and what the deadline rule names agree after a release:

- at every instant after the instant of a release and before the end of its hold,
  the outcome of the step names the released action (`Bridge.release_named`), whose
  velocity is the first command of the release;
- over any list of readings, in any order, every command sent is the velocity of the
  action that the standing after the release names at that reading, and that
  velocity is not zero (`Bridge.ticks_named`, `Bridge.ticks_sent`);
- from the end of the hold that standing names the default and a tick sends nothing
  (`Bridge.tick_lapsed`);
- inside the hold, after a tick, the last send of a velocity that is not zero is
  younger than the resend age, and until the next reading it stays younger than the
  resend age plus the gap to that reading (`Bridge.tick_fresh`,
  `Bridge.release_fresh`, `Bridge.Fresh.age`).

At the instant of a release itself the two differ: the deadline rule counts an
action as in force after the instant it is released at, so the outcome still names
the preceding action there, and the bridge has sent the new velocity.

The force names what the bridge keeps in force and not what the body does. The last
send of a velocity can be just before the end of the hold. Under the assumptions
below the daemon receives it at most the transit allowance later and holds it for
its expiry, so it replaces the last velocity it received by zero less than the expiry
plus the transit allowance after the end of the hold: 510 ms with the declared
numbers.

The observed run saw more than the assumed expiry. The daemon checks the age of an
intent once per 20 ms control tick, so the replacement came 503 to 520 ms after the
last send, and the gait was back at standing 83 and 85 ms after the replacement. How
long the body moves after a lapse is UNKNOWN beyond those observations: it is a
property of the daemon's smoothing of a command and of the body, and no assumption
below states it.

The declared numbers are a resend age of 100 ms, a grace of two cycles and a transit
allowance of 10 ms, with an allowed gap of 50 ms between two readings of the clock.
The resend age, the gap and the transit sum to 160 ms, which is less than the
daemon's 500 ms (`keep_declared`). That these numbers keep a velocity in force rests
on assumptions that are proved nowhere:

- the daemon's expiry of 500 ms, and that it ages a velocity from its receipt;
- the receipt follows the reading of the clock a send is stamped with by at most the
  transit allowance;
- a reading of the clock at least every 50 ms, which needs a reader that runs while
  the agent's step computes. That is a property of an executing host loop, which is not
  built, and of the operating system's scheduling;
- that the posture a caller states is the body's. A wrong one sends the toggle the
  wrong way;
- that the declared duration of an action covers what the body takes for it.

**What became of an action.** `Action.outcome` gives one of five outcomes from the
stated posture, the daemon's answer and whether the body showed the action:
`refused`, `unanswered` (the answer was not complete), `unexecuted` (accepted, and the
body did not show it), `unchanged` (accepted and shown, for a posture the body had, so
no skill was sent) and `executed`. The answer has three states: pending, accepted and
refused. A refusal, a pending answer and a missing execution are read first, so an
action that asks for the stated posture still reports them. `Action.Judged` is the specification, in
propositions about the two facts and about the commands the release sent, and
`Action.outcome_judged` states that the function gives an outcome exactly when the
specification holds of it. An outcome says that the daemon accepted the action exactly
for an accepted answer (`Action.outcome_accepted`); that is its registered decision
kind, and the five-case statement is registered beside it. `Bridge.outcome` reads the
posture that the state holds from the release, so the commands and the outcome of
one release read one posture (`Bridge.release_outcome`). A late release is not an
outcome: it is the fault of [the deadline rule](#the-time-a-world-declares). How
sensing shows an action is a declared table of policy labels, under "What a host
holds" below.

**What the body senses.** The daemons publish the state of the body at 50 Hz and an
8 by 8 grid of depths at about 14 Hz, on one monotonic clock of their own, and a
measured quantity is the decimal text of a JSON number. The record of both streams
from the observed run is in
[a second comment of issue 95](https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6051119525).
A host keeps none of them as a float. A `Decimal` is a number as its text spells it:
a sign, the digits as one natural number and a power of ten, with an exponent of
any size. A `Scale` declares how a field is kept: a number of decimal places, a least
and a greatest value. `Decimal.fixed` converts by integer arithmetic.

**What the conversion computes** is stated over the rational value of the decimal,
in [the proof library](../lean/AcornVerif/Decimal.lean), with none of the
conversion's arithmetic. `value` is the digits times ten to the exponent, negated
for a minus sign. `Nearest x n` says that the integer `n` is within one half of `x`,
and that where it is exactly one half away `x` is the nearer to zero; at most one
integer is nearest (`Nearest.unique`). For every scale and every decimal, the result
is the integer nearest to the value times ten to the places of the scale, saturated
to the bounds of the scale (`fixed_nearest`). A height of 0.116 m is 116 in
thousandths, the residues `1e-323` and `7.38787616182396e-14`, which
[the record of the run's timing](https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6046235895)
quotes, are zero, and an angle beyond 32.767 rad is 32,767. The result is a
`Scale.Word`, whose type holds the proof of its bounds.

**How it computes** with powers of ten that the scale and the length of the digits
bound. Write the shift for the exponent plus the places of the scale. The conversion is the direct rounding
followed by the saturation for every decimal (`Decimal.fixed_clamp`), and it decides
two cases by comparing integers:

- with no digits, or with the width of the digits plus the shift negative, the
  rounded magnitude is zero (`Decimal.magnitude_vanishes`);
- with digits and a shift of at least the width of the scale, which is the width of
  its larger bound, the rounded magnitude is at least ten to that width
  (`Decimal.magnitude_beyond`) and so beyond both bounds (`Scale.width_bound`): the
  result is the least value for a minus sign and the greatest without one;
- between the two it divides, and forms two powers of ten: one that multiplies the
  digits and one that divides. With `w` the width of the scale and `d` the width of
  the digits, the exponent of the first is below `w` and the exponent of the second
  is at most `d` (`Decimal.shift_between`), so the largest powers are ten to the
  `w - 1` in the numerator and ten to the `d` in the denominator.

The width of a natural number is the count of its octal digits, and one for zero: one
more than a third of its binary logarithm, rounded down. A number is less than ten to
its width, and the width is read from the binary length of the number, so neither
comparison divides the digits by ten. Ten decimal digits are about eleven octal digits.

What the conversion forms is therefore bounded by the scale and by the length of the
digits, and not by the size of the exponent: `1e401` saturates and `1e-401` is zero
with no power of ten formed. For thousandths in sixteen bits `w` is 5, so `1e1`
forms ten to the 4 and `1000000000e-13` forms ten to the 10.

Two scales are declared. `Declared.milli` keeps thousandths and saturates at plus and
minus 32,767. `Declared.range` keeps whole millimetres from 0 to 32,767. Each fits
sixteen bits (`Declared.milli_sixteen`, `Declared.range_sixteen`).

A `State` is one frame of the state stream: the angle of each of the fifteen joints
and, when the daemon reports them, their rates; the direction of gravity and the
turning rate in the frame of the trunk; the height of the trunk by the daemon's
odometry; the label of what drove the tick; the daemon's reports of a fall; the
servo gain, which can be null; and the names of what limited the daemon's commands.
A `Depth` is one frame of the depth stream: 64 zones, each a distance in millimetres
and the sensor's status byte. A field whose absence means that nothing was measured
is an `Option`, and absence is not a zero. A `Reading` pairs a state frame with a
depth frame, if there is one, and states the age of that depth frame: the time from
it to the state frame (`Reading.age_exact`), and zero when the depth frame is not the
older (`Reading.age_ahead`). The two frames are stamped on the daemons' clock, a
`Stamp`. It is a type apart from the `Instant` of a host's clock, because a host that
reaches the daemons from another machine reads another clock.

The scales and the choice of fields are authored, and what a reading leaves out the
frame of the interface cannot carry.

**Reading a number of the daemon's text.** The repository's JSON reader keeps the
spelling of a number, and scans it into a `Numeral`, the parts of the spelling: a
minus sign, the digits before the point, the digits after it and an exponent part.
There is one scanner. The parser uses it, and `Value.numeral` scans a kept spelling
again with it, so reading a number adds no second reader. A numeral is formed
(`Numeral.Formed`) when it has the form of a number in the JSON standard (RFC 8259,
section 6): the digits before the point are a single zero or digits with no leading
zero, a point has at least one digit after it, and an exponent mark and its optional
sign have at least one digit after them. Every scanned numeral is formed
(`Numeral.scan_formed`), the spelling of a formed numeral scans to that numeral
(`Numeral.scan_chars`), and a value has a numeral exactly when it is a number with
the spelling of that numeral (`Value.numeral_iff`). `Decimal.read` gives the decimal
of a JSON value: the sign, the digits before and after the point as one natural
number, and the exponent lowered by the count of the digits after the point. It reads
exactly the numbers whose spelling is that of a formed numeral (`Decimal.read_iff`),
so `1.` and `1e` have no decimal and negative zero has one. The proof library states
the number that a numeral writes without the reader's arithmetic: a digit by a table
of the ten digits, a run of digits by the place of each, the whole part plus the
fraction, times ten to the exponent. The decimal of a formed numeral has that value
(`ofNumeral_value`), and so the integer kept for a JSON value that is read is the
nearest to the number as the daemon wrote it, in the units of the scale, at a tie the
one farther from zero, saturated to the bounds of the scale (`read_nearest`). No
theorem states that every number of a parsed text has a numeral: that rests on the
parser building a number in one place, from the spelling of a scanned numeral.

**Reading a frame of the daemon.** `State.read` and `Depth.read` read the parameters
object of a state notification and of a depth notification, as a parsed JSON value,
into a state frame and a depth frame. Each gives a frame or nothing, and a frame is
refused whole: one member that is not read gives no frame. What each reader accepts and
gives is a proposition for each field, which names the member the field is read from
(`State.Written`, `Depth.Written`), and a frame is read exactly when it is written so
(`State.read_iff`, `Depth.read_iff`). A number kept in a scale is the nearest integer
to the number as the text writes it, saturated (`kept_nearest`): that is the declared
rule for the real quantities, which are the joint angles and rates, the gravity
direction, the turning rates and the position of the odometry. Every quantity that the
daemon writes as an integer is read exactly and never repaired: a stamp, a status, the
gain, the stated numbers of rows and columns and the distance of a depth zone with a
valid return are natural numbers that digits alone spell, so `1.0` is refused there.
A distance is read by the status of its zone (`Depth.read_distances`). With the status
5, a valid return, it is at most 32,767, the width the daemon states for it without the
sign, and a frame with such a zone at a negative distance is refused whole. The
distance of a zone without a valid return is not kept, because no consumer reads it:
it must be an integer of the daemon's signed sixteen-bit type, from -32,768 to 32,767,
and the zone keeps 0. A frame with a fraction or a number outside that type as a
distance is refused whole, whatever the status. An array has exactly its declared length. A string
outside the ten policy labels is the policy `other`, by a table of labels that the
function of names is proved equal to (`Policy.named_iff`). The joint rates, the gain
and the list of limit names can be missing, and a missing member and a null member are
both read as nothing measured. The object that holds the list of limit names must be
an object. A depth frame must state eight rows and eight columns. A member that neither
reader names is not read. The names of the members and the
labels are those of the record of one observed run; no theorem relates them to what a
daemon sends. `Line.read` reads a whole parsed line by declared criteria, with one
constructor of its result for each case and one theorem for each constructor. The
criteria are taken from the JSON-RPC 2.0 specification and are not the whole of it: a
line that meets them need not be valid by that specification, since the parameters of
a notification can be any value and no further member is refused. A notification has
the version `2.0`, a string method and no identifier:
it is a state frame or a depth frame when its parameters write the frame, an unread
frame of that stream when they write none, and a notice for another method. A response
has no method and an identifier, and exactly one of a result and an error: a result
carries the boolean of its accepted member, and an error is an object with an integer
code and a string message, with an identifier that can be null. Every other value is
invalid, an error member that is null beside a result included (`Line.read_state`,
`Line.read_depth`, `Line.read_unread`, `Line.read_notice`, `Line.read_result`,
`Line.read_fault`, `Line.read_invalid`). What a host does at an unread frame is not
decided.

**What a host holds, and its transitions.** A host has two phases, and each is a type:
`Idle`, with no percept awaiting its action, and `Awaiting`, with one. Sensing takes an
idle host to an awaiting one and a release takes it back, so a second percept over an
awaited one and a release with nothing awaited cannot be written. Each type carries a
proof that its state is reached from the start by the transitions (`Reached`, one
constructor for each transition), so every value has a derivation and what holds of
every derivation holds of every value.

- Hearing a line keeps the latest state frame and the two latest depth frames. A
  release holds the identifiers of its requests that are not answered, and a result or
  a fault counts only for the release that holds its identifier (`Sent.answer_iff`).
  The answer of a release has three states: refused when one of its requests was
  refused, pending while one of its commands is not answered, accepted when all were
  accepted (`Sent.reply_iff`). So an outcome that says the daemon accepted an action is
  given only then, and a release that is still pending at the next percept reads
  `unanswered`. The action is held as shown exactly when a state frame named a policy
  that a declared table gives for it (`Idle.hear_shown`): the walking network for the
  velocities that move, the standing network or the sitting label for standing still,
  the label of each skill and of each posture. That evidence is weak: the forward
  velocity and the turns share one label, a frame from before a command took effect can
  show the action, and the next percept can be sensed before the label changes. How
  often it is wrong, in either direction, is UNKNOWN until the simulator runs.
- A state frame is paired with a depth frame only when the depth frame is stamped at or
  before it: the later of the two latest depth frames that is, chosen when the host
  senses. With none, the reading has no depth, which the frame of the interface marks as
  absent. So the age of a depth frame is the exact difference of two stamps
  (`Idle.sense_age`). The frames held are functions of each stream alone, so the reading
  does not depend on how the two streams interleave (`Idle.heard_frames`); the bound of
  this is the cache of two depth frames.
- Sensing gives a percept only in a cycle that is not before the one the last release
  allows, and from a state frame heard since that release, which it uses up
  (`Idle.sense_iff`). The frame was heard after the release; it can have been made
  before it. The percept is built by the adapter, with the latch of the goal that the
  host holds: the latch of every reachable host is the fold of the adapter's `arm` over
  the readings it sensed (`Reached.latch`), so after a near reading no percept is the
  event of the goal until a clear one (`Idle.sense_held`).
- A release names the cycle it answers and is admitted exactly when that is the awaited
  one and has started (`Awaiting.release_iff`). The identifiers given are consecutive
  from those of the opening requests, the counter is the next one, and each transition
  raises it by the count it gives (`Reached.counter`, `counter_rises`). So each command
  gets an identifier at or above the counter before the release, given on no earlier
  step and held by no earlier release (`Awaiting.release_fresh`).
- No standing is stored. The standing of an idle host at an instant is the one of its
  last step, so the verdict of the host that a release returns is the deadline rule's
  at every instant: a fault from the deadline to the release, the instant of the
  release included, and during it the action of the release before, up to the end of
  its hold (`Awaiting.release_standing`, `Awaiting.release_fault`, `Calm.fault_named`).
- A reading of the clock, in either phase, sends the velocity again when the bridge says
  so, with a new identifier, and changes nothing that the deadline rule reads
  (`Idle.tick_keeps`, `Awaiting.tick_keeps`). While a percept awaits, what it sends is
  the velocity of the action that the deadline rule names in force, up to the end of its
  hold, and nothing from then (`Awaiting.tick_named`).

**The loop's core.** `Acorn.Host.Microduck.Loop` composes these transitions with the
agent's two step parts, with no effect: a driver hands it events (a line heard, a tick of
the clock, a finished choice, a finished learning), each with a reading of the clock, and
each step returns the next state and the lines to send. A stage is `ready`, `choosing` or
`learning`, and `choosing` is the only stage that holds an awaiting host, so a percept
awaits exactly while the agent chooses and no percept is sensed while the agent chooses or
learns. A `Loop` holds a stage with a derivation from its start (`Ran`) for its stepper and
its starting agent, as the host's two phases hold theirs, so a task of a loop computes the
stepper's part on what the loop sensed and no other value exists (`Loop.agent`). The
instant of a step is the later of the reading and the instant of the last step
(`Loop.at_later`), so a loop's instants do not go back and are never before its host's
origin, and `Idle.sense` is the only test of sensing. The agent's parts are tasks that the
runtime spawns from a `Stepper`'s functions, once each, so the action released for a
percept is the stepper's choice on it (`Stage.step_sense`, `Loop.step_release`);
`Stepper.ofAgent` binds the agent under `actThenLearn`, whose two parts compose to
`Agent.actOrdered` (`Stepper.ofAgent_step`). The driver's trusted contract is to hand a
finished choice or a finished learning only once `IO.hasFinished` holds of its task, with
the reading of the clock taken after that: a step told early reads the task's value all the
same but records the earlier reading as the instant of the release, so its lateness and the
hold and cycle times that follow are not meaningful. This is observed against the
simulator, not proved: told early, 59 releases waited 550 to 758 ms for the choice, all
reached the daemon after their deadline and none was counted late (run `live-early`);
told after `IO.hasFinished`, 39 of 41 were counted late (run `live-slow`). A tick reaches the host's own tick in every
stage, so the velocity of the last release is sent again while the agent computes
(`Stage.step_tick`). After its opening requests the loop sends exactly the lines of the
commands that the host's tick and release return, on the control connection
(`Stage.step_sends`), each with an identifier of at least `opening`, so no answer to an
opening request is attributed to a command (`Stage.step_fresh`). A refused frame or an
invalid line is counted and changes nothing else (`Stage.react_refused`). The step of a
finished choice releases its action at every instant, since the release of the awaited
cycle is admitted from the last step on (`Loop.step_release`), and the counts hold one
percept for each percept sensed and a release for each but the one awaited (`Ran.counts`).
No driver calls the loop yet, and none of these reads a clock or a socket.

**The interface value and the frame.** `Acorn.Handcrafted.Microduck.interface` is
this world's instance of the interface: the 64 zones of a depth frame as its symbol
array, four signals after the agent's own reward question, ten actions, at most 48
words, prediction feedback channels from `0x50`, and the timing of a wall clock with
the declared pace (`interface_timing`). Its ten actions (`interface_actions`) are the
positions of the action table; `Action.index` and `Action.named` are inverse to each
other (`Action.named_index`, `Action.index_named`). The adapter that builds a frame
is authored, and it is a locus of three departures of the
[learned-only binding](learned-only-binding.md): the channels and symbols (D1), the
signals (D5) and the event of the goal (D8). It authors no subtask potential, so
every potential of a frame is false, and a profile whose subtasks are declared has
none that can hold in this world.

A frame has one word for each kept quantity of a reading: the angle of each joint
in steps of 0.1 rad, its rate in steps of 0.5 rad/s, the gravity direction in steps
of 0.1, the turning rate of the trunk in steps of 0.25 rad/s, the height of the
trunk in centimetres, the label of what drove the tick, the daemon's two reports of
a fall, the servo gain in steps of 8, the four limit names as bits, and the age of
the depth frame in steps of 20 ms up to half a second. Two more words are host
events: what became of the preceding action, and whether its release was late, which
is the fault of [the deadline rule](#the-time-a-world-declares). The coder hashes a
channel and a value into one feature and does not generalise between two values, so a
step is the resolution the agent has of a quantity. The steps are authored and no
experiment has qualified them. Each position of the layout carries at most one word
(`entries_distinct`), two positions have two channels (`channel_injective`), and no
word is on a prediction feedback channel (`channel_clear`). A refused action, an
accepted action that was not executed and an action whose answer was not complete are
three values of their word (`became_injective`).

Absence is a word and not a zero. The rates, the gain and the depth frame can be
missing; each has a presence word, which is one when the reading has the quantity
and zero when it does not (`entries_presence`), and a reading without the quantity
has no word on its positions (`entries_rates`, `entries_gain`, `entries_depth`). The
symbol of a depth zone with a valid return is one more than its distance in whole
decimetres, and the symbol of a zone with another status is `0x1000` plus the
status, so a symbol is below `0x1000` exactly for a valid return (`symbol_valid`).
With no depth frame every symbol is one value that no zone has (`symbols_missing`,
`symbol_present`).

**The goal is computed from the body's own sensing.** The body is near an obstacle
when its trunk is upright, its depth frame is under half a second old, and a zone
of the two top rows has a valid return under 300 mm. It is clear of obstacles when
the trunk is upright, the depth frame is as fresh, and every zone of the two top
rows has the status 255, which the simulator sends for nothing in range, or a valid
return of at least 400 mm. The trunk is upright when the gravity word of the frame
for the upward component, on position 33, is below the level of -0.95, which is 318
(`entries_gravity`). In thousandths that is an upward component below -967
(`upright_iff`): a level is a step of 0.1 counted from the least value of the scale,
so the levels do not separate -0.95 from -0.967, and a reading whose upward component
is from -967 to -951 thousandths is not upright. The depth frame is fresh exactly
when the age word of the frame is below its cap (`fresh_level`). So both tests are
functions of what the frame gives the agent: the gravity word, the age word and the
symbols of the two top rows (`near_symbols`, `clear_symbols`). No reading is both
(`near_clear`).

The goal has a latch, which a host holds between two percepts and which starts
disarmed. A near reading disarms it, a clear reading arms it, and any other reading
leaves it as it was (`arm_near`, `arm_clear`, `arm_keeps`). The event of the goal is
a near reading while the goal is armed (`achieved_iff`); the reward is one at that
event and zero otherwise. After a near reading no reading is the event until a clear
one, whatever lies between (`arm_held`): two events need a clear reading between
them. That is the whole guarantee. A reading is not clear while a zone of the two top
rows has a valid return under 400 mm or a status other than 5 and 255, while the
trunk is not upright, or while the depth frame is not fresh. So a return that wavers
between 300 mm and 400 mm gives no second event, and neither does a trunk that
wavers across the upright threshold in front of an obstacle. The record gives the
noise of a depth as 3 mm plus 20 mm for each 4 m of range, read in the vendor's
source and not observed. A reading whose top zones all have the status 255 is clear,
so the guarantee says nothing against a sensor whose status drops out: every top
zone at 255, then one valid return at 100 mm, then that zone at 255, then the return
again, is two events with no retreat. The four signals are nearness and the daemon's
report of a fall, each at the horizons 0.9 and 0.99.

A minimum over the whole grid would read the floor: the observed run saw the lower
rows return a bare floor at 0.41 to 3.35 m and the two top rows return nothing.
That a flat floor is not read as near is argued from the record's geometry and is
not machine-checked. The sensor is 0.082 m forward, 0.021 m to the left and 0.113 m
up from the origin of the trunk, pitched 14.2 degrees down and rolled 2.8 degrees at
rest; its field of view is 45 degrees over eight rows; and the origin of the trunk
is 0.116 m above the floor for a standing body and 0.061 m for a sitting one. On the
axis the lower edge of row 1 points 2.95 degrees below the horizontal, and the roll
adds at most 1.1 degrees at the side of the row, so no beam of the two top rows
points more than 4.1 degrees below the horizontal at rest. An upright trunk is
tilted by less than 14.8 degrees and a tilt lowers a beam by at most its own angle,
so no such beam points more than 18.9 degrees below the horizontal, and a flat floor
is returned at more than 3.08 times the height of the sensor. At that tilt, in the
least favourable direction, the sensor is at least 203 mm above the floor for a
standing body and 148 mm for a sitting one, so a flat floor is returned at more than
450 mm. The assumptions are a flat floor, a gravity word that is a unit direction,
the head at its rest pose, and a trunk whose origin stays at its standing or sitting
height while it tilts. Nearness has no converse: for a standing body with an upright
trunk and the head at rest, the lowest beam of the two top rows passes about 0.2 m
above the floor at 300 mm, so a lower obstacle is not near for such a body. A sitting
body's sensor is lower, at 0.174 m, and so are its beams.

UNKNOWN, because no run has measured them: how far the trunk tilts while the body
walks, and so how often the body counts as upright then; where the standing and
walking networks and each skill hold the head, which they drive; the height of the
trunk during a skill; which status a robot's sensor sends for a usable return and
for nothing in range; what the two top rows return on a slope, a step or a soft
floor; whether the status of a zone drops out at close range, so that a body at rest
could collect events ([issue #95](https://github.com/rbeauchamp/acorn/issues/95)
records the measurement and what it decides); and how often the event occurs for a
body that does not approach anything. A
body with no depth sensor is never near and never clear, so this goal gives it no
reward; a goal that needs no depth sensor is not built.

UNKNOWN, because the observed run did not exercise them: how long sitting down
takes (the run recorded the label of the sitting network and not the time the body
took to rest, so `sit` is declared with the duration of `stand`); what a velocity,
a kick, the roll or the pick does while the body sits; what a second toggle does
while a toggle runs; whether a velocity sent as a request behaves as one sent as a
notification at five to ten sends a second; and whether the table's magnitudes move
a robot, whose networks can differ. The record cites a vendor design note that says
an accepted command is queued and arbitrated by a fixed priority; that was read and
not exercised.

### The OaK picture and the executed agent

[Oak Lab's mission page](https://oaklab.ai/mission.html) draws the OaK
architecture as five boxes and seven edges. Experience is joined to state
features. State features define subproblems to attain features. Subproblems
define options and values that solve them and the main problem. Options and
values define models of options. Planning runs from the models to the options and
values. Options and values use features, and so do models.

[The signature](../lean/AcornVerif/Oak.lean) states that picture as a type over
the interface (`Oak`). A box is a type, and an edge is a function, called an
**arrow**, whose arguments are what the picture lets it read. The planning arrow
takes models, options and values and a feature vector; no frame, reward or host
event is among its arguments. The picture draws options and values as one box,
so the signature has one type for both. Three things an agent needs are not
drawn, and the signature states how it reads each: the reward of a transition
is an argument of the two arrows that learn from it, an arrow chooses the
action, and the state that feature construction keeps is a type that only
perception reads and writes.

An **extra arrow** is a value that the options and values read from a percept
beside its features and its reward (`Oak.Extra`). Its field
`departure : Departure` is mandatory, so no extra arrow exists without a
registered departure. The departure is a declaration and is not checked against
what the arrow reads; review checks it against the code that produces the
value. `Oak.toAgent` composes the
arrows into an agent of the kernel, each once per percept: perceive, pose,
solve, model, plan, act. Such an agent reads a percept through what perception
returns for it, its reward and its extra arrows only (`Oak.step_congr`).

The signature does not bound what a feature vector carries. Perception reads the
whole percept and the type of a feature vector is free, so an instance can pass
any part of a percept on as a feature. That the features are features is a claim
of the instance, not of the signature.

A conformance statement has two forms. For an agent, `Oak.Conforms` says that
under a map of memories the composed arrows take the agent's action on every
percept and keep the image of its next memory; a conforming agent and the
composed arrows then take the same actions in every world
(`Oak.Conforms.actions`). Every agent conforms to the instance whose perception
holds its whole memory (`Oak.conforms_coarse`), so such a statement is as strong
as the types and arrows of its instance and no stronger. For one operation of an agent, `Oak.Realizes` says
that the operation reads the memory through one function, applies an arrow, and
writes the arrow's value into one view of the memory. Such an operation changes
nothing outside the view (`Oak.Realizes.restores`), leaves the arrow's value in
the view (`Oak.Realizes.writes`), and from two memories with the same input
leaves the same part in the view (`Oak.Realizes.reads`).

[The executed arrows](../lean/AcornVerif/CurrentOak.lean) and
[the accounting proofs](../lean/AcornVerif/CurrentAccounting.lean) state what the
executed definitions satisfy. Each theorem concerns the function the agent
executes.

The table uses these terms. The **coder** turns a frame's words and symbols into
features. The **local transition** is the rest of one decision: selection, the
learning of every learner and the choice of the action; the **local state** is
what it stores. The **higher-level controller** of [the learning
loop](#the-learning-loop) is called the meta-controller in the source, and its
action values over primitive control and the options are the **option values**.
A **free boundary** is a decision at which no option is executing and no
exploratory run is being served; the higher-level controller chooses there. The
**planning boundary** is the planning work done at a free boundary, and
**search control** is its choice of the stored feature vector to back up next.
The **lifetime observations** are the bounded record the agent keeps of its own
stream: reward totals, prediction records, option episode counts and attempt
totals. A profile without a hierarchy is the
`primitive` [research profile](#agent-configurations), which has no options. The
discounted criterion is one of the two [learning
objectives](#learning-objective).

| Property | What is proved | Theorems |
|---|---|---|
| Planning reads no percept | The executed planning boundary takes no frame, no reward word and no host event. Of the option table it is handed, it reads the models only: two tables with the same models give the same result, for every selection, planning state, feature vector, reward rate and exploration rate. The option values and the search-control state it returns read the planning state through the higher-level controller and the stored feature vectors only; the model caches, the last errors and the work count reach neither. | `planningBoundary_models`, `planningBoundary_values` |
| The boundary call is the planning arrow | `planArrow` is the executed boundary at the picture's type: from the option models, the option values and a feature vector to the option values. The executed call reads the local state through the option models, the planning view and two scalars, and after it the planning view is the arrow's value; two local states with the same input have the same planning view after it. The planning view is the option values, the stored feature vectors with the search-control position, the model caches, the last planning errors and a count of planning work. Of the two scalars, the reward rate is learned from earlier rewards and enters the backed-up target. The exploration rate of the higher-level controller's nominal policy completes the value function, and the profile's rate policy supplies it ([D6](learned-only-binding.md#d6--exploration-rate--step-9)): the declared constant in four research profiles and the authored schedule in `annealed`. | `planFree_realizes`, `planFree_planned`, `planFree_reads` |
| Planning writes the planning view only | Every planning boundary, whatever function it calls, leaves the rest of the local state as it was. The option policies, the option models, the primitive action values, the prediction learners and the representation are unchanged. | `planFree_writes`, `planFree_keeps` |
| The coder reads words and symbols | The features of a frame and the outputs of the generated units are functions of the bank, the frame's words, the stored prediction feedback and the frame's symbols. Two frames with the same words and symbols give the same features, whatever their signals, declared potentials and achievement events are. | `features_eq`, `units_eq`, `frame_congr` |
| The extra arrows are listed | The full decision reads a percept through the features and unit outputs of its frame, its reward word and three extra arrows only: on two percepts that agree in those it returns the same decision and next state. The arrows are the declared potentials (D2), the signal values of the prediction questions (D5) and the achievement event (D8). The local transition reads the frame through the first two only; the event is a separate argument. The potentials and the agent's reward question carry their departure in the executed values. | `act_extras`, `step_frame`, `extras`, `extras_departures`, `potentials_origin`, `signals_origin` |
| Where the stopping outcomes agree, the results agree | Inside the stopping decision the achievement event does one thing: it forces the ending with the reason `goal`. The theorems cover seven operations that take the event and consult a stopping decision: the settling and the off-policy learning of one option, the off-policy learning of all options, the value an interrupted option's span closes toward, and the dispatch of the higher-level controller's choice. For each of the seven, on every input: where the outcomes of the stopping decisions it consults agree under two events, its results agree. Selection (`TemporalControl.selectWithOperations`) also takes the event: it consults the executing option's stopping decision and hands the event to the free boundary (`TemporalControl.atBoundary`). No such theorem covers those two. The draw-first dispatch of `act-then-learn` (`TemporalControl.drawFirst`) takes the event in the same way, to consult the executing option's stopping decision, and no such theorem covers it either. The owed writes of that order (`TemporalControl.settle`) hand the event to the start of the selected option and read it nowhere else (`settle_unstarted`, `TemporalControl.settle_started`), and that start has the same statement as the seven: for one option and for the option table, where the outcome of the stored trajectory's stopping decision agrees under two events, the results agree (`startTemporal_event`, `startOption_event`). An outcome is a decision without its ending reason. The condition does not force the events equal, because at the duration cap every decision stops whatever the event is; so a theorem fails if its operation's result differs between a set and a clear event where the decisions stop under both. Where selection and two of those operations agree under two events, the local transition agrees. The completion of a decision reads the frame through its signal values only. A profile without a hierarchy does not read the event. | `decideOption_event`, `Skill.goal_ends`, `continuation_cap`, `settleFollowing_event`, `settleTemporal_event`, `followTemporal_event`, `followSlot_event`, `followOptions_event`, `takeoverValue_event`, `dispatchMeta_event`, `startTemporal_event`, `startOption_event`, `settle_unstarted`, `step_event`, `finish_signals`, `step_event_primitive` |
| Host accounting does not reach a learner: it writes observations only | Environment accounting, attempt accounting and censoring at process exit keep the composed storage of representation, learners and references, the primitive credit, the reward rate and the rate schedule, in every world interface. | `recordEnvironment_learners`, `recordAttempt_learners`, `censor_learners` |
| Host accounting does not reach a learner: no decision reads the observations | From two agent states that differ in their lifetime observations only, the full decision returns the same decision and states that again differ in those observations only, on every percept. So a host operation that writes those observations only changes neither the next decision nor the learners after it, and from two such states the executed agent takes the same action at every time in every world of the kernel. | `step_learners`, `act_learners`, `act_accounting`, `executed_actions` |

What these theorems do not establish:

- **That the executed agent conforms to the picture.** No instance of the
  signature is built for the executed agent. Four arrows are not separated from
  the composed step: the refresh of the ranked assignments (pose), the credit of
  the options, the higher-level controller and the primitive controller (solve),
  the option models (model) and selection (act). Of perception, the coder is
  separated; the prediction learners, whose outputs return as feedback words,
  and the tester are not.
- **That the executed step has the order of the signature.** `Oak.toAgent` runs
  each arrow once per percept: learn from the transition, plan, then act. At a
  free boundary the executed step of the default step order plans first, then
  draws an action, and credits the transition into the frame after the draw;
  under the discounted criterion it also credits an ending option before it
  plans. Under `plan-after-act` it draws first and plans after the action, and
  under `act-then-learn` it also credits after the action
  ([step order](#step-order)); neither is the signature's order. Either
  the step is changed to
  the signature's order as a declared mode, or the composition of the arrows
  takes the step's schedule as a parameter. That choice is open.
- **That feature construction reads the old perception and the percept only.**
  In `Oak.step` the next `Perception` is a function of those two. The executed
  tester reads more. At the end of every learning decision it computes each
  unit's utility from the outgoing weights of the unit's readers
  (`Lifecycle.score`): the primitive controller, the higher-level controller,
  the option policies, the option models and the prediction learners. That
  utility selects the unit to replace, so the next bank depends on the options,
  values and models. In an instance whose `Perception` type holds the bank, the
  next bank must be a function of that type and the percept, so that type must
  also hold what the tester reads of the options, values and models. An instance
  that keeps the bank in another type is not excluded. Either the signature gets
  an arrow by which feature construction reads the use of features by the other
  boxes, or the tester's read is declared as an arrow outside the picture
  (departure [D7](learned-only-binding.md#d7--feature-tester-schedule--step-2)).
  That second structural choice is open too.
- **That the option models read options only.** The picture's edge to the models
  leaves the box of options and values, and the signature lets the model arrow
  read both. The executed model's terminal target does read the current value
  function ([PAR-13](prior-art-review.md#par-13--option-expectation-models)).
- **That no operation reads the achievement event outside a stopping decision.**
  The event theorems are about results: where the stopping outcomes agree under
  two events, the results agree. They do not exclude every read of the event.
  Where a decision continues the event is clear, because a set event forces the
  ending; a read of the event there sees one value and changes no result, so it
  leaves every such theorem true. That the operations contain no such read is
  read from their definitions.
- **The achievement event through selection.** In a profile with a hierarchy,
  selection takes the executing option's stopping decision and hands the event
  to the free boundary, which hands it to the dispatch in a later state. No
  theorem states that chain, so no theorem here says where the composed step
  sends the event. The reason of an ending reaches no credit
  (`endTemporal_reason`, `closeOption_reason`): it goes into the end event of the
  returned decision, and from there into the lifetime observations and the
  stored last decision, as read from the completion of a decision.
- **The statement that closes both.** The exact open statement is the composed
  step written once with the stopping rule as a parameter and no event, equal to
  the executed step when the rule is the executed stopping decision at the
  frame's event. With no event to read, it excludes every read outside the
  stopping decisions, and it covers the chain through selection.
- **That planning runs on the feature vectors perception produced.** The planning
  arrow's inputs have the picture's types. That the boundary call receives the
  current frame's features and a stored earlier vector is the definition of the
  step, not a theorem about the signature.
- **A run of the host.** The accounting theorems concern one decision. No theorem
  composes them along a run.
- **Whether the composition learns.** That stays empirical.

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

### Step order

The core accepts `--step-order learn-then-act` (the default),
`--step-order plan-after-act` or `--step-order act-then-learn`, independently of
the research profile, criterion and planning selection. The order is part of the agent's construction: it selects
the [step](#the-two-parts-of-a-step) the agent runs and the loop the streaming
runner uses, together. The callbacks a host loop takes have the order as a type
index, and the state of an agent and the image of a checkpoint are types of
one construction (`AgentConstruction.callbacks`, `AgentConstruction.State`,
`AgentConstruction.Image`). A campaign takes the construction and derives the
callbacks itself (`AgentConstruction.runCampaign`). A save takes a state of a
construction and writes the order word of that construction, and a load admits
bytes only when the order word in their own header is the receiver's
(`CurrentCheckpoint.saved_header`, `Checkpoint.loadCandidate_header`,
`CurrentCheckpoint.saved_admitted_order`).

These types hold no proof of an order, because the learner state and the durable
image carry none. The order of a value is a fact about the code that made it, and
no proof inside the value can state it. The order is a type index: a state, an
image and a chosen value have the type of one construction, and a callback
record has its order as an index, so two values of different orders do not meet
by accident. No check stops a module of this project from making such a value. A
private constructor stops the constructor notation and the constructor name in
another module and does not stop a tactic; the constructors of the image and of
the callback record are public. The checkpoint file has a checksum word and is
not authenticated. An edit of its order word alone, to the word of another
order, is refused by the loader of every construction of the file's dimension:
the stored words of two orders differ in one byte, and the checksum separates
two byte strings that differ in one byte (`CurrentCheckpoint.relabeled_unloaded`,
`Rng.fnv_byte`). The same edit together with the checksum of the edited bytes is
admitted by the loader of the other order (`CurrentCheckpoint.relabeled_loaded`).
`CurrentCheckpoint.saved_admitted_order` is about bytes that a save of this
project wrote.

Theorems say what a value under another index gives. A state gives the agent's
step of that index's order on the same learner state
(`AgentConstruction.callbacks_act`), and a save that writes that index's word
(`CurrentCheckpoint.saved_header`). Two callback records with the same whole step
and the same host functions, at any two indices, give the same pure fold
(`CurrentRunner.complete_parts`), and a value that either loop returns agrees
with that fold in its run state, its outcome and its refusal. So a record that
is copied under another index returns those three values unchanged. The
resource counters that a loop also returns, which hold measured durations, and
the observer's effects are outside these statements. That the copy changes the
time of the world's transition is read from the two loops; it is argued and not
machine-checked. For a profile that has a resumable image, the durable data of
an image, put under a construction of another order, is the image that this
construction's loader returns for the first construction's payload with the
order word replaced (`CurrentCheckpoint.relabeled_payload`,
`CurrentCheckpoint.relabeled_admitted`, `CurrentCheckpoint.relabeled_loaded`).

Under `learn-then-act` the runner takes the world's
transition after both parts. Under `plan-after-act` and `act-then-learn` it takes
the transition between them (`StepOrder.Releases`), and the planning of a free
boundary follows the action. Under `act-then-learn` every write that reads the
reward follows the action as well, and an option that starts draws its first
action before the credit that the same percept causes
([the two parts of a step](#the-two-parts-of-a-step)).

With `--planning none` the deferred planning writes no learner and no rate source
(`TemporalControl.planFree_none`). With expectation planning the meta draw of a
free dispatch reads a meta-controller that this frame's planning has not yet
changed, so `learn-then-act` and `plan-after-act` can give different actions,
learned state, outcome rows and checksums from the first free dispatch. `act-then-learn` can differ from
`plan-after-act` from the first option that starts, with either planning
selection. No recorded result or audit pin covers `plan-after-act` or
`act-then-learn`.

Two observations also differ under an order that releases: the reported agent duration
is the sum of the two parts, measured around the world's transition, and a step's
telemetry frame is delivered after that transition. When the world refuses an
action, the second part still runs and the frame is delivered before the loop
returns the refusal. A refusal ends the campaign and returns no agent in any
order, so no checkpoint follows it.

Startup diagnostics and the streaming campaign summary report the effective
`step-order=learn-then-act`, `step-order=plan-after-act` or
`step-order=act-then-learn` after the planning selection, and CSV output has it in a comment line of its own after the planning
comment. A checkpoint records the order in its header, and header admission
succeeds only for an image whose order is the order of the receiving run
(`admitHeader_order`). The decisions that admit an order each have an exact
two-way statement against a specification that calls no function the decision
executes, and each is a registered decision with a two-way kind
(`Decisions.step_order_parse`, `Decisions.step_order_value`,
`Decisions.step_order`, `Decisions.header_admit`). The parser and the value admission are stated against the spelling of
an order (`StepOrder.parse_spelled`, `StepOrder.parse_refused`,
`stepOrderValue_iff`). The command-line admission is stated on the argument list
alone (`stepOrder_iff`, `stepOrder_refused`), and the option reader it calls has
its own contract on that list (`Cli.value_absent`, `Cli.value_follows`,
`Cli.value_missing`). Header admission is stated on the stored words and the
returned typed values (`admitHeader_iff` against `HeaderAdmitted`, with
`StepOrder.tag_stored` for the order word). The ANSI view runs
both parts before each transition, reports `step-order=learn-then-act` and
refuses `--step-order`.

### Viewer support

The viewer's built-in launch accepts only `--research-profile ranked` and uses
the discounted criterion with expectation planning and the `learn-then-act` step
order. It does not accept the core's `--criterion`, `--planning` or `--step-order`
flags or the other four profiles. Use the terminal
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
| `--step-order` | `learn-then-act` (default), `plan-after-act` or `act-then-learn`; selects the [step order](#step-order) of the agent and its host loop. |
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
# step-order=<learn-then-act, plan-after-act or act-then-learn>
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

The two comments after the header name the planning selection and the step
order. The last line is a
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
- [PAR-19](prior-art-review.md#par-19--planning-after-the-action): Planning after the action, [Acorn.Timing](../lean/Acorn/Timing.lean) and [Acorn.Handcrafted.StepParts](../lean/Acorn/Handcrafted/StepParts.lean).
- [PAR-20](prior-art-review.md#par-20--acting-before-learning): Acting before learning, [Acorn.Handcrafted.DrawFirst](../lean/Acorn/Handcrafted/DrawFirst.lean) over [Acorn.Options](../lean/Acorn/Options.lean) and [Acorn.Temporal](../lean/Acorn/Temporal.lean).

## Boundaries

Types constrain stored words and receiver-bound state. Restored and functionally
updated values must satisfy the same admission as initial construction. Learned
code cannot import host/handcrafted owners except at explicit composition roots.
A provenance witness declares an origin; review must assess whether it is honest.
The viewer receives telemetry and requests lifecycle stop only.
[Acorn.Decisions](../lean/Acorn/Decisions.lean) registers the admissions, parsers
and validity tests of the executing library for which a property of the accepted
or refused result is proved, with what each proof establishes; the
[Regula audit](verification.md#regula-audit) requires a contract of every
registered function whose result type is not `Decidable`. The module
documentation of that registry lists the groups of definitions with a `Bool`,
`Option`, `Except` or `Decidable` result that carry no contract; no check keeps
that list complete.

Core calls select an explicit research profile. The [prior-art register](prior-art-review.md#current-default-qualification)
records qualification decisions. Each proof states its hypotheses, including
conditions on policies, value projection and models. See the source comments,
[learned-only binding](learned-only-binding.md) and [verification](verification.md).
