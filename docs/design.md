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

Operation in real time needs three more parts, and none is built:

- the timing discipline of a world, with a world on a wall clock and a missed
  deadline as a protocol fault;
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
most 381 words and feedback channels from `0x50`. Its adapter builds each percept
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
[goal proofs](../lean/AcornVerif/CurrentGoals.lean),
[curriculum proofs](../lean/AcornVerif/CurrentCurriculum.lean) and
[spawn proofs](../lean/AcornVerif/CurrentSpawn.lean).

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

Theorems say what a value under the other index gives. A state gives the agent's
step of that index's order on the same learner state
(`AgentConstruction.callbacks_act`), and a save that writes that index's word
(`CurrentCheckpoint.saved_header`). Two callback records with the same whole step
and the same host functions, at any two indices, give the same pure fold
(`CurrentRunner.complete_parts`), and a value that either loop returns agrees
with that fold in its run state, its outcome and its refusal. So a record that
is copied under the other index returns those three values unchanged. The
resource counters that a loop also returns, which hold measured durations, and
the observer's effects are outside these statements. That the copy changes the
time of the world's transition is read from the two loops; it is argued and not
machine-checked. For a profile that has a resumable image, the durable data of
an image, put under a construction of the other order, is the image that this
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
