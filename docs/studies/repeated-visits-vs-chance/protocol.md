# Improvement over repeated visits against a uniform-random policy: protocol

This is the protocol of study `repeated-visits-vs-chance`, the observation that
[U7](../../baseline-assessment.md#conformance-sequence) of the baseline
assessment asks for ([#61](https://github.com/rbeauchamp/acorn/issues/61)).
It fixes every choice below before any outcome exists.

**Protocol revision 1. Status when written: not authorized, not run.** This
file does not follow later status, because a registered revision is not edited
([revisions](#revisions)); the baseline assessment's U7 row records the current
status. Writing this protocol does not authorize execution. The
[scientific evidence guidance](../../../CONTRIBUTING.md#scientific-evidence)
requires the owner's explicit authorization before the first run.

Study [first-pass-vs-chance](../first-pass-vs-chance/results.md) observed one
pass of the curriculum. In one pass neither arm has met an installed goal
before, so that study compared two policies that know nothing of the goal. This
study observes what it could not: whether the agent does better at a goal on
later visits than on earlier ones.

## Question

Over repeated visits to the same two targets, do the `ranked` agent's attempts
to reach them get shorter, and by more than those of a policy that chooses
every action uniformly at random, when each follows the same campaign from the
same initial world?

Terms used below:

- A **seed** is the 64-bit number given to `--seed`. It fixes the generated
  world, the two reach targets and every pseudo-random stream of the world, the
  agent and the comparator.
- The **standard curriculum** is the 13 goals of `rawStandardCurriculum`, in
  order, numbered from 0: survive 200 steps, collect 2 wood, collect 2 stone,
  reach a near target, collect 4 wood, craft an axe, collect 3 food, reach a far
  target, collect 2 gold, craft a boat, collect 8 wood, survive 800 steps,
  collect 4 gold.
- An **attempt** installs one goal and runs until the goal is satisfied or a
  step cap is reached. A **cycle** is one attempt at each goal in order. A
  **campaign** is four cycles, numbered from 0. The world is not reset between
  attempts or cycles: position, inventory and energy carry on.
- A **visit** to a goal is the attempt at it in one cycle. Each arm visits each
  goal four times.
- The **steps** of an attempt are the actions it executed: the steps to
  achievement when the goal was achieved, otherwise the cap.
- The **reach goals** are goals 3 and 7. A reach goal is satisfied when the body
  is within three tiles of its target on both axes.

## What derivation settles

Claim labels follow the
[baseline assessment](../../baseline-assessment.md): machine-checked, argued,
assumed and UNKNOWN. The theorems named here are in
[the runner proofs](../../../lean/AcornVerif/CurrentRunner.lean) unless another
owner is named, and concern the executed definitions of
[the comparator](../../../lean/Acorn/Host/Baseline.lean),
[the attempt](../../../lean/Acorn/Host/Attempt.lean) and
[the campaign](../../../lean/Acorn/Host/Campaign.lean).

1. **The comparator's action law.** *Machine-checked, under one assumption.*
   The comparator's action is `baselineAction`, a function of its stream and of
   nothing else: no world, observation, goal or result is among its arguments.
   `baseline_action_code` proves that the action's code is ⌊9w / 2⁶⁴⌋ for the
   stream's output word w, and `baseline_action_stream` that a draw consumes
   exactly one output. `action_word_interval` proves that the words selecting
   one code are exactly one interval, and `action_word_count` that the interval
   holds c words for wait and eat and c + 1 for the other seven actions, where
   c = 2 049 638 230 412 172 401 and 2⁶⁴ = 9c + 7 (`word_space`). Under a
   uniform output word (assumed), every action has probability within 2⁻⁶⁴ of
   1/9. Only the comparator's task outcomes need observing.
2. **The arms follow one campaign.** *By construction and machine-checked.*
   `runRandomBaseline` admits its plan with `CampaignPlan.admit` from the
   arguments the agent's runner admits its plan from, starts from
   `World.initial` of the same configuration, looks each goal up in the same
   curriculum and asks the agent's own boundary function, `atAttemptBoundary`,
   what follows each attempt. `boundary_single_attempt` proves that with one
   attempt per goal the next attempt does not depend on the outcome, so both
   arms make the same 52 attempts, at the same goals in the same order, whatever
   either achieves. `baseline_finishes` proves that the comparator's record of a
   bounded campaign is never cut short: it ends at the campaign's completing
   boundary or at an explicit world refusal.
3. **An attempt means the same thing in both arms.** *Machine-checked for the
   attempt transition; argued for the native loop.* `Corresponds` relates an
   agent attempt to a comparator attempt with the same world and step count
   whose completion flag is the agent's reason to stop early.
   `start_corresponds` proves that installing a goal in one world puts the arms
   in corresponding states, whatever result the agent carries in.
   `tick_corresponds` proves, for every agent callback, that when the agent's
   transition acts and the comparator draws the same action, the comparator
   takes that step and the states correspond again. `idle_corresponds` proves
   that when the agent's transition takes no action, neither does the
   comparator's. `outcome_corresponds` proves that corresponding attempts that
   have taken a step report the same steps, completion flag and position and
   carry the same world on; an admitted campaign's cap is at least one step. So
   the two arms' attempts are one function of the world and the action
   sequence: both stop at the first step whose successor satisfies the goal, or
   at the cap, and neither ends an attempt before its first step. The agent's
   side of these theorems is `Attempt.tick`. The native loop runs the same
   selection and commit (`DecisionInput.selectOwned_eq`,
   `SelectedStep.owned_commit`, machine-checked); that it calls them in this
   order is argued from `runAttemptSteps`. The arms differ in the policy and in
   the agent's learning. One refusal is on the agent's side only: the agent
   observes the world before each action and the comparator does not, so an
   observation the world refuses ends the agent's pass alone.
4. **What an earlier visit leaves behind.** *Argued from the definitions.*
   `Goal.observe` satisfies a collect goal when the inventory holds the
   requested count and a craft goal when the tool is owned, whenever they were
   acquired. The only writes that lower an inventory count are a craft, which
   subtracts wood and stone and refuses a tool already owned
   (`Inventory.craft`), and eating, which subtracts one food (`performAction`).
   No write clears a tool or lowers gold. So in either arm a craft goal or a
   gold goal achieved once is satisfied again at the first step of every later
   visit, and a wood, stone or food goal is satisfied at once whenever the
   stock is still there. The stock need not be there: an arm that eats its
   food, or crafts with the wood or stone a goal counted, can fail a goal it
   achieved before. So what is retained can raise an arm's count of goals
   achieved in a later cycle without anything being learned, by an amount that
   depends on what the arm kept; the count is not bound to rise. A reach goal
   reads the body's position and nothing else (`ReachRelation.between`), so no
   inventory satisfies it: the body has to be at the target.
5. **The two survive goals are independent of the policy.** *Argued from
   machine-checked lemmas.* `World.setGoal` sets the goal's origin to the
   current time. Each successful step advances the clock by one
   (`World.step_clock`), leaves the goal and its origin unchanged
   (`World.step_goal`) and reports completion from the successor state
   (`World.step_completion`). So in every cycle every action sequence satisfies
   goal 0 at its step 200 and goal 11 at its step 800, whenever no world step
   is refused.
6. **No task reward arrives before achievement.**
   `StepResult.reward_completion` (machine-checked) makes the reward 1 on the
   achieving step and 0 on every other, and the achieving reward is carried
   into the next attempt (`Attempt.start_carried`). What the agent brings to a
   visit is what it learned on every earlier attempt. On a first visit that
   includes no reward for the goal. On a later visit it includes the reward of
   each earlier visit that achieved the goal, and nothing for the goal if none
   did.
7. **A run is a function of its command and binary.** *Argued from the types;
   the compiled binary, the Lean runtime and the operating system are trusted
   boundaries.* The comparator is a pure function of the world configuration,
   the seed and the campaign arguments (`runRandomBaseline`), and it runs after
   the agent's campaign has returned, in its own copy of the initial world. The
   agent's step (`AgentCallbacks`) and the world's step (`World.step`) are pure
   functions. Observers receive values and return nothing to the agent. Clock
   readings reach only telemetry, the printed campaign summary and the CSV
   footer.
8. **Work.** *Argued from items 2 and 5.* Each arm makes 52 attempts and takes
   at most 4 × (11 × 3000 + 200 + 800) = 136 000 steps per seed.
9. **Equal blocks cancel a constant advantage.** *Argued.* The
   [estimand](#estimand-margin-and-claims) compares each arm's first two visits
   with its last two, the same number of attempts on each side. Exchanging the
   two blocks in both arms negates each arm's improvement and D, which turns
   every win into a loss and every loss into a win. So if the joint
   distribution, over seeds, of the two arms' visit steps is unchanged by that
   exchange, wins are exactly as frequent as losses, and since no seed is
   both, q is at most 1/2. A policy that is better or worse than chance by the
   same amount on every visit therefore cannot produce the claim. This does
   not say either arm is in fact unchanged by the exchange; item 4 and
   [the limits](#what-a-result-will-and-will-not-establish) name what else
   changes between visits.

**UNKNOWN: the frequency with which the agent's reach attempts shorten by more
than the comparator's.** For one seed the outcome is a fixed computation, but
the only known way to evaluate it is to execute it: up to 136 000 updates of
about three million learned parameters in binary32 arithmetic, each depending
on the states the agent's own earlier choices reached in a generated terrain.
The definitions bound an attempt's steps by its cap and no more: no
established invariant determines whether or when an attempt achieves its goal,
so none settles how often a seed is a win. A kernel-checked evaluation would
re-execute the same stream at greater cost.
Over the population of 2⁶⁴ seeds the frequency cannot be enumerated. It is
estimated from a random sample of seeds.

## Design

| | Agent arm | Comparator arm |
|---|---|---|
| Policy | `ranked` research profile, discounted criterion, expectation planning | Uniform over the nine actions to within 2⁻⁶⁴ (item 1) |
| Learning | Fresh agent at the first step; learns on every step; nothing is frozen | None |
| Owner | The full agent, through `acorn-core demo` | `runRandomBaseline`, selected by `--baseline` |
| World | Side 1024, from the seed | A second copy of the same initial world |
| Stream | Four cycles of 13 goals, one attempt each, cap 3000 steps | The same (items 2 and 3) |

One process per seed runs the agent's campaign and then the comparator's.

**Why these values.** The side and the cap are the core's defaults
([core arguments](../../../lean/Acorn/Host/Cli.lean)) and the values of study
first-pass-vs-chance. One attempt per goal makes a visit one attempt and makes
the schedule independent of the outcomes (item 2). Four cycles is the smallest
campaign that gives each block of the comparison two visits to each reach goal,
so that no block rests on a single attempt. None of these values was chosen
with an outcome of this study in view, and none exists.

**Outcomes that carry information across cycles.** By item 4 an arm's count of
goals achieved can rise from cycle to cycle on what it retained alone, and by
item 5 the survive goals carry no information. A count of goals achieved
therefore does not separate learning from keeping. The primary outcome is the
steps of the eight visits to
the two reach goals, which only the body's position can end early. The food
goal's steps are reported but carry no decision: the outcome record holds no
inventory, so it cannot separate food collected during a visit from food
carried into it, and an arm that eats less keeps more.

**Horizon: four cycles, at most 136 000 steps.** A checkpointed resume is not
used to give the agent more experience first. A restore starts the option
models and the off-policy questions afresh and restarts the world
([checkpoint admission](../../verification.md#checkpoint-admission)), so it
would evaluate a different composition.

**Initialization.** Each run constructs the agent with
`AgentConstruction.standard` from the seed, loads no checkpoint and starts the
world at `World.initial`.

**Population, sample and prior access.** The population is the 2⁶⁴ seeds. The
sample is the 20 seeds of [seeds.txt](seeds.txt), drawn once, in the order
listed, with

```sh
od -An -N160 -v -tu8 /dev/urandom
```

when this revision was written. No seed was discarded or redrawn, and none is a
seed of study first-pass-vs-chance. No outcome of any run at these seeds was
observed. The results of study first-pass-vs-chance at its own 20 seeds were
known when this protocol was written; they concern one pass and other seeds,
and no value here was fitted to them. The draw itself cannot be audited
afterwards; that is an attestation, not a proof. There is no development set,
selection step or held-out set, because nothing is tuned.

One smoke run was made in preparing this protocol, to check that the run
command parses and to check the extraction commands against the core's own
output: seed 1, which is not in the list, a world of side 64, a cap of 5 steps
and four cycles, 260 agent steps in all. Its output was discarded and it is not
part of the record.

## Estimand, margin and claims

For an arm and a seed, let s(c, g) be the steps of the visit to goal g in cycle
c. The arm's **early cost** is E = s(0, 3) + s(0, 7) + s(1, 3) + s(1, 7), its
**late cost** is T = s(2, 3) + s(2, 7) + s(3, 3) + s(3, 7), and its
**improvement** is I = E − T: how many fewer steps its last four reach attempts
took than its first four. Each cost is an integer from 4 to 12 000.

For a seed, let A be the agent's improvement, an integer from −11 996 to
11 996, and D be A minus the comparator's improvement, an integer from −23 992
to 23 992. A seed is a **win** when A ≥ 1200 and D ≥ 1200: the agent's reach
attempts shortened by at least the margin, and by at least the margin more than
the comparator's. It is a **loss** when A ≤ −1200 and D ≤ −1200, and a **tie**
otherwise. A seed on which the world refuses either campaign is not a win.

- **Estimand.** q, the fraction of the 2⁶⁴ seeds that are wins.
- **Meaningful margin.** 1200 steps: 300 steps for each of the four late reach
  attempts, one tenth of an attempt's cap. A seed counts toward the claim only
  when the agent's reach attempts shorten, between its first two visits and its
  last two, by at least 300 steps per attempt, and by at least 300 steps per
  attempt more than the comparator's. When the comparator's costs do not
  change, one further late attempt that reaches its target within 1800 steps
  is enough; a difference of a few steps is not. The value is a judgment of
  what is worth calling improvement, fixed here before any outcome.
- **Claim.** q > 1/2: in most worlds the agent's reach attempts shorten over
  repeated visits by at least the margin, and by at least the margin more than
  chance's do.

Both conditions are needed. The agent's improvement must exceed the
comparator's, because a world that persists changes for a policy that learns
nothing: the body starts each later visit from where the previous cycle left
it, and a boat, once crafted, opens water (item 4). The comparator meets the
same mechanisms in its own copy of the world. The agent's improvement must
also exceed zero by the margin, because D alone can be large while the agent
gets worse: an agent whose late cost is 1200 steps above its early cost,
beside a comparator whose late cost is 2400 above, has D = 1200 and has not
learned to reach anything.

The mean of D is reported but carries no decision. D is bounded only by
±23 992, so an interval for its mean that is valid at every sample size is far
wider than one for q, and an interval with approximate coverage, such as a
bootstrap, would rest on an unverified large-sample argument.

## Uncertainty method

Let V be the number of wins among the 20 seeds, W the number of seeds whose
valid outcome is a win, and M the number of seeds with no valid outcome
([failed runs](#stopping-rule-exclusions-and-failed-runs)). A valid outcome
shows whether its seed is a win and a missing one does not, so W ≤ V ≤ W + M,
and V = W when no seed is missing.

**Sampling law.** By item 7, whether a seed is a win is a fixed property of the
seed. The 20 seeds are independent uniform draws from the population (assumed of
the operating system's entropy source), so V has the binomial distribution with
20 trials and probability q. This needs no assumption about the generator that
turns a seed into a world, and no independence between worlds.

**Interval.** For a count w, the exact binomial interval is the set of values
of q that neither one-sided exact binomial test rejects at 0.025: its lower end
is the largest q with P(Bin(20, q) ≥ w) ≤ 0.025, or 0 when w = 0, and its upper
end the smallest q with P(Bin(20, q) ≤ w) ≤ 0.025, or 1 when w = 20. The
reported 95% interval for q takes its lower end at W and its upper end at
W + M. With no missing seed it is the exact binomial interval at W.

Coverage is at least 95% for every q and holds at this sample size.
P(Bin(20, q) ≥ w) increases with q, so the lower end at V exceeds the true q
only when V reaches the smallest w whose upper tail under the true q is at most
0.025, an event of probability at most 0.025; the upper end is symmetric.
Neither end falls as the count rises, because P(Bin(20, q) ≥ w) falls and
P(Bin(20, q) ≤ w) rises with w. So the lower end at W is at most the lower end
at V, and the upper end at W + M is at least the upper end at V: the reported
interval contains the exact binomial interval at V, whatever caused the missing
outcomes.

Reporting an interval and not a point estimate follows the uncertainty-aware
evaluation cited by the
[promotion standard](../../prior-art-review.md#default-promotion-and-demotion).
That source's bootstrap is not used.

| Count | Interval for q | Count | Interval for q | Count | Interval for q |
|---|---|---|---|---|---|
| 0 | 0.000 to 0.169 | 7 | 0.153 to 0.593 | 14 | 0.457 to 0.882 |
| 1 | 0.001 to 0.249 | 8 | 0.191 to 0.640 | 15 | 0.508 to 0.914 |
| 2 | 0.012 to 0.317 | 9 | 0.230 to 0.685 | 16 | 0.563 to 0.943 |
| 3 | 0.032 to 0.379 | 10 | 0.271 to 0.729 | 17 | 0.621 to 0.968 |
| 4 | 0.057 to 0.437 | 11 | 0.315 to 0.770 | 18 | 0.683 to 0.988 |
| 5 | 0.086 to 0.492 | 12 | 0.360 to 0.809 | 19 | 0.751 to 0.999 |
| 6 | 0.118 to 0.543 | 13 | 0.407 to 0.847 | 20 | 0.831 to 1.000 |

Lower ends are rounded down and upper ends up. The reported interval takes its
lower end from the row of W and its upper end from the row of W + M. The table
was computed for this protocol by exact rational arithmetic and bisection; it
equals the table of study first-pass-vs-chance, which has the same sample size.

## Decision rule

W and M are the counts defined under [uncertainty method](#uncertainty-method).

| Result | Condition | What is reported |
|---|---|---|
| **Accepted** | W ≥ 15 | In most worlds the agent's reach attempts shorten over repeated visits by at least 300 steps per attempt, and by at least 300 steps per attempt more than chance's do. |
| **Refuted** | W + M ≤ 5 | In most worlds they do not. |
| **Inconclusive** | otherwise | The sample does not settle whether q is above or below 1/2. |

The thresholds are exact: P(Bin(20, 1/2) ≥ 15) = 5425/262144 ≈ 0.0207, and
P(Bin(20, 1/2) ≥ 14) ≈ 0.0577 exceeds 0.025. The rule accepts with probability
at most 0.0207 when q ≤ 1/2 and refutes with probability at most 0.0207 when
q ≥ 1/2. A missing seed never counts as a win toward acceptance and always
counts as one against refutation, so both bounds hold whatever caused the
missing outcomes.

What the rule can detect, exactly, with no missing seed:

| True q | Accepted | Refuted | Inconclusive |
|---|---|---|---|
| 0.1 | 0.0000 | 0.9887 | 0.0113 |
| 0.2 | 0.0000 | 0.8042 | 0.1958 |
| 0.3 | 0.0000 | 0.4164 | 0.5836 |
| 0.5 | 0.0207 | 0.0207 | 0.9586 |
| 0.7 | 0.4164 | 0.0000 | 0.5836 |
| 0.8 | 0.8042 | 0.0000 | 0.1958 |
| 0.9 | 0.9887 | 0.0000 | 0.0113 |

**Why 20 seeds.** Twenty is the smallest sample for which this rule accepts with
probability at least 0.8 when q = 0.8 and refutes with probability at least 0.8
when q = 0.2; at every smaller sample that probability is below 0.76. The
value 0.8 is a planning choice, not an estimate of q. If q lies between about
0.3 and 0.7 the likely result is inconclusive.

**Negative and inconclusive results** are reported with the same prominence as
an accepted one: the result line, W, losses, ties, M and the interval, in the
baseline assessment's U7 row and in the issue. A refuted result is stated as
refuted at this horizon. It includes the case in which neither arm reaches a
target on any visit, where every A and every D is 0; the exploratory counts say
whether that happened. An inconclusive result is stated as inconclusive; it is
neither evidence of learning nor evidence against it. Outside this study's
scope, learning stays UNKNOWN.

No result changes the
[qualification register](../../prior-art-review.md#current-default-qualification).
Promotion needs the separate decision and fresh evidence the promotion standard
describes.

## Stopping rule, exclusions and failed runs

- **Fixed sample.** Twenty seeds, one run each; the only further run is the
  rerun allowed below. There is no interim analysis, no extension and no
  replacement seed. A further study uses a new protocol revision and new seeds,
  and its sample is not pooled with this one.
- **No exclusions.** No seed is removed for its outcome.
- **Missing.** A seed has a valid outcome when its last run exits with status 0
  and reports a complete outcome CSV: the core prints `csv written successfully`
  on standard output exactly when no CSV creation or write failed, and a CSV
  failure does not change its exit status. Every other seed has no valid
  outcome, including one killed at the per-run deadline and one whose
  comparator was refused, and counts in M.
- **Reruns.** A run interrupted from outside the executed definitions (a machine
  restart, an operator's kill, a full disk) is rerun once with the same command.
  A run that exits with status 0 without a complete outcome CSV was interrupted
  in this sense: the operating system refused a file operation. The interrupted
  record is first moved, unedited, to the directory named interrupted beside
  the seed directories, so both records are kept and the seed's own directory
  holds the rerun alone. By item 7 a rerun cannot select among outcomes. A run
  killed by the per-run deadline is not rerun, and a rerun is not rerun: a seed
  whose rerun gives no valid outcome is missing.
- **Deadline kills.** The record decides whether the deadline ended a run. A
  run counts as killed by the deadline when its standard error holds the line
  "time: command terminated abnormally" and the resource report's real time is
  at least 14 400 s. The same line with a shorter real time, or a record with
  no exit status, is an interruption from outside. The exit status does not
  separate the two, as revision 1 of study first-pass-vs-chance recorded for
  this host and this wrapper. A deadline kill cannot show less than 14 400 s,
  because the report's clock starts before the deadline's and stops after it.
- **Derived checks.** The record behind a valid outcome must agree with items
  2, 5 and 8: 52 outcome rows for the agent, the row numbered r from 0 holding
  goal r mod 13 and attempt 0; 52 comparator lines, the line numbered r holding
  cycle ⌊r / 13⌋, goal r mod 13 and attempt 0; achievement of goals 0 and 11 at
  200 and 800 steps in every cycle of both arms; and 52 attempts for each arm
  in the printed comparison. A violation means the executed binary is not the
  source this protocol analyses. The study stops, the violation is reported as
  a deviation and no decision is issued.

## Resource budget

The machine is the shared development host: an Apple M4 Pro with 14 cores (10
performance, 4 efficiency) and 24 GB of memory, running macOS 27.0.

| Quantity | Limit | Kind |
|---|---|---|
| Agent steps | At most 136 000 per run: 2 720 000 with no rerun | Derived (item 8) |
| Concurrent processes | 4; each run's loop is sequential and uses one core | Fixed |
| Per-run deadline | 14 400 s, enforced by SIGKILL | Hard limit |
| Runs | 20, and at most one rerun per seed: at most 40 | Fixed ([reruns](#stopping-rule-exclusions-and-failed-runs)) |
| CPU time | At most 80 core-hours with no rerun, at most 160 in all | Hard limit: runs of at most 14 400 s each |
| Wall time | At most 20 hours with no rerun | Hard limit: 20 runs on 4 workers. A rerun runs for at most 14 400 s |
| Expected CPU time | About 6 to 14 core-hours | Estimate, not a bound |
| Expected wall time | About 2 to 4 hours | Estimate, not a bound |
| Memory per process | UNKNOWN | Recorded per run |

The estimate rests on the resource observations of study first-pass-vs-chance,
protocol revision 1, runs first-pass-vs-chance/r1/seed-N, on this host: 47 to
62 agent steps per second per seed, 58.0 over all seeds or about 17 ms per
step, over passes of 10 008 to 34 000 steps, and 134 to 157 MiB of peak
memory. At 17 ms per step a campaign of 136 000 steps takes about 39 minutes,
and 20 of them about 13 core-hours; a campaign whose later cycles end goals at
their first step is shorter. Whether the step rate and the memory hold beyond
34 000 steps is UNKNOWN: no longer run has been observed, and neither can be
derived from the definitions, because both depend on the runtime's allocation
and on the learned state. The deadline allows the same 105 ms per step as that
study's and binds only above it. The comparator's campaign adds world steps
only. If four processes do not fit in memory, concurrency is lowered, which
changes no outcome (item 7) and raises the wall-time limit in proportion.

The runs invoke no Lake command. The host's shared build slot is needed only
for the verification and build that precede them; four processes leave six
performance cores to other work. Other load changes wall time and no outcome.

## Execution

Preconditions: the owner's authorization names this protocol revision and the
commit to run. That commit contains this revision unchanged, and its Lean
sources are those of the commit that registered the revision; the first block
below refuses to continue otherwise. It takes the registering commit to be the
one that first added this file, which is so because pull requests are
squash-merged and revision 1 reaches the main branch in one commit. It compares
this file, the seed list and the Lean sources with that commit. The checkout
must have full history: a shallow checkout ends at a commit that then appears
to have added every file, so the block refuses one. Running any other Lean
sources needs a new revision first.

The commands are for this host (macOS, GNU coreutils installed). Each block
below is a complete bash script, run by bash from the root of the checkout. The
run script exports a shell function, which zsh, this host's default shell, does
not do. The run script was executed once, for the smoke run named under
[design](#design), with its seed, side, cap and deadline changed. The
extraction and calculation commands were executed against that run's output and
against records assembled by hand from the output definitions. No script has
been executed at the study's parameters.

Build and record the run identity, from a clean, full-history checkout of the
authorized commit:

```bash
set -euo pipefail
study=docs/studies/repeated-visits-vs-chance
out="$study/observations/r1"
test -z "$(git status --porcelain)"
test "$(git rev-parse --is-shallow-repository)" = false
registered=$(git log --diff-filter=A --format=%H -- "$study/protocol.md" | tail -n 1)
git diff --quiet "$registered" HEAD -- lean "$study/protocol.md" "$study/seeds.txt"
./scripts/verify.sh
./scripts/lean.sh build acorn-viewer
mkdir -p "$out"
{
  git rev-parse HEAD
  printf '%s\n' "$registered"
  shasum -a 256 lean/.lake/build/bin/acorn-core "$study/protocol.md" "$study/seeds.txt"
  cat lean/lean-toolchain
  sw_vers
  sysctl -n machdep.cpu.brand_string hw.ncpu hw.memsize
  date -u +%Y-%m-%dT%H:%M:%SZ
} > "$out/identity.txt"
```

Run the 20 seeds, four at a time. The script refuses a seed that already has a
directory, so it never overwrites a record:

```bash
set -euo pipefail
study=docs/studies/repeated-visits-vs-chance
out="$study/observations/r1"
run_seed() {
  dir="$out/seed-$1"
  mkdir "$dir" || return 1
  status=0
  /usr/bin/time -l gtimeout --signal=KILL 14400s \
    lean/.lake/build/bin/acorn-core demo --research-profile ranked \
      --criterion discounted --planning expectation --seed "$1" --side 1024 \
      --steps 3000 --attempts 1 --goals 13 --cycles 4 --baseline \
      --csv "$dir/outcomes.csv" > "$dir/stdout.txt" 2> "$dir/stderr.txt" || status=$?
  printf '%s\n' "$status" > "$dir/exit-status.txt"
}
export -f run_seed
export out
xargs -P 4 -n 1 "$BASH" -c 'run_seed "$1"' bash < "$study/seeds.txt"
```

Rerun an interrupted seed, written N here, under the
[reruns rule](#stopping-rule-exclusions-and-failed-runs), once the run script
has ended. First move its record aside, unedited. This script refuses a seed
that already has an interrupted record, so no seed is rerun twice:

```bash
set -euo pipefail
out=docs/studies/repeated-visits-vs-chance/observations/r1
mkdir -p "$out/interrupted"
test ! -e "$out/interrupted/seed-N"
mv "$out/seed-N" "$out/interrupted/seed-N"
```

Then run the run script again. It refuses every seed that still has a
directory, reports each refusal and exits with a nonzero status. It runs the
seeds that have none: those moved aside, and any that an interruption left
unstarted.

Extract one line per seed, of eleven fields: the seed; the exit status; whether
the core reported a complete CSV; the derived check on the agent's rows, with
the agent's early and late costs; the derived check on the comparator's lines,
with the comparator's early and late costs; and the agent's and the
comparator's attempt counts as the core printed them:

```bash
set -euo pipefail
study=docs/studies/repeated-visits-vs-chance
out="$study/observations/r1"
for dir in "$out"/seed-*; do
  grep -Fqx 'csv written successfully' "$dir/stdout.txt" && csv=complete || csv=incomplete
  agent=$(awk -F, 'NR > 1 && !/^#/ { r = rows++
      if ($1 != r % 13 || $2 != 0) bad = 1
      if ($1 == 0 && !($4 == 200 && $5 == 1)) bad = 1
      if ($1 == 11 && !($4 == 800 && $5 == 1)) bad = 1
      if ($1 == 3 || $1 == 7) { if (r < 26) early += $4; else late += $4 } }
    END { print (rows == 52 && !bad ? "ok" : "violated"), early + 0, late + 0 }' \
    "$dir/outcomes.csv" 2> /dev/null) || agent="absent 0 0"
  comparator=$(awk '$1 == "#" && $2 == "baseline" { r = rows++
      split($3, c, "="); split($4, g, "="); split($5, a, "="); split($6, s, "="); split($7, d, "=")
      if (c[2] != int(r / 13) || g[2] != r % 13 || a[2] != 0) bad = 1
      if (g[2] == 0 && !(s[2] == 200 && d[2] == 1)) bad = 1
      if (g[2] == 11 && !(s[2] == 800 && d[2] == 1)) bad = 1
      if (g[2] == 3 || g[2] == 7) { if (r < 26) early += s[2]; else late += s[2] } }
    END { print (rows == 52 && !bad ? "ok" : "violated"), early + 0, late + 0 }' \
    "$dir/outcomes.csv" 2> /dev/null) || comparator="absent 0 0"
  printf '%s %s %s %s %s %s\n' "${dir##*seed-}" \
    "$(cat "$dir/exit-status.txt" 2> /dev/null || echo absent)" "$csv" "$agent" "$comparator" \
    "$(sed -n 's/^distinct goals achieved .* (agent used \([0-9]*\) attempts; random policy used \([0-9]*\))$/\1 \2/p' "$dir/stdout.txt")"
done > "$study/results-r1.txt"
```

A line whose status is not 0, or whose CSV is incomplete, is a missing seed.
Every other line is valid and must read check ok in its fourth and seventh
fields and 52 in its tenth and eleventh; anything else is a derived-check
violation. For a valid line, A is the fifth field minus the sixth, and D is A
less the eighth minus the ninth. W counts valid lines with A ≥ 1200 and
D ≥ 1200, and M counts the seeds of the list without a valid line:

```bash
awk '$2 == 0 && $3 == "complete" { a = $5 - $6; d = a - ($8 - $9)
    w += (a >= 1200 && d >= 1200); l += (a <= -1200 && d <= -1200); v++ }
  END { print "W", w + 0, "losses", l + 0, "ties", v - w - l, "M", 20 - v }' \
  docs/studies/repeated-visits-vs-chance/results-r1.txt
```

The [decision rule](#decision-rule) gives the result, and the interval table
gives the interval's lower end at W and its upper end at W + M.

## Records

- **Run identity.** Each run is `repeated-visits-vs-chance/r1/seed-N` for its
  seed N, and an interrupted run that was rerun is
  `repeated-visits-vs-chance/r1/interrupted/seed-N`. An empirical citation names
  the study, the revision, the run or runs and the comparison.
- **Original observations.** Each seed's directory holds the outcome CSV, the
  standard output, the standard error with the resource report, and the exit
  status, exactly as written. The CSV holds one row for each of the agent's
  attempts and one comment line for each of the comparator's
  ([outcome CSV](../../design.md#outcome-csv)). An interrupted run's directory
  holds whatever that run wrote. They are never edited. The extracted results
  file and any written summary are presentations, kept apart from them.
- **Source and environment.** The identity file records the commit run, the
  commit that registered the revision, the SHA-256 of the binary, of this
  protocol and of the seed list, the toolchain, the operating system, the
  processor and the start time.
- **Timing.** This revision reaches the main branch before the first run.
  GitHub's record of the merge is the independent time of registration; run
  start times come from the local clock, which nothing attests. A content hash
  shows that a file is unchanged, not when it was written.
- **Deviations.** Any departure from this protocol is recorded with the result,
  with its reason and its effect on the claim.

## Analysis

**Confirmatory.** One comparison, the decision rule above. There is no second
confirmatory test, so no multiplicity adjustment applies.

**Exploratory.** Reported as description, with no decision and no claim:

- the value of D for each seed with a valid outcome, its mean and range, each
  arm's early cost, late cost and improvement, and the counts of wins, losses
  and ties, with the exact binomial interval for the fraction of losses, its
  lower end at the count of losses and its upper end at that count plus M;
- the number of seeds on which the agent's improvement A is at least 1200, the
  number on which D is at least 1200 whatever A is, and the number on which the
  comparator's improvement is at least 1200, each with its exact binomial
  interval. Each is at most one half of the win condition and none is the
  claim;
- for each arm, each reach goal and each cycle, the number of seeds achieving
  the visit and the steps of each visit, and the same for the food goal, read
  with the caution under [design](#design);
- for each arm, each of the other goals and each cycle, the number of seeds
  achieving the visit, and how many of those at the attempt's first step: what
  each arm retained, as item 4 describes;
- the position columns at the end of each reach visit;
- the learner columns of the outcome CSV and the campaign summary's replacement
  and ranking counts;
- observed steps per second, wall time and peak memory, as observations of this
  host and not as performance claims. Peak memory is read from the resource
  report's "maximum resident set size" line, for a run that ended on its own;
  a run killed at the deadline has no memory observation, as revision 1 of
  study first-pass-vs-chance recorded for this wrapper.

## What a result will and will not establish

- **Adaptation.** The agent learns throughout the measured campaign. The steps
  describe a learner in its first 136 000 steps, not a trained policy held
  fixed.
- **Attribution.** The comparator is not an ablation of the agent: it has no
  features, no memory and no temporally extended exploration, and it is not the
  agent with learning switched off. A win shows the whole `ranked` composition
  shortening its reach attempts over visits, and by more than chance does.
  Learning is one cause of that. Another is anything that persists differently
  in the two worlds: the two arms end each cycle in different places and with
  different inventories, and an arm that owns a boat can cross water the other
  cannot. The comparator meets these mechanisms but not in the same amounts, so
  a win does not by itself exclude them, and it credits no single mechanism.
- **A refuted or inconclusive result** does not show that the agent cannot
  learn the reach goals. The agent is rewarded for a goal only when it achieves
  it (item 6), so an agent that never reaches a target on its early visits has
  received nothing to learn that goal from.
- **Scope.** The result concerns worlds of side 1024, the standard curriculum,
  four cycles with a 3000-step cap, the two reach goals, and the source at the
  authorized commit. A material change to the learning equations, features,
  reward or selection rules needs a new observation.
- **Lifetime cost.** Memory and latency over a lifetime longer than 136 000
  steps are outside this study.

## Revisions

A revision is this file and [seeds.txt](seeds.txt) as committed together. It is
registered when it reaches the main branch. From then until the run, any change
to either makes a new revision with a new number and a new observations
directory; its seeds are redrawn only if a run was made at the old ones. After
the run, the only edits are corrections that follow a renamed declaration or a
moved link. The identity file holds the hash of the
revision as run, and Git holds its text.
