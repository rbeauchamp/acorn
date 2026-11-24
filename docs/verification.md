<!-- Generated from site/AcornDocs/Verification.lean by ./scripts/verify.sh site write. Edit that source, not this file. -->

# Verification

This guide describes Acorn's compiler, proof and execution checks. Each theorem
states the property and assumptions it checks. For installation and a first run,
start with the [README](../README.md#start-with-the-live-viewer).

Run `./scripts/verify.sh` in the actual Git checkout after provisioning the pinned
Lean, Mathlib, FloatLib, lean-intent and Verso dependencies, a C compiler, OpenSSL 3, ShellCheck
and GNU coreutils.
Each run of the command has a hard 360-second deadline, which includes the
project compilation the run does and every ordinary check; from cold project
outputs that is the whole build. The [merge gate](#build-and-source-inventory)
splits the cold build over two runs, each with its own deadline. The deadline
uses process-group SIGKILL with no grace period or budget override; missing,
skipped or timed-out checks fail. OS scheduling and signal delivery are the
trusted mechanisms that enforce this deadline.

Project instruction changes have no live Acorn runtime surface. The complete
verification command remains required for documentation changes.

## Platform setup

In work on a change a launch needs the owner's authorization for that run;
[running a program](../CONTRIBUTING.md#running-a-program) says where the
invocations that may be driven without it are listed.
Use `./scripts/start.sh` for automatic setup and launch, or
`./scripts/start.sh --prepare-only` to prepare and build without learning.
It uses Homebrew on macOS and apt-get on Ubuntu/Debian. It installs missing
prerequisites, which changes the machine's package manager state, so an agent
runs it only where the person it works for has agreed to that, and it
provisions the pinned Lean, Mathlib, FloatLib and lean-intent dependencies;
repeat launches use the offline bootstrap when those dependencies are already
available. The bootstrap status that decides this admits the Lean package's
configuration, tracked sources and `.lake` containment (including
`lean/.lake/packages` and Lake's numeric package configuration cache directories
and files), writes only the launcher's own
override file and tracked-module stamp atomically through exclusive temporary
files (clearing only Acorn's confirmed cached configuration traces when tracked
Lean modules change) without building any Lean or C target, and asks Lake
whether the FloatLib modules the proof
bridge imports, the lean-intent modules that the intent bridge and the gate's
lean-intent checker `lean/AcornTools/Intent.lean` import, the native objects of the
lean-intent modules that checker links, and the Regula modules the decision
registries and the theorem inventory `lean/AcornTools/Theorems.lean` import with
the native objects the theorem inventory links are current.
The first setup may need network access, a package-manager password prompt or
the macOS command-line tools installation dialog. It never runs Acorn as root
and does not change the global Xcode selection or Lean default toolchain.

The [verification workflow](../.github/workflows/verify.yml) runs the
[merge gate](#build-and-source-inventory) when a pull request is opened or
reopened and at every push to it, and at no other time, on GitHub's standard
`ubuntu-24.04` x64 image. It installs no
system package: it admits by name the packages that image provides, and takes
elan from a release pinned by the SHA-256 of its archive. Every workflow step
that reaches the network before the gate has its own time limit, so a stalled
download fails that step. The workflow keeps no cache: each run provisions the
dependencies from their pinned sources. Automatic local setup supports macOS and
Ubuntu/Debian Linux.

For manual setup, which changes the machine's package manager state and so is
done by an agent only where the person it works for has agreed to it, install
macOS command-line tools and the packages below
([Homebrew installation](https://brew.sh/)):

```sh
brew install coreutils shellcheck openssl@3 elan
```

For Ubuntu, under the same condition, install:

```sh
sudo apt-get update
sudo apt-get install -y build-essential curl git libgmp-dev openssl shellcheck coreutils elan
```

Ensure Lean and Lake are available in your shell, then run
`(cd lean && lake exe cache get && lake build Mathlib regula/lint floatlibBridge regulaInterface leanIntentBridge leanIntentNative)` from the
repository root to provision the pinned toolchain/dependencies; the build compiles
only Mathlib modules absent from the upstream cache, plus Regula's lint driver.
FloatLib, lean-intent and Regula publish no cache, so the same command
compiles the FloatLib modules that the proof bridge imports, the lean-intent modules
that the intent bridge and the lean-intent checker import with the native objects
the checker links, and the Regula modules that the decision registries and the
theorem inventory import with the native objects the theorem inventory links.
The offline bootstrap asks Lake whether every artifact those imports need is
current and refuses to run until it is: verification never compiles a dependency
inside its deadline. Verification also builds the
[documentation site](#documentation-site): run
`(cd site && lake build verso/VersoManual verso/VersoManual:shared)` once to provision pinned Verso and its shared library, which
verification likewise requires to be built already. Do not use `lake update` to
resolve a missing dependency; that changes the selected versions.

Build with `./scripts/lean.sh build acorn-viewer`; Lake also builds its declared
core and checkpoint-helper dependencies. OpenSSL is required for build-time
source hashing. The launcher adds Homebrew's OpenSSL 3 to its own environment;
manual builds need a usable OpenSSL on PATH.

### Headless and advanced launch

In work on a change a launch needs the owner's authorization, with or without a
browser. `./scripts/start.sh --no-browser` prints the actual bound loopback URL.
`--run-dir DIR` selects another run directory and `--port N` selects a port;
the default port is allocated by the OS. Browser opening is optional and its
failure does not stop the agent. Use `./scripts/start.sh --help` for the launcher
options. `--help` and `--prepare-only` stop before the launch. Raw viewer options are documented in [the viewer specification](viewer-ux.md).

### Interrupted-launch recovery

The launcher keeps `.acorn-launch/` outside the run directory so that Clear
cannot remove its ownership lock. An ordinary exit removes the lock. A forced
termination or machine crash may leave it behind. A second launcher refuses
to displace an uncertain owner.

Read `.acorn-launch/pid` and inspect that process and its viewer/core descendants.
Only after confirming that no process still owns this run, remove the lock's
temporary files (control, pid and installer.sh) and the
empty `.acorn-launch/` directory; the launcher can then be run again with the
options it was first given. In work on a change, the conditions for running it
again are those of the first run, which
[running a program](../CONTRIBUTING.md#running-a-program) states. Preserve `acorn-run/`.
Do not manually launch another viewer against a directory already in use.

### Build and verification failures

If a tool is missing, install the named prerequisite before retrying, under the
condition on installing that [platform setup](#platform-setup) states. On macOS,
check that `xcode-select -p` points to an installed, usable developer toolchain.
If verification reaches its 360-second deadline, retain the failing command
and diagnostic for a focused report; do not raise the limit or treat a partial
run as a pass. Run the complete command to check all verification owners.

## Compiler and execution boundary

Every Git-tracked Lean source below `lean/` must be a regular file and a module
of the libraries Acorn, AcornVerif, NativeApp, AcornDocument or Entry, which
[the Lake configuration](../lean/lakefile.lean) assigns only from tracked
modules, or a listed tool module. The [Regula audit](#regula-audit) claims the
first four with Bootstrap; Entry holds the executables' roots. Every retained
native target is built and checked against Lake's evaluated targets and compiled
entry owners; each executable root must be a maintained module. Ownership
admission refuses a facet-qualified build key in the root package's Lake
configuration. The [Lake configuration](../lean/lakefile.lean) documents the
restriction and its pinned-Lake rationale. Before any Lake command, `Bootstrap.lean` must elaborate with no message,
reject `-f`/`--file`/`-d`/`--dir`/`--packages` overrides on build and query
(and as leading Lake options on exe and env, while preserving `-K`
configuration settings and executable or command arguments), and run Lake
explicitly against the tracked configuration (`-f lakefile.lean`, while
documentation site commands pass `-f lakefile.toml` directly) with `--wfail`, so any warning,
including a header-time warning such as a deprecated import, fails the build
(while `scripts/regula.sh` preserves Regula's default `lake build --wfail` and
`lake lint` invocation after verifying `lean/lakefile.lean` and refusing any
`lakefile.toml` shadow inside `lean/`). Source/compiled admission checks
imports, capability
owners, artifact origins and native routes. The Regula audit, not ordinary
verification, checks the axioms that each declaration of the claimed libraries
depends on. The theorem inventory counts the theorem declarations and refuses a
native replacement other than a verified compiler-generated constructor-index
pair. Every proof passes through the kernel.

The modules that compose the agent import no world. Source and compiled admission
refuse a declared module that imports a host module, or references a declaration
owned by one, unless it is one of a world's own declared modules. The grid world's are
Acorn.Handcrafted.Observation, Acorn.Handcrafted.Cumulants and Acorn.Handcrafted.GridWorld. The [Microduck](https://github.com/pollen-robotics/microduck)
world's is Acorn.Handcrafted.Microduck,
which binds that world to the interface; the host's sensing builds its percepts, which the
executable microduck-host runs, and no theorem states what it feeds a learner. The last of the grid world's modules binds the
grid world to the agent's interface.
`Acorn.Handcrafted.Agent.grid_inputs` states what that binding feeds each
learner, in terms of the host's own channel, signal and potential definitions, for
every agent state, observation and reward word:

```lean
theorem Acorn.Handcrafted.Agent.grid_inputs {profile : Acorn.Handcrafted.FeatureProfile}
  {config : Acorn.Features.Config} {criterion : Acorn.Features.Criterion}
  {dimension : Acorn.Dimension} {planning : Acorn.Features.PlanningSelection}
  (state :
    Acorn.Handcrafted.Agent Acorn.Handcrafted.Grid.interface profile config criterion dimension
      planning)
  (obs : Acorn.Host.Observation) (reward : Acorn.Binary32) (achieved : Bool) :
  Acorn.Handcrafted.Grid.percept profile.taskMode obs reward achieved =
      { frame := Acorn.Handcrafted.Grid.frame profile.taskMode obs achieved, reward := reward } ∧
    state.words (Acorn.Handcrafted.Grid.frame profile.taskMode obs achieved) =
        Acorn.Handcrafted.observationWords obs
          (Acorn.Handcrafted.feedbackPredictions state.control.runtime.references.demonPredictions)
          profile.taskMode ∧
      (Acorn.Handcrafted.Grid.frame profile.taskMode obs achieved).symbols =
          Acorn.Handcrafted.observationPatch obs profile.taskMode ∧
        Acorn.Handcrafted.signalValues (Acorn.Handcrafted.Grid.frame profile.taskMode obs achieved)
              reward =
            Acorn.Handcrafted.evaluateCumulants Acorn.Handcrafted.cumulantOrder obs reward ∧
          (Acorn.Handcrafted.Grid.frame profile.taskMode obs achieved).declared =
              Acorn.Handcrafted.spatialPotentials obs ∧
            (Acorn.Handcrafted.Grid.frame profile.taskMode obs achieved).achieved = achieved
```

`AcornVerif.GridCorrespondence` keeps the agent's composition over host
observations, as it was before the interface, as a frozen reference that no executing
module imports. `AcornVerif.GridCorrespondence.act_eq` states that the
interface agent's decision on the grid percept returns the same next state and
decision as that reference:

```lean
theorem AcornVerif.GridCorrespondence.act_eq {profile : Acorn.Handcrafted.FeatureProfile}
  {config : Acorn.Features.Config} {criterion : Acorn.Features.Criterion}
  {dimension : Acorn.Dimension} {planning : Acorn.Features.PlanningSelection}
  (state :
    Acorn.Handcrafted.Agent Acorn.Handcrafted.Grid.interface profile config criterion dimension
      planning)
  (obs : Acorn.Host.Observation) (reward : Acorn.Binary32) (goal : Bool) :
  AcornVerif.GridCorrespondence.Direct.act state obs reward goal =
    state.act (Acorn.Handcrafted.Grid.percept profile.taskMode obs reward goal)
```

`AcornVerif.GridCorrespondence.callback_eq` and
`AcornVerif.GridCorrespondence.initial_eq` state the same for the host's step and
construction. Restoration has no frozen reference, since restoration is exact
(`Acorn.Handcrafted.Agent.restore_exact`). The reference covers the composition; the
storage types beneath it are the executed ones at the grid's action count.

The executed step is two functions under a declared step order:
`Acorn.Handcrafted.Agent.choose` selects, and
`Acorn.Handcrafted.Chosen.learn` completes the step from the value the first
returned. `Acorn.Handcrafted.Agent.act_parts` states that under the default
order they compose to the executed step, for every agent state and percept, in every
world:

```lean
theorem Acorn.Handcrafted.Agent.act_parts {interface : Acorn.Features.Interface}
  {profile : Acorn.Handcrafted.FeatureProfile} {config : Acorn.Features.Config}
  {criterion : Acorn.Features.Criterion} {dimension : Acorn.Dimension}
  {planning : Acorn.Features.PlanningSelection}
  (state : Acorn.Handcrafted.Agent interface profile config criterion dimension planning)
  (percept : Acorn.Features.Percept interface) :
  state.act percept = state.actOrdered Acorn.StepOrder.learnThenAct percept
```

Under the order that plans after the action,
`Acorn.Handcrafted.TemporalControl.atBoundary_unplanned` states that the meta
draw of a free dispatch reads the meta-controller before that frame's planning,
and `Acorn.Handcrafted.Agent.actOrdered_undrawn` that a step whose decision
records no meta decision is the executed step under that order and the default one.
With no planning selected, `Acorn.Handcrafted.Agent.actOrdered_unplanned` states that
the two orders are one step: the same next agent and the same decision for every agent
state and percept. `AcornVerif.StepParts.loop_unplanned` states that they then have
one closed loop in every world that waits for the agent.

Under the order that acts before it learns, the first part makes every draw and takes
no reward word. `Acorn.Handcrafted.Agent.choose_reward` states that two percepts
with one frame give the same temporal state, decision and record of owed writes,
whatever their reward words. The frame carries the achievement event, which the first
part reads, so the statement does not make the action independent of that event.
`AcornVerif.DrawFirst.actThenLearn_planAfterAct` states that
this step is the step that plans after the action wherever the decision starts no
option and no option closes at a free dispatch under the discounted criterion:

```lean
theorem AcornVerif.DrawFirst.actThenLearn_planAfterAct {interface : Acorn.Features.Interface}
  {profile : Acorn.Handcrafted.FeatureProfile} {config : Acorn.Features.Config}
  {criterion : Acorn.Features.Criterion} {dimension : Acorn.Dimension}
  {planning : Acorn.Features.PlanningSelection}
  (state : Acorn.Handcrafted.Agent interface profile config criterion dimension planning)
  (percept : Acorn.Features.Percept interface)
  (unstarted : (state.choose Acorn.StepOrder.actThenLearn percept).decision.started = none)
  (uncrossed :
    criterion = Acorn.Features.Criterion.discounted →
      (state.choose Acorn.StepOrder.actThenLearn percept).decision.metaDecision.isSome = true →
        (state.choose Acorn.StepOrder.actThenLearn percept).decision.ended = none) :
  state.actOrdered Acorn.StepOrder.actThenLearn percept =
    state.actOrdered Acorn.StepOrder.planAfterAct percept
```

`AcornVerif.DrawFirst.drawBoundary_start` and
`AcornVerif.DrawFirst.dispatchMeta_start` state what the first action of an
option that starts reads in each case. The second also states that selection makes the
writes of the start with `Acorn.Handcrafted.TemporalControl.startOption`, and
`Acorn.Handcrafted.TemporalControl.settle_started` that the owed writes make them
with the same function. `AcornVerif.DrawFirst.drawBoundary_unplanned` states what
the meta draw of this order reads, and `AcornVerif.DrawFirst.drawFirst_assigns`
that the assignment refresh precedes its draws.
`AcornVerif.DrawFirst.selectWithOperations_form` and
`AcornVerif.DrawFirst.drawFirst_form` state, for every state, frame and reward word
and on every branch, that selection and the draw-first dispatch followed by its owed
writes are one specification, `AcornVerif.DrawFirst.dispatchForm`, in two modes.
That specification reads its mode in two places, so those are the places where the two
orders can differ. The first is the free dispatch, and
`AcornVerif.DrawFirst.boundaryForm_frozen` states that in a frozen profile it gives
one result in both modes, also when its meta draw starts an option. The other place is
an option that closes under the discounted criterion.

Under every order `Acorn.Handcrafted.Agent.choose_keeps` states that the first
part writes neither the primitive controller nor a prediction demon, and
`Acorn.Handcrafted.Chosen.learn_rng` that the second part draws nothing from the
action generator.

A host releases the action after both parts or between them.
`Acorn.Host.DecisionInput.chooseOwned_release` states that one pass of the host
protocol gives the same result either way, on acceptance and on a refusal.
`Acorn.Host.runAttempt_complete` states that every value either native loop of
an attempt returns agrees with one pure fold of whole steps,
`Acorn.Host.Attempt.complete`, in its run state and outcome, or in its refusal
with the learned stage of a refused pass (`Acorn.Host.AttemptAgrees`,
`Acorn.Host.Attempt.complete_learned`). The terminal frame and the resource
counters are outside the agreement:

```lean
theorem Acorn.Host.runAttempt_complete {order : Acorn.StepOrder} {config : Acorn.Host.WorldConfig}
  {α β : Type} {goal : Acorn.Host.Goal} {cap : UInt64}
  (callbacks : Acorn.Host.AgentCallbacks order α β) (observer : Acorn.Host.StreamObserver β)
  (context : Acorn.Host.GoalContext) (initial : Acorn.Host.Attempt config α goal cap)
  (resources : Acorn.Host.RunnerResources) (world after : Void IO.RealWorld)
  (value :
    Except (Acorn.Host.Refusal config α goal cap)
      (Acorn.Host.RunState config α × Acorn.Host.GoalOutcome × Acorn.Host.RunnerResources))
  (returned :
    Acorn.Host.runAttempt callbacks observer context initial resources world =
      EST.Out.ok value after) :
  Acorn.Host.AttemptAgrees (Acorn.Host.Attempt.complete callbacks context cap.toNat initial) value
```

A world declares its timing in its interface: it waits for each action, or it moves on
a wall clock with a declared cycle and a latency in cycles.
`Acorn.Handcrafted.Grid.interface_timing` states that the grid world declares that
it waits. For a wall-clock declaration, `Acorn.Pace.meets_index` states the verdict
on the instant an action is released at: the deadline is met exactly when the release
falls in a cycle before the one the deadline starts. `Acorn.Pace.outcome` gives, for
what a host holds, a world's default and an instant, the action in force and whether a
fault holds. `Acorn.Pace.step_fault` states that in one step a fault holds exactly
from the deadline to the release:

```lean
theorem Acorn.Pace.step_fault {α : Type} (pace : Acorn.Pace) (origin : Acorn.Instant) (rest : Option α)
  (prior : Acorn.Force α) (index : ℕ) (released : Acorn.Instant) (chosen : Acorn.Force α)
  (now : Acorn.Instant) :
  (pace.outcome origin rest (Acorn.Standing.during prior index released chosen now) now).fault =
      true ↔
    (pace.deadline origin index).nanoseconds ≤ now.nanoseconds ∧
      now.nanoseconds ≤ released.nanoseconds
```

`Acorn.Pace.step_holds` states that the preceding action is in force at every
instant of the fault at which it has not lapsed, which is every instant in a world whose
actions do not lapse, and `Acorn.Pace.step_lapsed` that from its lapse the fault has
the world's default. `Acorn.Pace.step_faultless` states that no instant has a fault
exactly when the release meets the deadline. An instant is a natural number of
nanoseconds, so this arithmetic is exact. The statements are about these functions. The
grid world declares no wall clock; the Microduck's world declares one, and its host keeps a
standing in its pure transitions.

The Microduck world has an action table and a bridge's state, as pure definitions, which the
host's transitions call. The type of the commands a bridge can send is closed: enable, one of
four velocities, one of five skills. `Acorn.Host.Microduck.Action.commands_powered`
states that the release of an action never sends the enable command.
`Acorn.Host.Microduck.Action.next_covers` states, for every release, timely or
late, that the cycle the next percept is computed to have starts no earlier than the
release plus the action's declared duration and a transit allowance:

```lean
theorem Acorn.Host.Microduck.Action.next_covers (action : Acorn.Host.Microduck.Action) (pace : Acorn.Pace)
  (transit : ℕ) (origin : Acorn.Instant) (index : ℕ) (released : Acorn.Instant) :
  released.nanoseconds + action.duration + transit ≤
    (pace.boundary origin (action.next pace transit origin index released)).nanoseconds
```

That a sensed percept cannot precede that cycle is in the pure transitions of a host: a
percept is sensed only in a cycle that is not before that one, and from a state frame heard
since the release (`Acorn.Host.Microduck.Idle.sense_iff`); it can be sensed in a later
cycle. While the percept awaits its action, a reading of the clock sends the velocity of the
action that the deadline rule names in force, up to the end of its hold, and nothing from
then (`Acorn.Host.Microduck.Awaiting.tick_named`).
A host is in one of two phases, each a type whose values are reached from the start by the
transitions, and its verdict at every instant is the deadline rule's for its last step: a
fault holds from the deadline to the release, the instant of the release included
(`Acorn.Host.Microduck.Awaiting.release_fault`), and the latch of the goal is the fold
of the adapter's rule over the readings sensed (`Acorn.Host.Microduck.Reached.latch`).
The pure core of the host's loop calls the transitions with the agent's two step parts, and the action released for a percept is the agent's choice on it (`Acorn.Host.Microduck.Loop.step_release`). The executable `microduck-host` runs that loop over three nc child processes, the trusted transport, at readings of the monotonic clock, and hands it a finished choice or learning only after the runtime answered that its task finished, with the reading taken after that; it is effects, with no theorem of its own. A bridge's state stores the record of its release, and the
cycle of the next percept and the end of the hold are functions of that record, so
`Acorn.Host.Microduck.Bridge.next_covers` holds of every state.
`Acorn.Host.Microduck.Bridge.ticks_named` states that over any list of readings of
the clock every command sent is the velocity of the action that the standing after the
release names at that reading, and `Acorn.Host.Microduck.Bridge.tick_lapsed` that
from the end of the hold that standing names the world's default and nothing is sent. At
the instant of a release itself the deadline rule still names the preceding action, by its
convention that an action is in force after the instant of its release.
`Acorn.Host.Microduck.Bridge.fault_named`
states the action in force during a fault: the preceding action up to the end of its
hold, and the default from it. `Acorn.Host.Microduck.Bridge.tick_fresh` and
`Acorn.Host.Microduck.Bridge.Fresh.age` bound the age of the last send of a
velocity inside its hold. Five things are assumptions of those statements' use and not
theorems: the daemon's expiry of a velocity, the time from a send to the daemon's receipt,
the gap between two readings of the host's clock, that the posture a caller states is the
body's, and that a declared duration covers what the body takes.

What the Microduck senses is kept as bounded integers, also as pure definitions, which the
readers of a daemon's line call when the executable microduck-host hears a frame. The daemon reports a measured quantity as the decimal text of a JSON
number, and `Acorn.Host.Microduck.Decimal.fixed` converts such a number to an integer
of a declared scale by integer arithmetic alone. What it computes is stated over the
rational value of the decimal, `AcornVerif.Decimal.value`, and the predicate
`AcornVerif.Decimal.Nearest`, which name none of the conversion's arithmetic: the
result is the integer nearest to the value in the units of the scale, at a tie the one
farther from zero, saturated to the bounds of the scale.

```lean
theorem AcornVerif.Decimal.fixed_nearest (scale : Acorn.Host.Microduck.Scale)
  (decimal : Acorn.Host.Microduck.Decimal) (nearest : ℤ)
  (near :
    AcornVerif.Decimal.Nearest (AcornVerif.Decimal.value decimal * 10 ^ scale.places) nearest) :
  ↑(Acorn.Host.Microduck.Decimal.fixed scale decimal) = max scale.low (min scale.high nearest)
```

`AcornVerif.Decimal.Nearest.unique` states that at most one integer is nearest, and
`AcornVerif.Decimal.rounded_nearest` that the rounding of the executed arithmetic is.
The statement holds for an exponent of any size. The conversion decides by two comparisons
of integers when a decimal rounds to zero and when it saturates
(`Acorn.Host.Microduck.Decimal.fixed_clamp`), and between them it forms two powers
of ten: the exponent of the one that multiplies the digits is below the width of the
scale, and the exponent of the one that divides is at most the width of the digits
(`Acorn.Host.Microduck.Decimal.shift_between`). The bounds of the result are part of
its type.

`Acorn.Host.Microduck.Decimal.read` gives the decimal of one JSON value. It scans the
spelling that the JSON parser keeps with the parser's own scanner,
`Acorn.Json.Numeral.scan`, and reads exactly the numbers whose spelling is the whole
spelling of a numeral that has the form of a number in RFC 8259, section 6
(`Acorn.Host.Microduck.Decimal.read_iff`). The number that a numeral writes,
`AcornVerif.Decimal.written`, is stated by a table of the ten digits and the place of
each digit, with none of the reader's arithmetic. The integer kept for a value that is read
is nearest to that number in the units of the scale, at a tie the one farther from zero,
saturated to the bounds of the scale:

```lean
theorem AcornVerif.Decimal.read_nearest (scale : Acorn.Host.Microduck.Scale) (json : Acorn.Json.Value)
  (decimal : Acorn.Host.Microduck.Decimal)
  (read : Acorn.Host.Microduck.Decimal.read json = some decimal) :
  ∃ numeral,
    numeral.Formed ∧
      json = Acorn.Json.Value.number (String.ofList numeral.chars) ∧
        ∀ (nearest : ℤ),
          AcornVerif.Decimal.Nearest (AcornVerif.Decimal.written numeral * 10 ^ scale.places)
              nearest →
            ↑(Acorn.Host.Microduck.Decimal.fixed scale decimal) =
              max scale.low (min scale.high nearest)
```

No theorem states that every number of a parsed text is read: it follows from
`Acorn.Json.parse_sound`, whose grammar spells each number of an accepted text as an
`Acorn.Json.Grammar.Number`, with `Acorn.Json.Grammar.number_iff` and
`Acorn.Host.Microduck.Decimal.read_iff`, by an induction over the derivation that no theorem
states.
`Acorn.Host.Microduck.Reading.age_exact` states the age of the depth frame
that a reading is paired with. A parsed JSON value is read into these types by
`Acorn.Host.Microduck.State.read` and `Acorn.Host.Microduck.Depth.read`, and a
frame is read exactly when it is what the value writes, member by member
(`Acorn.Host.Microduck.State.read_iff`, `Acorn.Host.Microduck.Depth.read_iff`).
A whole parsed line is read by `Acorn.Host.Microduck.Line.read` as exactly one case
of declared criteria, which are taken from JSON-RPC 2.0 and are not the whole of it: a
notification, as a frame of its stream or as a notice
(`Acorn.Host.Microduck.Line.read_state`, `Acorn.Host.Microduck.Line.read_depth`),
a response with a result or with an error (`Acorn.Host.Microduck.Line.read_result`,
`Acorn.Host.Microduck.Line.read_fault`), and invalid for every other value
(`Acorn.Host.Microduck.Line.read_invalid`).

A host writes each request as the text of a JSON value of two levels, and the parser of
this repository reads the text of every such value back as the value:

```lean
theorem Acorn.Json.parse_request (request : Acorn.Json.Request) (simple : request.Simple) :
  Acorn.Json.parse (String.ofList request.chars) = Except.ok request.value
```

So for every identifier and command the parser reads the line of a send as the request of
that send (`Acorn.Host.Microduck.Command.line_asked`). A second theorem states what every
text that the parser accepts is: a JSON text of the grammar of RFC 8259,
`Acorn.Json.Grammar.Text`, with a derivation that gives the value that the parser returns
(`Acorn.Json.parse_sound`). So a line of a daemon that the parser accepts is read as a value
that the grammar gives its text. No theorem states that the parser accepts every text of the
grammar, and none is about what a daemon sends or accepts.

Acorn's executable definitions and their state invariants are under lean/Acorn.
AcornVerif contains contracts importing those definitions and supporting
mathematics with explicit hypotheses. `Acorn.Constants` owns the shared machine
words; `AcornVerif.CurrentConstants` checks the stated correspondence with rational and
dimensional inputs used by the mathematical proofs. For example,
`AcornVerif.CurrentConstants.explore_rate_value` states that the binary32 word of the
declared exploration rate denotes the rational those proofs use:

```lean
theorem AcornVerif.CurrentConstants.explore_rate_value :
  AcornVerif.CurrentArithmetic.numerical32 Acorn.Handcrafted.declaredRate.value =
    AcornVerif.ModelConstants.exploreRate
```

Each theorem's actual type owns its domain, hypotheses and guarantee. Binary32
and Binary64 proofs concern admitted finite words or explicitly stated conversion
semantics; real/rational identities do not automatically establish machine
rounding equivalence. Universal program properties are limited to their checked
implementation linkage. Compiler/native runtime, filesystem stability, the
reviewed build/gate tools, cryptographic tools and OS remain trusted boundaries,
and the Regula audit's pass rests on the assumption about Acorn that the
[Regula audit](#regula-audit) states.

## Build and source inventory

The build tools enumerate Git-tracked files through `git ls-files --stage -z`
(stage `0`, mode `100644`/`100755`) and require every tracked path and ancestor
directory to be regular, ignoring untracked working-copy files and run
directories while failing closed on an empty or non-Git tree, unmerged stages,
or any tracked symbolic link or non-regular entry, and check explicit
inventories of the tool modules and of the native entries. Each shell launcher
(`scripts/gate.sh`, `scripts/verify.sh`, `scripts/lean.sh`, `scripts/regula.sh`),
`lean/Bootstrap.lean`, `lean/lakefile.lean` and `lean/AcornTools/TrackedFiles.lean`
admit `scripts/tracked-files.sh` directly against Git before executing it,
`lean/AcornTools/TrackedFiles.lean` admits `lean/Bootstrap.lean` and
`lean/lean-toolchain` before compiled tools invoke them, and `scripts/gate.sh`
admits its child scripts before launching them. Before any shell or Lake consumer reads them,
`scripts/tracked-files.sh` admits manifests (`lean/lake-manifest.json`,
`site/lake-manifest.json`), toolchains (`lean/lean-toolchain`,
`site/lean-toolchain`), Lake configurations (`lean/lakefile.lean`,
`site/lakefile.toml`), `lean/Bootstrap.lean`, the verified shell scripts,
`lean/no-comments.pin`, `.no-comments.json`, and `comment-ratchet.json`. On
both cache-stamp hits and misses, it validates every tracked source under
`lean/` (and under `site/` for site commands) on disk as a current non-symlink
regular file beneath non-symlink directories, enforces real workspace-owned
non-symlink containment across `.lake`, `lean/.lake/packages` (and each
manifest-named dependency checkout directory, its git metadata, configuration
file and manifest file when present), `.lake/config`, Lake's numeric package
configuration cache directories, and `lakefile.olean`, trace and
`lakefile.olean.lock` destinations (ignoring unrelated untracked entries such as
`.DS_Store`, refusing ambient `package-overrides.json` in any active workspace,
and refusing an untracked `lakefile.toml` inside `lean/` on the
`scripts/regula.sh` route that uses Lake's default resolution), and decodes
`lean/lake-manifest.json` through Lake's manifest loader before the first Lake
workspace load in `scripts/gate.sh` and `scripts/regula.sh`.
Repository-relative document path references, browser assets, Lake manifests
and native inputs likewise require tracked regular entries (with `lean/.lake`
and `lean/.lake/packages` admitted only as directory references in
documentation), and `native-audit` derives its `.c` and compile-trace artifact
paths directly from the current admitted native module inventory rather than
walking compiler output directories. When tracked Lean files change,
`scripts/tracked-files.sh` deletes only cached `lakefile.olean` and trace files
whose parsed trace confirms Acorn ownership (leaving missing, malformed and
other packages' traces untouched) and writes the tracked-module stamp
atomically through an exclusive temporary file (while `lean/Bootstrap.lean` and
`lean/AcornTools/Gate.lean` write their override files the same way) before invoking Lake
(`-f lakefile.lean` through `Bootstrap.lean`, `-f lakefile.toml` under `site/`,
and default workspace resolution after shadow-config refusal for
`scripts/regula.sh`), while `scripts/verify.sh` invokes
`SHELLCHECK_OPTS='' shellcheck --norc` so ambient configuration cannot alter
script checks. The checks take their file lists from Git's stage-0 tracked
regular-file index without materializing a separate HEAD checkout or hashing
every tracked file independently against HEAD; verdict-producing commands
(`./scripts/gate.sh`, `./scripts/verify.sh` outside `site write` and
diagnostics, `./scripts/regula.sh`, and the compiled audit executables
`acorn-gates` outside `site write` and diagnostics, `lean-boundary-audit`,
`native-audit`, `ownership-audit`, `corpus-audit`, `theorem-count`,
`intent-check`, and `frame-check` outside `frame-check print`) additionally
check via Git that the index and working tree report no staged or unstaged
changes against HEAD and no assume-unchanged or skip-worktree index flags
(hosted CI and validation runs already execute on fresh checkouts of the exact
commit), while keeping `git diff --check` and `no-comments`'s internal index
lookup intact. Direct development builds, non-verdict executables (such as
`world-certificates`), `frame-check print`, `./scripts/verify.sh diagnostics`
and `./scripts/verify.sh site write` enforce stage-0 regular-file tracked
admission while permitting uncommitted edits to tracked files. Runtime
`--research-profile` selects agent mechanisms; it does not change verification.
Resource, route and compiler flag admission, browser byte generation, corpus and
declaration checks always run. Missing or untracked referenced files fail
admission.

Numerical proofs use the executing Lean definitions. Native admission checks
their compiler IR, primitive calls, resource contracts and compiler flags.
Primitive IEEE interpretation remains a native assumption.

The merge gate is `./scripts/gate.sh`. The no-mistakes pipeline runs it
(`.no-mistakes.yaml`) before a pull request opens, on the exact commit it
validates, and every gate check enumerates only Git-tracked stage-0 regular
files so untracked working-copy entries do not enter checks or change the
verdict, apart from the deliberate refusals of ambient `package-overrides.json`
in an active workspace, non-regular or symlinked entries in checked `.lake`
destinations, and an untracked `lakefile.toml` inside `lean/` during
`scripts/regula.sh`. GitHub runs the same
script at each event that gives a pull request its head, within the limits
described after the frame check below. The gate provisions the pinned dependencies,
then runs the command twice, from cold project outputs, each run under its own
360-second deadline. The first, `./scripts/verify.sh build-executing`, admits the
sources as the complete command does, then selects every module outside the proof
library `AcornVerif` except `AcornTools.AxiomPins`, and every executable. It builds
these targets and their dependencies, with native objects where applicable, and
admits nothing after the build. The axiom pins import the proof library, so they
remain in the second stage despite belonging to the tools. The second is the
identical complete command, which selects every tracked module: Lake
reuses an output of the first only where its trace matches the checked-out
source, toolchain and options, and builds the rest. So in the gate the cold
build and the checks no longer share one deadline: the first bounds the build of
the executing library, the tools except the axiom pins, and their dependencies;
the second bounds the remaining proof build, the axiom pins and every check.
On a four-processor machine the cold build with the checks beside
it inside one deadline left too little margin. The gate then runs the
[Regula audit](#regula-audit), lean-intent's two checks and the frame
check on the same commit (each also when an earlier step failed), and serially
after them (only when ordinary verification succeeded, so un-admitted sources
are never elaborated) the pinned `no-comments`
check (`.no-comments.json`, `comment-ratchet.json`, `lean/no-comments.pin`),
passing only when both runs, the audit and all four post-checks pass. When
ordinary verification passed,
lean-intent's two checks and the frame check run one after another in a
background subshell beside the Regula audit, because every module and executable
is already built and all three read the finished build without writing to
`lean/.lake/`; when verification failed, all three run one after another, and the
`no-comments` check is refused without executing the binary. Otherwise, once
verification succeeded, the `no-comments` check runs serially afterward so its
workers never overlap with the Regula audit's memory peak, offline-verifying the
binary's SHA-256
from `lean/no-comments.pin` (for `darwin-arm64` and `linux-x86_64`) before
executing and checking all scoped `.lean`
files across `lean/` (including `lean/lakefile.lean`) and `site/` code
(`site/AcornSite.lean`, `site/AcornSite/`, and `site/Main.lean`, excluding
`site/AcornDocs.lean` and `site/AcornDocs/` Verso prose), using explicit
`-f lakefile.lean` and `-f lakefile.toml` workspace configuration flags in
`.no-comments.json` after validating `.no-comments.json`'s configured ratchet
path, workspace directories, Lake flags, empty tool/workspace-exclude prefixes
and Verso-scoped exclude prefixes alongside `lean/no-comments.pin` and both
workspaces against tracked regular files,
against `comment-ratchet.json` for exact head sync, plus unconditional
monotonic non-growth against the merge-base ratchet alongside rejecting newly
excluded files that still hold comments at the merge base (tracked files with
zero comments carry no ratchet entry).

The lean-intent checks run from `lean/AcornTools/Intent.lean`. It reads the
modules from Lake: the libraries among the default targets, through the Lake
script intentLibraries of the [Lake configuration](../lean/lakefile.lean), and
the modules of each through the modules facet of Lake itself, refusing an empty list of
libraries, a library with no module and a module listed twice. It imports those
modules into one environment and gives the one list to lean-intent's confirmation
check, which decides that each deliverable's current revision is confirmed by
answers whose authority traces back to the owner, and to its implementation check,
which decides that each deliverable names the constant implementing it, with the
proof that it fulfils the record. The gate passes only when the first finds
nothing, the second reports no awaiting-implementation declaration, and the
findings of the second are, as a set, the unimplemented findings of
the deliverables that the checker's one closed list names as awaiting an
implementation, each with the issue that tracks its fulfilment proof
(`AcornVerif.Intent.onlyAwaiting_iff`, `AcornVerif.Intent.implemented_of_onlyAwaiting`).
Another finding, an awaiting-implementation declaration, a listed name that is
no declared deliverable and a listed deliverable that gains an implementation
each fail it, and both checks refuse a project that declares no deliverable. The list names the hash record's
deliverable, whose proof rbeauchamp/acorn#184 tracks, the deliverable of the
intent record of contract 1 of the mission contract, the interface every world
meets, whose proof rbeauchamp/acorn#213 tracks, and the deliverable of the intent
record of contract 3, the invariants of learning from one stream, whose proof
rbeauchamp/acorn#215 tracks; it was decided on the owner's
behalf by the agent supervising Acorn's research, since the intent-first method
confirms a record before its implementation exists, and it remains until the
listed deliverables migrate to lean-intent's awaiting-implementation
declaration (rbeauchamp/lean-intent#52). That the modules Lake lists are all those of the
package, and that the constant an implementation names is what an executable runs,
are trusted.

The frame check runs from `lean/AcornTools/Frame.lean`. A target's file freezes
the target's text. A pin file beside it, a regular file ending in `.frame` in
`lean/AcornVerif/Targets/`, freezes what that text reads: it names the target, the
names a submission may change, the names kept and not followed, and, for every
other declaration of the project that the target reaches through types and
definitions, the SHA-256 digest of its printed kind, universe parameters, type and
value. The check enumerates Git-tracked regular files under
`lean/AcornVerif/Targets/` (refusing an empty targets set), admits only regular
files ending in `.lean` and regular files ending in `.frame`, and accepts a
non-empty tracked targets directory with zero `.frame` files; any other tracked
entry under that directory, a subdirectory or a symbolic link included, fails
it and is named, while untracked working-copy entries are ignored. The check
reads declarations
from compiled modules, never from sources, and running it builds the checking
program and no module that program reads. So for each pin file it first
requires the module the file names to be, under exactly that name, one of the
package's Lean source files, a member of the inventory that verification's
build requests from. It then asks Lake, through the bootstrap and building
nothing, for the source file and the compiled file of the root package's
module of that name, which Lake gives only when the module is built from the
present sources. It requires that source file to be the inventoried file, and
the compiled file Lean finds for the module to be the compiled file Lake
named. It fails, naming the module, when
the tree holds no source file of exactly that name, a name that differs from a
source's only in the case of its letters included, when the root package does
not hold the module, when Lake does not report the module and every module of
the workspace it imports current, when Lake reads the module's source from
another place, and when Lean finds the module's compiled
file elsewhere. A module of a dependency or of the documentation package is
refused as no source of this package, and any tracked entry below the package
directory that is neither a regular file nor below regular directories fails
the inventory and the check with it. The command that prints a pin file requires
the same things
before it reads a module. So a compiled file that an earlier build left
behind is not read in
place of the tree's source, as far as Lake's record of what is current is
right: that record, and that nothing but Lake has written the compiled files
since, are trusted. The check relies besides, as every check of the gate does,
on the stability of the file system while it runs, which the
[compiler and execution boundary](#compiler-and-execution-boundary) lists among
the trusted boundaries. The check then computes
that list from the compiled module and fails when a
pinned declaration is no longer reached, has another digest, or a reached
declaration is not pinned, naming each. With no pin file it reports that no
target's frame is pinned and passes, so a target is pinned only once the owner
has merged its pin file. The digest detects a change; it is no evidence of what a
declaration means. The dependencies' declarations are not pinned here: Lake's
manifest pins their commits.

The pipeline stores the provisioned dependency checkouts, their build outputs
and the pinned `no-comments` binary once for each default-branch commit a run
starts from, and gives a run a private copy only while the run's toolchain,
lock and `no-comments` pin files equal that commit's; Lake rebuilds whatever
its traces do not show current. Acorn's own outputs are never carried from one
run to another.

GitHub runs the gate through the
[verification workflow](../.github/workflows/verify.yml): when a pull request is
opened or reopened and at every push to its branch, whether that branch is in
the repository or in a fork, on the pull request's head commit, within the
limits given below. Nothing else starts the workflow, and it cannot be started
by hand. A run started by hand on main would be in main's own context, where
what a run stores is restored by later runs on main, and GitHub's code scanning
reports a workflow that can run there and executes the script of a commit taken
from a pull request as a route to poisoning what main's runs restore (CodeQL's
query `actions/cache-poisoning/poisonable-step`). With no such trigger, no run
of the workflow is in that context. A pull request's job is run again from the
pull request, on the same commit (GitHub's documentation, Re-running workflows
and jobs). The workflow is one job. It takes the
head commit from the event, fails before any check when the event names none,
checks out full history (so `origin` holds the pull request base branch), and
never falls back to the merge of the head with its base. From that checkout
it runs `./scripts/gate.sh provision` to provision the pinned dependencies
(including the SHA-256-verified `no-comments` binary into `lean/.lake/packages`),
then runs `./scripts/gate.sh` with `ACORN_BASE_REF` set to `refs/remotes/origin/`
and the pull request's base branch name (which the script passes through
`--base-ref` to the pinned checker, which resolves it and refuses an
unavailable reference) to run the same gate as the pipeline's Test step.
No step of the workflow names a Lake target, a module, a package or another
script of the project, so the job relies on the
head only for that script and its two forms. So the dependencies and the checks
on GitHub are the script's own, with no second list to keep equal to it, and a
head whose script or Lake configuration is older or newer than the one on main
is provisioned and checked by its own. A failing check fails the job, and the
job's result is shown on the pull request. The job runs for a pull request to any
base branch, so that one later retargeted to main keeps the run made on its
head, and nothing runs after a merge. Because `no-comments` compares against
`refs/remotes/origin/` and the pull request's base branch when the job runs,
retargeting from a base with a looser ratchet when the head already contains main
relies on the owner re-running `./scripts/gate.sh` against main before merge.

The arrangement on GitHub differs from the pipeline's as follows. A step of
the workflow downloads elan's pinned release in every run and installs it only
after the archive's SHA-256 matches. The script's provisioning runs in a step
of its own, whose 27-minute limit bounds a stalled download and is no check's
deadline, and the script's provisioning in the last step then finds the
dependencies current. Nothing is stored between runs: every run
provisions everything from its pinned sources and builds from cold project
outputs. A copy stored by an earlier head of a pull request, which controls its
own workflow, could otherwise be restored and trusted by a later head whose own
changes show nothing of it. The job has a 60-minute limit, where the
pipeline's Test step has none. That limit is the sum of the limits of the two
jobs that ran these checks side by side before 2026-10-28; no check's own
deadline changed, and each of verification's two stages keeps its 360-second
deadline. This shape, slower than two jobs with stored dependencies, was decided
on the owner's behalf by the agent supervising Acorn's research.

A pull request's run is started by GitHub's ordinary event for pull requests,
never the privileged one that runs with the base repository's rights, so the run
for a fork's pull request receives none of the repository's secrets and a token
that cannot write to the repository. The workflow names no secret, asks for read
access to contents only, keeps no credentials in its checkout and pins the
checkout action by revision. No setting cancels or skips a run because a newer
head arrived: each head's run finishes, and its result stays on that commit.

That event has five limits, which Acorn accepts: GitHub's other event for pull
requests, which does start a run for a conflicting head, runs in the base
repository's own context, where a fork's code can reach its secrets and a token
that writes (GitHub's documentation, Events that trigger workflows). That
a fork's run holds no secret is the owner's requirement; naming the limits as
accepted was decided on the owner's behalf by the agent supervising Acorn's
research. Each limit is given below with what the pull request then shows for
its head. What the absence of a run and each ending of a run say about the
checks is stated after the fifth limit.

First, an event on a head that conflicts with its base starts no run. GitHub
starts no workflow for activity on a pull request that has a merge conflict
(GitHub's documentation, Events that trigger workflows, in the notes on the
event for pull requests). No run starts either when the conflict clears without
a push, as when main changes; a push or a reopening then starts one. A run that
an earlier event started on the same commit stays on that commit, as when a pull
request passed, was closed and is reopened after its base came to conflict with
it.

Second, a fork's run can wait for a maintainer. Under the repository's setting,
read on 2026-11-20, GitHub holds the workflows of a first-time contributor's
fork until someone with write access approves them, and marks a run left
unapproved for 30 days as failed (GitHub's documentation, Approving workflow
runs from forks). Until then the pull request shows the workflow as awaiting
approval, with no result. The approval lets the job start and nothing more: it
is no review of the change and no result of a check. GitHub holds in the same
way the run of a pull request that a workflow opens or updates with its own
token (the same notes); no workflow of Acorn does that.

Third, a pull request that edits the workflow or the gate script is checked by
its own edit. GitHub uses the version of a workflow in the commit of the event
that starts it (GitHub's documentation, Workflows), which for a pull request is
its merge with its base, and the job runs the script of the head. Such a pull
request can show the job as passed while it runs fewer checks than the gate on
main has. A reader sees that only in the pull request's changed files, under
the paths that [CODEOWNERS](../.github/CODEOWNERS) gives to the owner; nothing
in the run refuses the edit.

Fourth, a head whose event came before this workflow ran on pull requests, or whose
merge with the base it then had did not hold this workflow, has no run, since
GitHub repeats no event. A pull request open at that time shows no run of this
job until its next push or reopening, and then runs like any other, by its own
head's script.

Fifth, a head whose commit message carries one of GitHub's skip instructions gets
no run (GitHub's documentation, Skipping workflow runs). The pull request shows
no run of this job for that head until a commit without the instruction is
pushed.

Neither the absence of a run nor a failed run is by itself the result of a
check. What a run says about the checks is read from the log of the job's last
step, "The merge gate on the exact source", the only step in which a check
runs, in the `gate:` lines that the head's own script prints there. Each of
these lines ends with the time of day and the seconds since the script started.
The script of this revision prints `gate: verification, stage one` before its
first check and then reports each check's exit status on its own line:
`gate: verification exited 0; Regula audit beside lean-intent and frame checks`
(or `gate: verification exited N; Regula audit` when verification exited
non-zero) for verification's two stages together,
`gate: Regula audit exited N; lean-intent checks`,
`gate: lean-intent checks exited N; frame check`,
`gate: frame check exited N; no-comments check` and
`gate: no-comments check exited N` (or
`gate: no-comments check refused (integrity check failed)` when the cached
binary fails cache-containment or offline SHA-256 verification before starting, or
`gate: no-comments check refused (verification failed)` when either stage of
ordinary verification failed); when verification passed,
`gate: verification exited 0; Regula audit beside lean-intent and frame checks`
prints before either starts, while
`gate: Regula audit exited N; lean-intent checks`,
`gate: lean-intent checks exited N; frame check` and
`gate: frame check exited N; no-comments check` wait until both the Regula
audit and the background subshell finish.
It prints `gate: every merge check passed` last, and only when every status
is 0. A head that holds another revision of the script runs that revision's
checks and prints that revision's lines, which the head's own `scripts/gate.sh`
gives: a revision from before the `no-comments` check or frame check prints no
line for it.

For each check, the only evidence that it ran on the head and failed is a
`gate:` line that reports its exit status as other than 0, and the only evidence
that it ran and passed is such a line with the status 0. The only evidence that
every check of the head's script passed is the line
`gate: every merge check passed`. Each attempt of a run is read by its own log.
In the attempt being read, a check with no line that reports its exit status has
no verdict (including when the script prints
`gate: no-comments check refused (integrity check failed)` or
`gate: no-comments check refused (verification failed)` before starting the
binary, which still fails the gate), and an attempt without the passing line is
no pass of the gate. So an
attempt gives no check a verdict when GitHub marked it failed before a runner
started, as when an approval was never given; when a step before the last
failed; and when the last step ended before `gate: verification, stage one`, as
when the script's own recheck of the provisioned dependencies fails. When the
last step ends in the middle of a check, as when the job is cancelled at its
limit, each check already reported keeps its line, and that check and those
after it have no verdict in that attempt. A head with no run at all has no
verdict of any check.

Whether a merge requires this job is set in the repository's rules on GitHub,
not in a file of the repository. Where the rules require it, a head on which it
has not passed does not merge: GitHub requires a required check to pass on the
latest commit (GitHub's documentation, Troubleshooting required status checks).

Ordinary verification shares a compiler environment for ownership, the theorem
inventory and document-symbol admission. Executable entries retain isolated `main` owners
and reuse loaded dependency regions. Each IR reference must belong to that
entry's actual compiled import closure; data loaded for another entry cannot
satisfy this check. Shared regions live only for the audit process, and no prior
acceptance result is cached. Source, boundary, native-route and browser checks
remain required. Standalone ownership, theorem and corpus commands remain
available for focused diagnostics.

Checks that do not depend on one another run at once: the two source admissions
with Lake's target inventory before the project build, and compiled boundary,
native, browser-kernel and ownership admission after it. Each of these
prints the output of a step whole when the step ends, and all of them are reaped
before a failure is reported. The site check runs after these admissions, also
when one of them fails, because building the documents can rebuild this
package's modules into the build directory that the admissions read. The build
requests modules first and executables after them. An executable whose Lake
configuration names a target it needs is held back with its root module: both
are requested after every other module and executable, because Lake waits for
that target before it reads the next request, so every other job is scheduled
first.
Each compiler process of the build uses at most two threads, where the default
is one for each processor; this limits how far the processes Lake runs at once
compete for the same processors.

## Regula audit

[Regula](https://github.com/rbeauchamp/regula) is an audit of Lean builds. Acorn
requires its release v0.13.1, pinned in `lean/lakefile.lean` and locked in
`lean/lake-manifest.json` at the commit that the release's tag names, and the
merge gate requires the Regula audit:

```sh
./scripts/regula.sh
```

The script obtains Regula's proof verdict by the route that the release
publishes: two commands, in order, on one build, each from the directory lean
with no option of Lake's and with the variable `REGULA_FULL` unset. The first,
`lake build --wfail`, fails on any warning, which a proof hole gives. The second,
`lake lint`, is Regula's checker. It reads the build, replays the claim's cone in
Lean's kernel into an empty environment, and runs Regula's rules under the
profile that the package's `lintDriverArgs` states. It exits 0 for a pass, 1 for
a fail and 2 for an incomplete run, and its last line states the verdict; a pass
ends that line with the directory it audited. The script passes only when
`lake lint` exits 0 and its last line is the pass on lean. The commands resolve
dependencies through the Git lock in `lean/lake-manifest.json`, without the
bootstrap's path overrides, so Lake fetches a dependency whose checkout is not
at the locked revision. The other passages of Acorn's documents that describe
the gate's Regula step refer to this one.

The claim's cone is each constant of a claimed module and every constant that
one of them reaches through what each mentions, as Lean's kernel checks it, with
the constants that the kernel itself builds into a term, and nothing else. The
kernel must accept each of them, so an unsound proof in a dependency that the
claim reaches fails the audit, as one in a claimed module does; a constant of an
imported module that the claim does not reach is not replayed. Regula's rules
follow the same relation, so a claimed constant that reaches Lean's proof-hole
axiom, a project axiom, an axiom that `native_decide` adds, or any axiom outside
the profile fails the audit.

A pass of Regula's proof verdict means, as the release states, that the proofs
of the claimed modules are sound and use only axioms that the profile allows,
for a project that places no file or code aimed at the checker or the toolchain.
Its two commands run in Acorn's own Lake, so a project written to attack them
could make them print a pass whatever its build holds: through a library that
the loader takes from the project's own library directory into the checker, a
doctored copy of Regula that the project's configuration or package directory
supplies, the code of its Lake configuration, or code that runs while it builds.
Acorn is its own project, written to be verified and not aimed at Regula's
checker or Lean's toolchain, and the audit relies on that: it is an assumption
of Acorn's trusted base, which no check of the gate establishes. The pass also
rests on Regula's own list of assumptions about Lean, Lake and the operating
system, and holds only in Regula's named configurations: Lean v4.36.0, the
route above, and macOS 27.2 on Apple silicon or Ubuntu 24.04.5 LTS on x86-64.
It says nothing about what a compiled program runs, which the checks of
ordinary verification below cover, or about whether a theorem states what was
meant, which review reads.

Regula's full verdict needs no assumption about the project. It starts the
checker from a checkout of Regula built apart from the project, and before
anything is compiled it refuses each construct outside a closed set, so that,
under five hypotheses that Regula states about Lean, Lake and the operating
system, no code of the project runs while it builds. Acorn cannot get it: only a
project with no dependency in its Lake configuration and no Mathlib in its
imports can, and Acorn requires Mathlib, Regula, FloatLib and lean-intent.
Regula's
[README](https://github.com/rbeauchamp/regula/tree/v0.13.1#what-a-pass-means)
and
[specification](https://github.com/rbeauchamp/regula/blob/v0.13.1/specification/README.md#a-project-aimed-at-the-checker)
state both verdicts and what each rests on.

The claim is the modules of the default targets of the Lake configuration and
every module of the package that their imports reach. The default targets are
the libraries Acorn, AcornVerif, NativeApp, Bootstrap and AcornDocument. They hold
every Acorn theorem: the executing definitions with the theorems stated beside
them, the proof library, the native application, the build launcher, and the
names that the document audit admits from outside the project with the theorem
that states what an admitted name is. A theorem can mention only declarations of
the modules its own module imports, so every definition of the package that a
claimed theorem is about is claimed as well. `lake lint` imports the claimed
modules into one environment, where Lean refuses two
declarations of `main`. So Bootstrap, which `lean --run` interprets before anything is built,
declares the one top-level `main` of the claim, and the root of each of the
twelve application executables is a
module of the library Entry, outside the claim. Its `main` applies the entry
function of a claimed module, such as `Acorn.SwiftTdDriver.main`, and it holds
nothing else; the theorem inventory refuses a theorem in it. AcornTools, the
reviewed tooling trust boundary with the
eight tool executables, and the
[documentation site](#documentation-site) are also outside the claim and hold no
theorem.

The profile is standard-logical: propext, Quot.sound and Classical.choice, and no
other axiom, for the whole claim. No stricter profile is attainable, because
Lean's core definitions of binary32 and binary64 arithmetic depend on
Classical.choice, as does the Mathlib analysis in AcornVerif. One bridge module in
AcornVerif is the only importer of FloatLib, a proof dependency whose theorems
use the same three axioms; the boundary audit refuses a FloatLib import by any
executing module. A second bridge module in AcornVerif is the only module the
boundary audit admits that imports lean-intent, the proof dependency in which the
intent records under `AcornVerif.Intent` are stated; it depends on nothing beyond
Lean's own libraries, and the audit refuses a lean-intent import by any other
module it admits. Of the tool modules, which it does not admit, only the merge
gate's lean-intent checker, `lean/AcornTools/Intent.lean`, imports lean-intent, for
the two readers it runs. The compiler, native runtime, operating system and spawned
processes stay trusted.

`lean/Acorn/Decisions.lean` states the contracts of the library's decision
functions for which a property of the accepted or refused result is proved, and
registers those functions. A decision function is an admission, parser or
validity test: its result accepts or refuses an input. A contract is a Regula
executable contract about the executing definition itself, with the kind its
proof establishes. A two-way kind states that the function accepts exactly the
inputs that satisfy the written specification, with one accepted and one refused
input as witnesses. A registration is a declaration of Regula's type
RegisteredDecision. No rule of Regula reads a contract or a registration: the
ownership audit requires, for each registered function, a contract with a kind
in `Acorn.Decisions` or `AcornVerif.Decisions`, so it fails when a contract is
removed while its function stays registered. A decision procedure whose result
type is `Decidable` carries both directions in its type and is registered with
no contract. An admission with an argument or result type that depends on an
earlier argument, and a decision that takes its element type as an argument,
carry a kind in the forms that Regula.Contract gives for them. The kind is
stated about the function applied to every field of a structure of its arguments
and, where the result type depends on the input, about whether the result holds
a value, with the value forgotten. A statement of the value of an accepted
result stands beside such a kind as a requirement with no kind. A function keeps
a requirement with no kind where no kind is true of it or where the rule for
specifications below excludes the kind, and the ownership audit requires the
contract by name. The module documentation of `lean/Acorn/Decisions.lean` gives
the four reasons: a function that accepts every input or whose accepted inputs
no theorem states; a specification that reads a part of the input, such as the
state of a learner, whose type declares an invariant that names tests that the
function runs; a verdict that is the guard of the function, where the guard
applies a definition that no proposition states apart from it, such as an order
of the viewer's captures; and a result whose type depends on the input and is
neither an option nor an error, such as an index that comes with the equation
that names it, which the kinds read only through whether it holds a value. A
requirement with no kind is checked only as a theorem about the executing
definition. Such a statement can fix one direction only, and it need not show
that both outcomes occur for its function. Kinds for the functions of the second
reason are remaining work of
[issue 105](https://github.com/rbeauchamp/acorn/issues/105). A contract states
only what its theorem proves.

A kind compares a function with its specification as the two are defined now.
Where the two call one test, a defect of that test changes the two sides
together, and the proof of the kind can stay valid. So the specification of a
contract with a kind reaches no test that the function or the acceptance
predicate also reaches, read at any depth through the declarations it names,
the declared types of the parts of the input it reads among them. A test is a
function with a result of `Bool`, or a definition of an instance of BEq, Lean's
class of equality tests, outside Lean's own library. The projection function of
a structure field is no test, whatever the type of the field: it reads stored
data. Review applies this rule; no check of Regula or of Acorn does. Acorn states
each such condition as a proposition, with a theorem that connects the test with
it, such as `Binary32.Negative` for the sign bit or the strict order
`Binary32.Less`. A function that a specification reaches, such as the signed key
`Binary32.key`, decides the proposition through an instance that runs the test,
so the executed comparison is the same one. The rule says nothing of a
projection function, so `inventory_craft` may read the fields
`Host.Inventory.axe` and `Host.Inventory.boat`, which its specification and its
function both read, and nothing of a shared function with another result than
those two, such as `Binary32.key` or `Host.terrain`. Review admits such a
function where something other than the kind fixes it: a primitive operation of
a number type that Lean's library defines, or a definition with a statement of
its own against a reading that does not apply it, such as the slot map of the
feature bank, stated as SplitMix64 on Lean core's bit vectors. The module
documentation of `lean/Acorn/Decisions.lean` names those statements, the groups
of shared definitions that have none yet, and each proposition with its theorem.

No check of Acorn finds a decision function that is not registered. The module
documentation of `lean/Acorn/Decisions.lean` lists the groups of definitions with
a `Bool`, `Option`, `Except` or `Decidable` result that carry no contract, with
the reason for each group. That list has no check of completeness: a new
definition with such a result can arrive with no contract and no entry. No kind
says that a specification is the intended one. `Acorn.Decisions` belongs to the
Acorn library, so the claim covers it, and it registers no function of another
library. It is the only module that imports Regula's registration type. No module
imports it, so no entry point links what it declares; the boundary audit admits
it with the proof sources and refuses an import of it. `AcornVerif.Decisions`
states the contracts whose proofs need the proof library. Their functions are
registered in `Acorn.Decisions`, and the ownership audit counts a contract with a
kind in either module toward a registration. It requires each statement there
with no kind by name. The certificate checkers have their contracts there. No
checker is complete about its goal, so a refused certificate establishes nothing
about whether the goal can be reached: the blocked checker and the stance
checker carry the sound kind. The replay checker carries the two-way kind about
its action list: it accepts exactly an action list of at least one and at most
the cap actions whose run of the executed world step, from the world with the
goal installed, ends in a world in which the goal is attained. The world step
decides propositions in the place of its tests, so that specification shares no
test with the checker. The module documentation of
`lean/AcornVerif/Decisions.lean` lists the functions of that module that keep no
kind, with the reason for each and which of them are also remaining work of
issue 105.

The audit is a second check of the merge gate and is not part of
`./scripts/verify.sh`. It builds the claimed modules again where Lake's traces
differ and runs Regula's checker, whose replay of the claim's cone does not fit
beside the ordinary checks inside the 360-second deadline. The gate runs it
after ordinary verification and requires both before a merge. A pass is Regula's
proof verdict, with the meaning and the assumption that the section above
states; it does not replace review.

### What Regula checks in place of Acorn's tools

Acorn's tools under `lean/AcornTools` are outside the claim, so no proof covers
them. They check a compiled declaration or the Lake configuration only where no
part of the Regula audit refuses at least the same inputs for the same modules.
Each paragraph below takes one property: what the Regula audit refuses for the
claimed modules, and what the tools check. Where the tools refuse more, the
paragraph gives an input that shows it, and that check stays.

Ordinary verification alone therefore does not refuse a project axiom, a
dependency on an axiom outside propext, Quot.sound and Classical.choice, a
compiler-trusting proof, or a compiled unsafe or partial declaration outside
RG1006's exempted forms (a partial recursion helper of a terminating recursive
definition, or the unsafe implementation half of a verified compiler-generated
constructor-index pair). The Regula audit refuses each of them, and the merge
gate requires it. Run `./scripts/regula.sh` for it before proposing a change to
a Lean source.
Ordinary verification still refuses the words `axiom`, `sorry`, `unsafe`,
partial and `native_decide` in every executing and proof source, through source
admission, and a proof hole through the build, where a warning is an error.

**Project axioms.** RG1001 refuses an axiom declared in a claimed module. The tools
make no such check.

**Axioms that a declaration depends on.** RG1003 refuses a constant of a claimed
module with a transitive axiom outside propext, Quot.sound and Classical.choice,
and RG1005 one whose axioms exceed the standard-logical profile. Both rules
examine every constant: theorems, definitions and instances, and read what each
constant mentions as Lean's kernel checks it, so an axiom that a claimed constant
reaches only through an inductive type's block counts. The tools make no such
check. The tool module AcornTools.AxiomPins still pins the exact axiom
sets of selected theorems in the build, with message guards around
`#print axioms`; it imports the proof library and lies outside the claim with the
other tools.

**Proof holes and compiler-trusting proofs.** RG1002 refuses a constant that
depends on Lean's proof-hole axiom, directly or through an import, and RG1004 one
that depends on an axiom that `native_decide` or a related tactic adds. Both rules
read the transitive axiom set. The tools make no such check.

**Unsafe, partial and looping declarations.** RG1006 refuses a constant of a
claimed module that is unsafe, partial or named as a recursion helper, without
an exempted form (a partial recursion helper of a terminating recursive
definition, or the unsafe implementation half of a verified compiler-generated
constructor-index pair on Lean v4.36.0), or a constant whose value mentions the
loop constructs that while and repeat compile to. The tools make no such check
of compiled declarations.
The host's loops that run until something outside the program happens, such as
the end of a stream or a stop request, iterate over `Acorn.Host.forever`, whose
iteration in IO and BaseIO is a fixed-point definition with the one-step
unfolding of Lean's own loop (`Acorn.Host.forIn_io`). The viewer's stream of
live frames runs in Std's Async monad, which runs a continuation in a task, so
no such definition exists for it; it calls Std's own loop of that monad, the
one that repeat reaches there, and that loop is part of the trusted toolchain.

**Kernel replay.** `lake lint` checks every constant of the claim's cone in Lean's
kernel again from an empty environment, so a proof that the build's own kernel
check skipped is checked there. Regula's specification records a module that
added, with the kernel check skipped, a theorem of False whose name Lean marks
as internal and that nothing mentions: Regula v0.12.0's three commands passed
it, and v0.13.0's `lake lint` gives an incomplete verdict, RG2001, with the
kernel's refusal. The tools make no such check.

**Native replacements: the tools refuse more.** The theorem inventory refuses each
declaration of a module of Acorn, AcornVerif, NativeApp, AcornDocument or Entry
that carries a replacement attribute or an extern attribute, whatever reaches it
and whatever is proved about it, except a verified compiler-generated
constructor-index replacement that Lean v4.36.0 emits for every safe, non-Prop,
non-builtin inductive type whose constructor count is not one
(`AcornTheoremCount.isCompilerCtorIdx`, matching Regula v0.13.1's structural
check on the pair and its toolchain constructor-tag helper). The Regula audit
reads replacement and extern attributes only to qualify RG1006's exempted forms
(recursion helpers and constructor-index pairs) and has no general rule refusing
them on safe declarations: a pass says nothing about what a compiled program
runs. Source admission refuses both attributes as words in every executing and
proof source, so the inventory adds the declarations that elaboration generates.
This check runs once, in the theorem inventory. A copy in the compiled boundary
admission would repeat the same predicate for a subset of the same modules in
the same command, `./scripts/verify.sh`.

**Reach of each entry: the tools refuse more.** The ownership audit follows the
compiler's intermediate code from the entry point of each executable, the tool
executables among them. It refuses an extern or a proof hole in a maintained
module on the way, and requires that the entry reaches each definition that
`entryUses` lists for it, the claimed entry function first. Regula examines no
compiled code.

**Module inventory: the tools refuse more.** The Lake configuration sets
`roots := #[]` on its libraries, constructs explicit per-module globs solely
from Git-tracked regular `.lean` files below `lean/`, and admits every declared
executable's root module against that same tracked regular-file inventory
during configuration elaboration and target discovery. A new tracked source
below Acorn, AcornVerif or NativeApp is therefore a module of that library, the
claim covers it, and Acorn's boundary predicates class it by its name;
untracked files on disk are neither assigned to libraries nor buildable as
library modules or executable roots. The tools keep no written
list of those application modules. A new tracked source below
`lean/AcornTools` is a module of a tool library outside the claim: ownership
admission enumerates tracked regular `.lean` files from Git and requires each
tracked source outside the five libraries assigned from tracked modules to be an
entry of `toolingModules`, and each entry to be a tracked source. A tracked
source below `lean/` that no library has is outside the claim unless a claimed
module imports it: the same requirement refuses it, and Lake refuses the build
request for a module that no library has.

**Executable inventory: the tools refuse more.** Ownership admission refuses a Lake
executable whose target name and root module are not a pair of `executables`,
and a listed pair that Lake does not have. It also requires that a module
declares `main` exactly when it is the root module of an executable or is
Bootstrap, the interpreted build launcher. The list is also the Lean owner of the
executable names that the build order and this document read.

**Decision registrations.** The ownership audit requires a contract with a kind for
each registered decision function whose result is not `Decidable`, as stated
above, and counts only a contract about the whole function whose condition
applies its kind to that function. Its subject is the function applied to
nothing but the arguments its type takes implicitly, so a contract about one
application does not count. Its condition is the kind with every argument but
the last, which the contract supplies with the function, or a function of the
contract's subject whose body is the kind with a last argument that mentions the
bound variable; any other form, such as a condition that ignores its argument
and decides the identity function, does not count. Regula reads no
registration.

Regula has no rule for the import layers of the learned-only boundary, the
capability owners, source syntax admission, the departures register, native
admission, the corpus checks or the required proof links. Those checks are
Acorn's own.

## Review protocol and the rule on runs

Two of Acorn's rules are written rules. No check of the gate, of Regula or of
GitHub executes either, and both are accepted risk in Acorn's trusted base.

The first is the [review protocol](../CONTRIBUTING.md#review-protocol), which
says which review a pull request gets, who assigns its referee or reviewer,
what the report, the short review or the validation pipeline's review holds
and when work is complete. The gate establishes that the
proofs of a change are sound and that its checks pass on a commit. It
establishes nothing about whether a theorem states what its pull request
claims, which the referee reads, nothing about whether a referee or a
reviewer was assigned as the protocol requires, and nothing about whether a
pull request passed the maintainers' validation pipeline. The trace of the
protocol is the pull request itself: the comment that records the assignment
and each referee's report, the short review or the validation pipeline's
review. One GitHub account serves the owner and the organization's agents, so
under individual maintainer-led assignment GitHub does not show that the agent
that assigned a referee or a reviewer is another than the one that did the work;
the assignment comment states who assigned. For a pull request that claims no
result and passed the maintainers' validation pipeline, the assignment comment
records the owner's standing designation of the validation pipeline's
configured reviewer, that the pull request passed, the run, the reviewer's
model family and the exact head commit, beside the run's unedited review.
Unedited means that a posting withholds nothing but a security
vulnerability's details and private material, which is a private path, a
private record or personal data, each withheld part of private material
marked as withheld with its kind; each finding's existence, the verdict and
what was done about each finding stay on the pull request.
Under the single-maintainer interim provision, while Acorn has one human
maintainer, a truthful assignment comment for a referee's review or a short
review can instead record the owner's standing designation of the model
configured as the validation pipeline's reviewer, reading the pull request
standalone as that review requires, its model family, and the exact head
commit without identifying a separate per-PR assigning agent, alongside its
unedited exact-head report or short review. The protocol prohibits same-family
self-review (disqualifying that model if chosen for author-side review,
advice, writing or fixing while permitting re-reads after findings issued in
its designated referee or reviewer role), falls back to another model family
or an uninvolved person under the general rule when the designated model is
disqualified, and retires that use of the designation once Acorn has more
than one human maintainer. No check enforces that a pull request passed the
validation pipeline, model-family separation, designated-role vs. author-side
advice, multi-maintainer retirement, or which findings still block after a
review's third round, leaving those checks as accepted risk in the written
protocol. A
referee or a reviewer can be wrong, and two referees can both be wrong. An
author's own account of a goal that changed while the work was done is
something the protocol cannot check, since a referee sees the pull request and
not how it was produced; the referee's reading of the work is what can catch
it (a risk the owner allowed on 2026-11-20). A short
review must state the three things it checked; that
its three lines were written after reading, and not copied as a formula, is
something no rule can see. Whom the rule of
assignment admits as a referee or a reviewer for work that a person did with
no model is the
maintainers' call. A change to what the protocol requires, allows or rules
out merges only once the owner has confirmed it, and no check enforces that
either: [CODEOWNERS](../.github/CODEOWNERS) names neither the contributor
guide nor the review skills, so GitHub requests the owner's review of no
change to them. A review counts only for the commit, title and description it
read, and GitHub lets a title or a description be edited at any time, so that
the description that merged is the one that was reviewed rests on the
maintainers' reading at the merge. A finding that discloses a security
vulnerability is reported, answered and ruled on by the private route and
only named as open or closed on the pull request; that it is closed before a
merge is likewise checked by no tool.

The second is the rule on runs
([what counts as a run](../CONTRIBUTING.md#what-counts-as-a-run)): stepping
the agent or one of its learners over a sequence of percepts is a run by
whatever means, and every pull request lists the computations made on the
agent, with the parts that section gives for each entry. No cheap executable guard exists for an evaluation
made in a scratch file or on a contributor's machine, since nothing of it need
reach the pull request. The rule's trace is the list in the pull request's
description, which rests on its author's account and which the referee or
reviewer reads against the change.

## Documentation site

This guide is a [Verso](https://verso.lean-lang.org/) document,
`site/AcornDocs/Verification.lean`, in a separate Lake package under site. A Verso
document is a Lean module, so building the page elaborates what it says about
Lean. A declaration or module it names must resolve. A theorem statement is
printed from the theorem Lean checked. A constant or an audit pin is a Lean term
whose value is read from its owner when the page is rendered, so the document
holds no copy of it. A reference that no longer matches its owner fails the
build. The other documents under docs are Markdown and are not built this way.

```sh
./scripts/verify.sh site
```

The site check runs after the project build and the other admissions of the
finished build, inside the deadline of `./scripts/verify.sh`; the command above
runs it alone. It builds the documents, renders the pages
and requires `docs/verification.md` to equal the Markdown rendering of this
document; `./scripts/verify.sh site write` writes that file. The Markdown file is
kept so that existing links and readers on GitHub are served, and so that the
document and pin checks of verification, which read Markdown, still cover this
guide. The rendered pages stay in the working copy; nothing is published.

The step maps each locked dependency of the site to its provisioned checkout, so
Lake fetches nothing, and refuses to run until Lake reports pinned Verso built.
The renderer runs in Lean's interpreter: a linked executable would compile the
native code of every proof module a document imports. If the site check stops
fitting the verification deadline, it becomes a separate check of the merge
gate with its own bound; the deadline is not raised. At the shared site entry of `lean/AcornTools/Gate.lean` (covering
`./scripts/verify.sh site`, `./scripts/verify.sh site write` and full
verification) and before site provisioning in `scripts/gate.sh`,
`scripts/tracked-files.sh` parses `site/lakefile.toml` and both lock manifests
through Lake itself (deriving the site's path-override manifest directly from
Lake's decoded manifest entries), requires `roots = []` and closed single-module
globs whose effective module set together with `site/Main.lean` equals the
Git-tracked regular `.lean` files under `site/` (and `AcornOwnership.siteModules`),
admits `site/lakefile.toml`, `site/lake-manifest.json`, `site/lean-toolchain`,
`site/Main.lean`, `docs/verification.md`, and `.lake` containment (without
refusing unrelated `lakefile.lean` files under `site/`, since every site
invocation passes `-f lakefile.toml`), synchronizes `lean/` tracked-module
configuration traces, enforces unique decoded package names and checkout
directories, requires the exact Acorn path requirement and manifest entry
(`../lean` without copy), and requires every shared Git dependency of
`lean/lake-manifest.json` to match in URL, revision, subdirectory (none),
configuration file and manifest file, because both packages share one set of
dependency checkouts.

The site package is documentation tooling outside the Regula claim.
[Verso](https://github.com/leanprover/verso), pinned in `site/lakefile.toml`, and
Lean's elaborator are trusted to build it. The build establishes that each
reference exists, has the stated type and shows its owner's current value; review
still decides whether the prose describes that owner faithfully.

## Mutation diagnostics

**Pinned digest: `0x28c98382d02dbf12`**

In work on a change, the command below is run only on the owner's authorization
for that run.

```sh
lean/.lake/build/bin/acorn-core audit --expect 0x28c98382d02dbf12
```

The expected digest has one form, `0x` and exactly sixteen lowercase hexadecimal digits:
it is a hash identifier, not a number, so it is not read as a command-line number and
digit-only text such as `10` is refused.
Paired checksum `68e84d568d55f8ad`. The deployed arm runs the ranked profile
with the declared D6 exploration rate. The optional ./scripts/verify.sh diagnostics
command runs all three fixed arms under the same deadline. All three pins record
the published generate-and-test tester and task-reading generator (PAR-11, D7),
off-policy option learning (PAR-17) and option expectation models with planning under
the current values (PAR-13, PAR-14). Every pin also records persistent exploration by whichever layer
selects the action, a run interrupting the option whose draw began it and closing its
meta span there (PAR-8, D3);
the declared-rate and differential pins also record the stable, sign-correct
reward-respecting subtasks, assigned at every free decision boundary, and the
declared-rate dynamics decision. The fixed audit arms
are compared through these paired digests. Run these optional diagnostics when
investigating a dynamics change, and in work on a change only on the owner's
authorization for that run: they are not on the closed list that
[running a program](../CONTRIBUTING.md#running-a-program) points to.

## Checkpoint admission

Format 21 holds the exact image of the agent:
every field of its temporal state, the option models, primitive credit, the rate schedule
and every process-local reference included. Every earlier format is refused
(`AcornVerif.CurrentCheckpoint.previous_generation_unloaded`). Format 20 stores, after
each option slot's trajectory, that option's off-policy questions, which the agent no longer
holds (PAR-18, retired). Format 19 has the layout of format 20, but its weights were placed by
the hashes that read their first two words only through their XOR, so a saved weight can sit
at the slot of another feature. Load checks dimensions,
identifiers, criterion and step order
in the header, then reads the image with every stored word in its own domain, every
learner through the check of its invariant and the agent's two invariants. An incompatible
image is refused and writes to that file are disabled. Loading the bytes that a save of a
state writes returns that state, for every state of the resumable construction
(`AcornVerif.CurrentCheckpoint.load_saved`). The world restarts, and the host begins a
new session of the predictive-agreement evaluator. Filesystem persistence relies on the
narrow C file-sync helper, native IO and the operating system; `lean/Acorn/Host/Checkpoint/IO.lean`
states what a saved report establishes on each platform and what stays accepted risk.

## Viewer ownership boundaries

The viewer observes telemetry and supervises process lifecycle. Only a stop
request enters the core, at an attempt boundary. Source/compiled ownership
prevents learned code from reaching host control. Browser numeric and lifecycle
contracts have executable owners and generated bytes; see
[the viewer specification](viewer-ux.md).
Predictive agreement compares forecasts with settled finite returns within the
current process. Incomplete horizons and unavailable state are reported as unknown.

Every lifecycle decision the supervisor makes about the core process and the run's published state
is made by one pure step, `Acorn.Host.Viewer.Supervision`, except the actor's pre-launch check of
the ranked core's executable file below: a closed state, the events the native
actor `Acorn.Host.Viewer.Supervisor` hands it, and one step per event or per outcome of the call
it waits for, which returns the next state and the effects to perform. The actor reads the
world, performs the effects in order and then the call, and hands the call's outcome back before
it reads anything else; it is effects, with no theorem of its own. Each turn reads, while nothing
is pending: the identity a process reported, one queued command, the process slot, the identity
again, so that a reaped process's last report is attributed before any launch or archival, and
then a tick. The state the step returns is stored before its effects run, so a native error that
stops the effects after it leaves that state, and the next turn goes on from it, as a restarted
viewer goes on from the state file. A supervision is sealed by
its run from its start, and every state a run reaches keeps one invariant
(`Acorn.Host.Viewer.Ran.invariant`): a run directory that moved with no replacement owned is
never acted on again (`Acorn.Host.Viewer.Supervision.retired_untouched`), a configuration that
disables Clear never archives (`Acorn.Host.Viewer.Supervision.clear_disabled`), a closing viewer
starts nothing (`Acorn.Host.Viewer.Supervision.closing_starts_nothing`), and a spawn waits on a
durable state that records its launch (`Acorn.Host.Viewer.Supervision.spawn_recorded`). A spawn
follows only the successful write of that state, takes the generation one above the last, and
only when the lifecycle is idle, intends to run, has no Clear pending and its restart budget
admits a launch at that instant (`Acorn.Host.Viewer.Core.resume_launch`); no event and no other
outcome reserves a generation or waits to spawn (`Acorn.Host.Viewer.Core.step_calm`,
`Acorn.Host.Viewer.Core.resume_calm`). A Stop winds a live process up whether or not its intent
is saved (`Acorn.Host.Viewer.Core.stop_winds_up`); a core's exit never closes the viewer,
which closes at a later tick that the actor hands after it attributes the identity the core's
readers delivered (`Acorn.Host.Viewer.Core.step_finished_defers_close`); every lifecycle
value with an exhausted restart budget intends to stay stopped
(`Acorn.Host.Viewer.Lifecycle.exhausted_stopped`), and the published control reasons retain
the capped cause and explain giving up after three failed starts
(`Acorn.Host.Viewer.controlTelemetry_reasons`); Clear
installs a run other than the one it retires (`Acorn.Host.Viewer.Core.replaced_identity`);
the instants recorded by steps and outcomes do not go back, whatever the clock reads
(`Acorn.Host.Viewer.Core.instant_later`, `Acorn.Host.Viewer.Core.step_last`,
`Acorn.Host.Viewer.Core.resume_last`); and
every result first installs its own lifecycle and publishes its control record from it
(`Acorn.Host.Viewer.Stepped.effects_settle`). The operating system's process, signal and wait
semantics, the file system's durability, the Lean runtime's IO, mutexes and clock, the identity
a core reports, the actor's mapping of each effect and call to the native operation it names, and
its pre-launch check of the ranked core's file remain the trusted base.

The viewer's supervisor starts its child, the core or the command `--cmd` names, only on an
explicit act: the `--start` flag, a Start on the viewer's control endpoint, which the page's Start
button sends, or a state file whose running intent an earlier Start set while the supervisor's
child was the child this launch starts. The viewer starts two other processes outside the
supervisor, neither of them a learner: a relay of its standard input under `--control-stdin`, and
the system's opener for the page under `--open-browser`. The state the bootstrap builds when the
run directory holds no state file intends to stay stopped
(`Acorn.Host.Viewer.PersistedState.unstarted`). For every Clear configuration, every durable
state that intends to stay stopped, and every state reached from the start on it by steps on
events that hold no operator's Start and by outcomes of the pending calls: the lifecycle admits no
reservation at any instant and intends to stop, and the call the state waits for, if any, is no
spawn and writes no state that intends to run
(`Acorn.Host.Viewer.Reached.stopped_spawns_nothing`;
`Acorn.Host.Viewer.Reached.unstarted_spawns_nothing` states it for the state built with no
state file). The relation these statements are about covers one supervisor's lifetime: one start,
its steps on events and the outcomes of its pending calls. It ends with that viewer; it reads no
state file and starts no second viewer. The states it reaches are the states of a run and no
others (`Acorn.Host.Viewer.Reached.ran`, `Acorn.Host.Viewer.Ran.reached`). The
statement is not empty: from the start on every durable state that admits a launch, there are
events that hold a Start and a state reached by them that waits to spawn the first generation
(`Acorn.Host.Viewer.Core.start_spawns`). That is a statement of existence, whose witness has
every call between the Start and the spawn succeed; a Start whose intent cannot be written reaches
no spawn. The state built with no state file admits a launch for every seed within the browser's
integers (`Acorn.Host.Viewer.Core.unstarted_launch`), and the control record of the start on
that state says the run is desired stopped and actually stopped
(`Acorn.Host.Viewer.Core.start_control`).

A state file is decoded only when it is a JSON object that holds the six members of the state,
each admitted, and beside them at most a schema version and a child record; any other is refused.
Two things then decide whether the intent it records is kept. The first is the version: the
natural number that the `schema_version` member spells in decimal digits alone, of any size
(`Acorn.Host.Viewer.stateVersion`). A member that is absent, or that is spelled any other
way, as a string or as a number with a sign, a fraction or an exponent such as `3e0`, is no
readable version and marks an earlier version's file. Every state the decoder returns for a state
file whose schema version does not read as the current one intends to stay stopped
(`Acorn.Host.Viewer.PersistedState.decode_earlier`), and the statement above holds of the
supervisor started from a state that was successfully decoded from an earlier version's file
(`Acorn.Host.Viewer.Reached.earlier_spawns_nothing`). Before the file carried a version, the
viewer wrote a running intent in it when it found no file, with no Start, so such a file cannot
show that a Start set its intent. For a file that names another natural number the decoder returns
an error (`Acorn.Host.Viewer.PersistedState.decode_other`), and so it does for a file whose
schema version is a number whose digits spell two to the power 64 or more
(`Acorn.Host.Viewer.PersistedState.decode_wide`).

The second is the child. With every state it saves, a viewer writes the record of the child its
supervisor would start (`Acorn.Host.Viewer.childRecord`): the executable's path, its length
in bytes, the 64-bit FNV-1a digest of every byte of the file
(`Acorn.Host.Viewer.fileDigest`), and the argument vector at a reference launch. One action
reads the file at that path, its length and its digest, and a file that cannot be read whole gives
no record; the bootstrap reads it with that action when the viewer starts. A launch under `--cmd`
has
no record, because the process a shell starts for a command depends on the working directory, the
environment and the files the command names. The decoder returns a running intent only for a file
that names the current version and the record of the launch that reads it, which must have one
(`Acorn.Host.Viewer.PersistedState.decode_running`). Every state it returns to a launch with
no record, or with another record than the file names, intends to stay stopped
(`Acorn.Host.Viewer.PersistedState.decode_unbound`), and the statement above holds of the
supervisor started from such a state (`Acorn.Host.Viewer.Reached.unbound_spawns_nothing`).
So a running intent saved while the supervisor's child was one process is not taken as a Start for
another: a Start given under a fixed command does not start the ranked core at a later launch, and
neither does one given for a core at another path, of another length or content, or with
other arguments. Sameness is equality of the two records and no more. This part is read from the
code and not proved: before the ranked core is started, the first time and at every restart, the
actor reads the executable's file again by the same action and compares its length and digest
(`Acorn.Host.Viewer.ProgramReading`) with what the viewer read when it started, whether or not
the state file can hold the record. It does so once, before the launch is recorded: a refusal
there writes nothing and spawns nothing, so the saved state is exactly as it was before the
refusal: no new mark of a started process and no agent epoch spent. A run that had already started
a process keeps that mark, and the running intent that a Start saved before the launch was checked
stays as saved. The run is shown stopped with
the reason. No process could have been created on that path. After a launch is recorded the actor
spawns with no further reading, so no refusal of this kind follows the record: a file replaced
before that reading is refused, and one replaced after it, before the launch record or after it,
is not seen and is started, which is the first of the limits named below. The reason of a
refusal is shown in the page and printed on the viewer's standard
error, and it tells three cases apart, each with what clears it: the program differs from what
this viewer read when it started, and starting the viewer again records it as it is now; the
program cannot be read now, and the refusal clears in this viewer when the file can be read again
with the same content, while starting the viewer again does not help as long as it stays
unreadable; the program could not be read when the viewer started, and starting the viewer again
when it can be read clears it. A fixed command is written and spawned with no reading: a Start
under `--cmd` is an explicit act for that command line as given, and it covers the restarts of
the command by the viewer that received the Start, whatever program the command designates when
each restart is made, so a program replaced under that command line between a Start and a restart
is run by the restart. Where a launcher passes `--cmd` with a command that names the core, a Start
is an explicit act for a learner and its restarts are covered by that act. For the ranked core
three things are
assumed and not compared: the interval between that reading and the operating system starting the
program, in which the launch is recorded, so that a file replaced in that interval is started;
that the environment the child inherits is unchanged; and that
two files of equal length and equal digest are one. The digest suffices against accident, a
rebuilt file that agrees in length and in a 64-bit digest by chance, and forging it needs no more
power than writing the state file by hand, which is an accepted risk already. The fixed command
is a fourth accepted limit beside these three: making use of it needs the power to replace a
program on this machine between a Start and a restart, which the other limits already assume, and
the ranked core, which is the learner, is compared before every start. A file that names
the current version and this launch's child is restored with the intent it records. A running one
resumes when its launch is admitted
(`Acorn.Host.Viewer.PersistedState.launch`: a run that has started a process needs a next
agent epoch within the browser's integers) and the writes and the spawn that follow succeed.

The rest is read from the code and not proved. The actor hands the step an operator's Start only
for a command that was submitted to its queue, which the bootstrap does for the `--start` flag and
the HTTP server for an admitted control request. The bootstrap hands the supervisor the state it
read or built. Every state the actor writes carries the record of its own child. Of the text the
viewer writes, the other fields of a state read back as written, and a running intent reads back
as running exactly for a launch with the same, present record: a running intent written under
`--cmd`, which has no record, reads back stopped, by design.
`Acorn.Host.Viewer.RunDirectory.readState`
refuses a state file that is unreadable or malformed. It refuses without opening it an entry that
is not a regular file or a link to one, such as a link whose target is gone, a directory, a pipe
or a device, so that it never waits on one, and it reads only a run directory with no entry under
the state file's name as no file. On a refusal the viewer exits before it serves anything,
constructs no supervisor and leaves the file as it is, because a file another version wrote is not
guessed at and reading it as stopped would publish over it. That a running intent in a state file
follows a Start given in some earlier viewer, while that viewer's child had the record the file
names, is argued from the write clause above by induction over the viewers that owned the run
directory, assuming that only viewers write the file. It is not proved, and the theorem, which
ends with one viewer, says nothing of a crash or of the viewer that comes after it.

The order at start-up is this. The viewer reads the state, builds its supervisor, binds its
listener, and only then prints the ready line and submits. When the state is written depends on
what the decoder (`Acorn.Host.Viewer.PersistedState.admit`) returns as its source. A state
built with no file (`Acorn.Host.Viewer.StartSource.absent`), or read from a file of the
current version with the intent that file records (`Acorn.Host.Viewer.StartSource.saved`),
is written in the supervisor's construction, before the listener binds. An earlier version's
file, whatever intent it records (`Acorn.Host.Viewer.StartSource.earlier`), and a file of
the current version whose running intent was given for another child
(`Acorn.Host.Viewer.StartSource.other`) are left exactly as they are
(`Acorn.Host.Viewer.StartSource.kept`) until the listener is bound. The bootstrap then
prints and flushes the line that says why the run is shown stopped, under the `--start` flag as
well, and only then publishes the stopped state it started from, in the current schema with this
launch's record,
before it prints the ready line, before the `--start` flag submits its Start and before any
command is processed. If the line cannot be written or flushed, the viewer exits before the
publication and the file is still the original. So a start-up that fails before that publication, with or without the
`--start` flag, leaves the next viewer the same file and the same reason, and such a file is read
as an earlier version's, or as given for another child, once: in the first launch that publishes
the stopped state. That is the boundary, and no other: the reason is not lost by a failure before
the publication, and after the publication it has been given, in that launch's first control
record and in its log, and is not given again. After it, a viewer of the earlier version started on the directory meets a file
of the current version. A crash between the bind and the publication leaves the original file. A
start-up that fails after the publication, when the ready line cannot be written for example,
leaves a current-version stopped file, and the reason the next launch gives is that the saved
state says stopped. A Start that reaches the control endpoint before the publication is only
queued; it is handled at a later turn of the actor if the start-up goes on, and is lost with the
viewer if the start-up fails after the publication. If the publication fails, the viewer exits
with that error before it prints the ready line: a failure before the rename leaves the original
file intact, whereas an indeterminate rename error (such as POSIX.1-2017 `rename` EIO or Linux
NFS rename-despite-error) can leave either the original file or the newly renamed current-version
stopped file on disk, so the next launch reads whichever entry is present and gives that entry's
reason. A viewer that fails once its listener is bound
ends through its shutdown, whose turns step the supervisor to close it and can write the map; no
turn on that path takes a command from the queue, so nothing is started from the intent the file
records and a Start queued by then is not handled. Whenever the start state is stopped, the one
line that says why (`Acorn.Host.Viewer.startAccount`) is in the reason of the first control
record the supervisor publishes, under the `--start` flag too. A page that connects while that
record is current shows the line; one that connects after a later transition has published its
record is sent that record and shows that transition's reason. The viewer also prints the line on its standard output, at most once in a launch: for a file
left as it is until the bind (an earlier version's, whatever intent it records, or one of the
current version whose running intent was given for another child) the line is printed and flushed
after the listener is bound and before the stopped state is published, under the `--start` flag
as well; for no state file, or a file of the current version that says stopped, it is printed
after the ready line and not under the flag. Under the flag the Start is submitted after the listener binds and is handled at a later
turn of the actor. The viewer says nothing of this kind when the start state is running.

The explicit-start statement above starts from a durable state that intends to stay stopped;
browser Stop persistence closes the crash window between acknowledging a browser Stop and
writing `desired = .stopped` to `state.json`. In the control endpoint
(`lean/Acorn/Host/Viewer/HttpServer.lean`) and supervisor actor
(`lean/Acorn/Host/Viewer/Supervisor.lean`), `Acorn.Host.Viewer.Supervisor.submitControl`
holds an admitted `stop` request behind a promise until the supervisor actor completes the
state-file write rather than replying on queue admission alone (and
`Acorn.Host.Viewer.Supervisor.submit` refuses `.stop` so callers cannot bypass durable
dispatch). For the pure supervisor step,
`Acorn.Host.Viewer.Core.step_no_ackStop` shows no step emits
`Acorn.Host.Viewer.Follow.ackStop`; `Acorn.Host.Viewer.Core.resolve_ackStop_spec`
and `Acorn.Host.Viewer.Core.resume_ackStop_spec` establish that
`Acorn.Host.Viewer.Follow.ackStop` is emitted only upon a successful write
whose written `Acorn.Host.Viewer.PersistedState` has `desired = .stopped`,
and `Acorn.Host.Viewer.Core.resume_error_no_ackStop` ensures every
write-error outcome omits `Acorn.Host.Viewer.Follow.ackStop`.
`Acorn.Host.Viewer.Core.stop_acknowledges_or_refuses` covers every supervisor state
(idle or busy, open or closing/closed, current or retired owner, with or without a waiting
replacement): stepping `.command .stop` either refuses immediately via
`Acorn.Host.Viewer.Follow.refuseStop` without emitting
`Acorn.Host.Viewer.Follow.ackStop`, or schedules a `.writeState` of a stopped
`Acorn.Host.Viewer.PersistedState` (without acknowledging on the step) whose resolution
emits `Acorn.Host.Viewer.Follow.ackStop` on write success and
`Acorn.Host.Viewer.Follow.refuseStop` without `Acorn.Host.Viewer.Follow.ackStop`
on write error. Under an interleaving state machine over disk updates (including indeterminate state-write
rename errors via `Acorn.Host.Viewer.CrashStep.writeFailIndeterminate`), crashes between
any two steps, and reboots (including optional startup state write-back and arbitrary Clear
configurations) (`Acorn.Host.Viewer.CrashState`, `Acorn.Host.Viewer.CrashStep`,
`Acorn.Host.Viewer.CrashReached`, `Acorn.Host.Viewer.CrashState.Invariant`,
`Acorn.Host.Viewer.CrashReached.invariant`),
`Acorn.Host.Viewer.PersistedState.encode_decode_stopped`,
`Acorn.Host.Viewer.CrashReached.crashed_disk_stopped` and
`Acorn.Host.Viewer.CrashReached.startup_cannot_resume_running` prove that
once `Acorn.Host.Viewer.Follow.ackStop` has been observed in supervisor processing order
with no later Start admitted by an idle, open supervisor (ordered at the actor's acknowledging
resolution rather than browser HTTP receipt time, so a concurrent Start processed after that
resolution supersedes it), a crash at any point leaves the on-disk state
stopped (or absent mid-Clear archive), so whenever a reboot loads the state via
`Acorn.Host.Viewer.DiskState.BootState` (covering both missing-file startup and any
successful parse and decode), the loaded state has `desired = .stopped` and never resumes
running without a later explicit Start, while
`Acorn.Host.Viewer.CrashReached.stop_never_acked_on_write_error` proves that a failed
write step — whether the failure leaves the previous disk entry untouched
(`Acorn.Host.Viewer.CrashStep.writeFail`) or publishes the temporary file despite
reporting an error (`Acorn.Host.Viewer.CrashStep.writeFailIndeterminate`) — leaves
`ackedStop` unchanged without emitting `Acorn.Host.Viewer.Follow.ackStop`.
`Acorn.Host.Viewer.exists_stop_crash_restart_witness` constructs a
`stop -> write -> ack -> crash` trace from every running persisted state with a conditional
boot extension for every admissible `Acorn.Host.Viewer.DiskState.BootState`, and
`Acorn.Host.Viewer.exists_stop_crash_reboot_populated` unconditionally inhabits the full
`stop -> write -> ack -> crash -> boot` trace by proving `Json.parse` and
`Acorn.Host.Viewer.PersistedState.decode` succeed on the published stopped file.
The boundary between these theorems and the host program is read from the code and not proved:
`Acorn.Host.Viewer.RunDirectory.writeState` writes and flushes an exclusively created
temporary file and renames it over `state.json` under the run directory's stable-path
assumption; neither the temporary file nor the directory is fsynced (power-loss durability is
not claimed), and visibility of complete bytes without torn files rests on local-filesystem
atomic rename semantics. Although `Acorn.Host.Viewer.CrashStep.writeFailIndeterminate`
models an ambiguous `state.json` rename failure (such as POSIX.1-2017 `rename` EIO
or Linux NFS rename-despite-error) without weakening the stopped-disk or no-ack guarantees,
`Acorn.Host.Viewer.RunDirectory.archive` classifies any caught filesystem rename error as
`Acorn.Host.Viewer.ArchiveResult.unchanged` without re-inspecting the filesystem, so
archival assumes on the failure side that a failed directory rename leaves the run directory
at its original path. Mapping `Acorn.Host.Viewer.Follow.ackStop` to HTTP `202` and
definite pre-execution refusals (`Acorn.Host.Viewer.ControlResult.refused`, `busy`,
`unavailable`) versus unconfirmed Stop outcomes
(`Acorn.Host.Viewer.ControlResult.unconfirmed`, serialized with `"unconfirmed":true`,
including write errors that may still request child wind-up and the 10-second `awaitControl`
timeout that ends only the HTTP wait without cancelling the Stop) to HTTP `503` in
`HttpServer.lean` and `Supervisor.lean` — where `Supervisor.performInActor` maps
`Acorn.Host.Viewer.Follow.refuseStop` to a fixed public
`Acorn.Host.Viewer.ControlResult.unconfirmed` string so HTTP `/control` JSON responses
never expose raw OS `IO.Error` messages or local run-directory/archive paths (detailed native
diagnostics remain in `Supervision.lean`'s `core.report .failed` diagnostic path and stderr) —
is likewise read from the code. On viewer shutdown interrupting an admitted Stop, the supervisor
resolves the waiter as `Acorn.Host.Viewer.ControlResult.unconfirmed` so HTTP returns `503`
(`{"ok":false,"unconfirmed":true,"reason":...}`) if the response completes before server teardown,
whereas server cancellation during shutdown can also yield an empty `503` or closed connection
without a JSON body; the browser treats both fail-closed as unconfirmed/unknown. Exiting without
starting a core on a parse or schema refusal from
`Acorn.Host.Viewer.RunDirectory.readState` in `lean/NativeApp/Viewer.lean` is likewise
read from the code. Nor does the theorem say who may
submit a Start: the viewer serves its page on the loopback interface to whoever loads it. And that
a Start was given is a property of the program: it is separate from the owner's authorization for
a run of a learner, which [running a program](../CONTRIBUTING.md#running-a-program) governs.

The paragraphs that follow give the definitions and lemmas those statements rest on, each with
what it says. A sentence about the actor, the reader or the bootstrap is read from the code and
not proved: no theorem covers them, because the actor
(`lean/Acorn/Host/Viewer/Supervisor.lean`), the reader and the bootstrap
(`lean/NativeApp/Viewer.lean`) are effects.

The supervisor starts its child in one place, the actor's
`Acorn.Host.Viewer.Call.spawn`. The actor makes a call only as the call of the pending
operation its state waits on, after it has performed the effects of the step that produced that
state; so it makes that call only when the state waits on
`Acorn.Host.Viewer.Pending.spawn`, and it makes it then if it reaches that call. The
theorems are about the step the actor runs (`Acorn.Host.Viewer.Core.start`,
`Acorn.Host.Viewer.Core.step`, `Acorn.Host.Viewer.Core.resume`). Their proof keeps
one property of a supervisor's state, that every intent the supervisor holds is to stay stopped
(`Acorn.Host.Viewer.Core.Unstarted`): the lifecycle's, the durable state's, a waiting
replacement's and the pending operation's. Its four parts are that the lifecycle intends to stop
and no Clear restores a running intent (`Acorn.Host.Viewer.Lifecycle.Unstarted`: the
lifecycle intends to stop, and a pending Clear restores no running intent); that the durable
state intends to stop; that a replacement that waits to be published intends to stop; and that
the pending operation carries no running intent and starts no process
(`Acorn.Host.Viewer.Pending.Unstarted`: neither a launch nor a spawn, no Start's intent,
and no state or Clear intent that says running). The intent of every command but Start is stopped
(`Acorn.Host.Viewer.Command.desired_stopped`): `Acorn.Host.Viewer.Command.desired`
computes it, and whether it is saved is the step's, since a disabled Clear changes nothing.

The start itself asks for no launch. For every durable state it is given, one that intends to
run included, and every Clear configuration, reason and reading,
`Acorn.Host.Viewer.Core.start` gives a state whose process slot is empty and which waits
on no call, whose lifecycle is the initial lifecycle of that state's identity and intent
(`Acorn.Host.Viewer.Lifecycle.initial`), which holds that durable state and no
replacement, and whose detail is the initial transition with the reason given. The supervisor
publishes that detail in its first control record. A page is sent the control record that is
current when it connects (`Acorn.Host.Viewer.Broadcast.subscribe`), so it shows that reason first
only if it connects before the record of a later transition has replaced that one
(`Acorn.Host.Viewer.Broadcast.settle`). What the start gives is the definition as written and not
a theorem, and the bootstrap gives it only a state that it built or admitted. So a supervisor that starts from a matching saved
running intent takes up that intent at its start and has asked for nothing there: a launch
becomes pending only in the launch check (`Acorn.Host.Viewer.Core.launchCheck`), which
the start does not make. The first constructor of `Acorn.Host.Viewer.Ran` is that start,
for every durable state, reason and reading. Whether the durable state is on disk when the
supervisor starts is a separate matter, given with the order at start-up above.

A lifecycle that intends to stop, with no running intent held for a pending Clear to restore,
admits no reservation, for every such lifecycle and every instant
(`Acorn.Host.Viewer.Lifecycle.unstarted_reserve`), and it keeps both under every
transition but two: a Start request, and a running intent queued while a Clear's replacement
waits (`Acorn.Host.Viewer.Lifecycle.replacementIntent`). A stopped intent queued while a
replacement waits keeps the lifecycle so
(`Acorn.Host.Viewer.Lifecycle.replacementIntent_unstarted`). An unstarted supervisor
launches nothing: for every state whose intents are all to stay stopped and every instant, the
launch check leaves the state as it is, with no change and nothing to follow
(`Acorn.Host.Viewer.Core.launchCheck_unstarted`). A step on any event but an operator's
Start keeps every intent stopped, for every state whose intents are all to stay stopped, every
Clear configuration and every reading (`Acorn.Host.Viewer.Core.step_unstarted`). Every
outcome of the pending call keeps every intent stopped, for every state whose intents are all to
stay stopped, the operation it waits for and every reading
(`Acorn.Host.Viewer.Core.resume_unstarted`). An unstarted supervisor starts no process and
writes no running intent: for every state whose intents are all to stay stopped, the lifecycle
admits no reservation at any instant and intends to stop, and the call the state waits for, if
any, is no spawn and writes no state that intends to run
(`Acorn.Host.Viewer.Core.Unstarted.spawns_nothing`).

`Acorn.Host.Viewer.Reached` relates an origin, the events handed to the step, the most
recent first, and a state reached from the origin by steps on events and by outcomes of pending
calls. Its constructors are the origin, before any event; a step on an event; and the outcome of
the call the state waits for. Nothing in it reads a state file or starts a second viewer. The
states reached from a start are states of a run (`Acorn.Host.Viewer.Reached.ran`), and
every state of a run is reached from a start by some events
(`Acorn.Host.Viewer.Ran.reached`); a run is `Acorn.Host.Viewer.Ran`, which every
`Acorn.Host.Viewer.Supervision` carries. No Start, no running intent: for every Clear
configuration, every origin whose intents are all to stay stopped, and every state reached from
it by events that hold no operator's Start, the state's intents are all to stay stopped
(`Acorn.Host.Viewer.Reached.unstarted`).

The statements of the theorems in full are these. A supervisor started from a stopped intent
waits on no spawn while no Start is handed to its step: for every Clear configuration, every
durable state that intends to stay stopped, every reason and reading the viewer starts with,
every sequence of events that holds no operator's Start, and every state reached by it from that
start, the lifecycle admits no reservation at any instant and intends to stop, and the call the
state waits for, if any, is no spawn and writes no state that intends to run
(`Acorn.Host.Viewer.Reached.stopped_spawns_nothing`). The three statements that follow are
that statement for particular start states. The first is for the state the bootstrap builds when
the run directory holds no state file, for every seed and whether or not a stray checkpoint was
adopted (`Acorn.Host.Viewer.Reached.unstarted_spawns_nothing`). The second is for every
state that `Acorn.Host.Viewer.PersistedState.decode` returns for a JSON value whose
`schema_version` member is absent, is not a number spelled in decimal digits alone or spells a
number other than the current version
(`Acorn.Host.Viewer.Reached.earlier_spawns_nothing`). The third is for every state that
the decoder returns to a launch that has no child record, or whose record differs from the one
the JSON value's `child` member names, or that reads a value with no such record
(`Acorn.Host.Viewer.Reached.unbound_spawns_nothing`). The control record of a start with no
state file says the run is stopped: for every seed, whether or not a stray checkpoint was
adopted, and every Clear configuration, reason, reading and observation, in the control record of
the start state the desired word and the actual word are both `stopped`
(`Acorn.Host.Viewer.Core.start_control`); the start on a restored running state has
another desired word. By the write clause of the first statement, a supervisor waits on the write
of a running intent only after a Start was handed to its step, or from a start state that held
one.

Those statements would hold of a supervisor that never spawned. After a Start, some continuation
waits to spawn: for every Clear configuration, every durable state that admits a launch, and
every reason and reading the viewer starts with, there are events that hold an operator's Start,
and a state reached by them from that start state, that waits to spawn the first generation with
the launch the durable state admits (`Acorn.Host.Viewer.Core.start_spawns`). The proof's
witness is the Start and one tick, with every call between them succeeding. It is a statement of
existence: a Start whose intent cannot be written is another continuation and reaches no spawn.
The proof keeps a private property of a state and a launch (`Core.Poised`): a serving state with
no process, no replacement and its run directory, whose lifecycle has no Clear to go on with and
reserves its first generation at every instant, and whose durable state admits the launch. A
Start admits a reservation: for every identity, every intent native startup is given and every
instant, the lifecycle of native startup, after a Start request, reserves generation 1
(`Acorn.Host.Viewer.Lifecycle.start_reserves`), and the complete retry budget admits a
launch at every instant (`Acorn.Host.Viewer.Retry.initial_ready`). The state built when no
state file exists admits a launch, for every seed within the browser's integers and whether or
not a stray checkpoint was adopted (`Acorn.Host.Viewer.Core.unstarted_launch`). The seeds
the bootstrap uses are within them: a drawn seed is below `2 ^ 48`
(`Acorn.Host.Viewer.viewerSeed_bound`) and the seed beside an adopted checkpoint is 42.

The state file. `Acorn.Host.Viewer.stateSchema` is the schema version the viewer writes,
which is 2; from this version on, a viewer that finds no state file writes a stopped intent, and
before it the viewer wrote files with no `schema_version` member. The current state file has
eight members: its schema version, six of state and the record of the child of the viewer that
wrote it. The six are a seed and an agent epoch spelled as unsigned 64-bit integers, a run
identity of sixteen hexadecimal digits, an intent, an origin and the process flag. Strict JSON
syntax and exact integer admission precede identity construction. The state a viewer builds when
its run directory holds no state file (`Acorn.Host.Viewer.PersistedState.unstarted`) is a
new run of a fresh agent that intends to stay stopped, so the absence of a file gives the
supervisor no running intent; its second argument records that a stray checkpoint of an earlier
layout was adopted into the run. The version a state file names
(`Acorn.Host.Viewer.stateVersion`) is nothing when the member is absent or is not a number
spelled in decimal digits alone, which `Acorn.Digits.read` reads. The rule is about
spelling: a string, `null`, and a number spelled with a sign, a fraction or an exponent are all
read as no readable version. The child record a state file names
(`Acorn.Host.Viewer.stateChild`) is the words of its `child` member when that is a JSON
array of strings, and nothing when the member is absent or has any other form. Admission of the
version a state file names is decided once (`Acorn.Host.Viewer.admitVersion`): a natural
number other than the current version is refused, so that a file another version wrote is
neither guessed at nor overwritten; the current version and no readable version are admitted.
The fields of a state file (`Acorn.Host.Viewer.PersistedState.fields`) are its
`schema_version` member when it has one, whose value that admission has already judged, its
`child` member when it has one, and the six fields of state.

The complete state schema refuses unknown fields, partial identity and a schema version that is a
natural number other than the current one. For a file that is decoded, one decision
(`Acorn.Host.Viewer.PersistedState.admit`) gives both the state admitted and where its
intent came from (`Acorn.Host.Viewer.StartSource`). The intent the file records is kept
only when the file names the current version and names the child record of this launch, which
must have one: the saved intent was then written by a viewer whose supervisor would start the
same child. In every other case the state keeps every field but its intent, which is admitted as
stopped: a file whose version does not read as the current one, because it has no
`schema_version` member or one that is not a number spelled in decimal digits alone, which is
read as an earlier version's file whatever `child` member it holds (the viewer wrote none before
the file carried a version); a file whose `child` member is absent,
is not an array of strings or names another record; and any file read by a launch that has no
record. The intent is the one field whose value an operator may never have chosen, and the other
fields are kept as written. Where the state a viewer starts from came from is one of four cases.
The run directory held no state file (`Acorn.Host.Viewer.StartSource.absent`). The state
file's version does not read as the current one: an earlier version's file, whose intent was
read as stopped (`Acorn.Host.Viewer.StartSource.earlier`). The state file names the schema
this viewer writes and this launch's child, or records a stopped intent; its intent is the one
it records (`Acorn.Host.Viewer.StartSource.saved`). The state file names the schema this
viewer writes and a running intent that was not given for this launch's child: the file names
another child record or none, or this launch has none; its intent was read as stopped
(`Acorn.Host.Viewer.StartSource.other`). The state admitted from a state file
(`Acorn.Host.Viewer.PersistedState.decode`) is the first component of that decision, so
the state and the account of where its intent came from are one decision. A private lemma
(`PersistedState.decode_stopped`) says that a state the decoder returns intends to stay stopped
unless the file names the current schema and the child record of this launch.

The statements about the decoder in full are these. A state the decoder returns for a file whose
version does not read as the current one intends to stay stopped: for every child record a
launch may have, or none, every JSON value whose `schema_version` member is absent, is not a
number spelled in decimal digits alone or spells another number, and every state the decoder
returns for it (`Acorn.Host.Viewer.PersistedState.decode_earlier`). A state the decoder
returns for a file that does not name this launch's child record intends to stay stopped: for
every launch that has no child record, and every launch whose record differs from the one the
JSON value's `child` member names, or that reads a value with no such record, every state the
decoder returns for the value (`Acorn.Host.Viewer.PersistedState.decode_unbound`). The
decoder returns a running intent only under the current schema version and for this launch's
child: for every child record a launch may have, or none, every JSON value and every state the
decoder returns for it that intends to run, the value's `schema_version` member spells the
current version, the launch has a child record, and the value's `child` member names that record
(`Acorn.Host.Viewer.PersistedState.decode_running`). The decoder returns an error for a
state file that names another schema version: for every child record a launch may have, or none,
and every JSON value whose `schema_version` member spells a natural number other than the
current version (`Acorn.Host.Viewer.PersistedState.decode_other`). The decoder returns an
error for a state file whose schema version spells a number of `2 ^ 64` or more: for every child
record a launch may have, or none, and every JSON value whose `schema_version` member is a
number whose spelling `Acorn.Digits.read` reads as a natural number of `2 ^ 64` or more
(`Acorn.Host.Viewer.PersistedState.decode_wide`).

The child record. A word of a child record that the state file can hold as written is printable
ASCII with no quotation mark and no backslash, so its JSON spelling is the word between
quotation marks (`Acorn.Host.Viewer.childWordAdmitted`). The room a child record may take
in the state file, which a viewer reads within 4096 bytes, is 2048: the lengths of its words,
with three more for each word's quotation marks and comma
(`Acorn.Host.Viewer.childBudget`). A child record the state file can hold has at least one
word, every word admitted, within the budget (`Acorn.Host.Viewer.childAdmitted`). The
digest of a file's content (`Acorn.Host.Viewer.fileDigest`) is 64-bit FNV-1a over every
byte, in order, a function of the bytes alone: Landon Curt Noll, Kiem-Phong Vo, Donald Eastlake
3rd and Tony Hansen, The FNV Non-Cryptographic Hash Algorithm, RFC 9923 (2026), sections 2 and
5; the step and the offset basis are those of `lean/Acorn/Rng.lean`. It tells two files apart
against accident and not against forgery. What a viewer reads of the file of the program its
supervisor would start (`Acorn.Host.Viewer.ProgramReading`) is the length of the file in
bytes and the digest of every byte of the file, in order. It is a function of the bytes read
alone, so it does not depend on what the state file can hold;
`Acorn.Host.Viewer.ProgramReading.of` is the reading of a file's content, read whole. The
record of the child a viewer's supervisor would start (`Acorn.Host.Viewer.childRecord`)
holds, as far as the viewer can read it before it starts it, the executable's path, the length
in bytes and the digest of the content read from the file at that path, and the argument vector
at a fixed reference launch (`Acorn.Host.Viewer.referenceLaunch`). At that launch the
words that carry the run's identity take fixed values, since the identity the state file holds
decides them at each launch. Two launches have the same child, for the purpose of a saved
running intent, exactly when both have a record and the records are equal word for word, so two
files of equal length and equal digest are taken as one. A launch has no record when sameness
cannot be established: a command given to a shell, whose process depends on the working
directory, the environment and the files the command names; an executable whose file cannot be
read whole; or words the state file cannot hold. The `child` member of a state file
(`Acorn.Host.Viewer.childText`) is the record's words as a JSON array of strings, and
`null` when the launch has no record or its record cannot be held. Serialization
(`Acorn.Host.Viewer.PersistedState.encode`) contains only closed spellings, numeric digits
and the admitted words of the child record of the viewer that writes it.

Reading and writing the file. Missing files and refused files have different result
constructors, so a caller cannot mistake a parse failure for a successful restore
(`Acorn.Host.Viewer.StateRead`): the run directory holds no entry named `state.json`
(`Acorn.Host.Viewer.StateRead.missing`); IO, syntax or schema refused the prior file, an
entry that cannot be opened included (`Acorn.Host.Viewer.StateRead.refused`); or the
complete state was admitted, with where its intent came from
(`Acorn.Host.Viewer.StateRead.restored`). The read
(`Acorn.Host.Viewer.RunDirectory.readState`) is bounded and preserves the distinction
between missing and malformed state. Only the absence of the directory entry, which Lean's
symlinkMetadata reads without following a symbolic link, is a missing state. An entry that
exists is opened only when it is a regular file, or a symbolic link that leads to one (Lean's
metadata follows links): anything else, such as a link whose target is gone, a directory, a pipe
or a device, is refused before it is opened, so the read never waits on an entry that cannot
supply a finite document. The two looks and the open are separate calls, so this rests on the
run directory's stable-path assumption like the rest of the reader. Every state the actor writes
goes through `Acorn.Host.Viewer.RunDirectory.writeState` with the record of its own
configuration's child. Publication uses an exclusively created temporary file under the run
directory's IO mutex and renames it onto `state.json` after a complete write and flush: failures
before the rename never replace the target, whereas an indeterminate rename error can leave
either the original or the newly renamed entry. Filesystem stability and POSIX rename remain the
run directory's trust boundary; no power-loss durability is claimed.

The actor. What the actor compares before it starts the configuration's child is
`Acorn.Host.Viewer.ChildProgram`. The bootstrap builds the constructor from the launch
itself, `Acorn.Host.Viewer.ChildProgram.ranked` for the core beside the viewer and
`Acorn.Host.Viewer.ChildProgram.fixed` for a command given to a shell, so the two are told
apart by construction and not by whether the state file can hold a record of the child. A fixed
command is spawned with no reading. The ranked constructor holds what this viewer read of the
executable's file when it started, none when the file could not be read whole, and the one
action that reads it. The bootstrap ran the action for the first and the actor runs it again
once before every start, before the launch is recorded, so what is compared was read the same
way. The configuration holds the record of the child it starts
(`Acorn.Host.Viewer.SupervisorConfig.child`), written with every state this viewer saves,
and none when sameness with another launch's child cannot be established or the state file
cannot hold the record; the comparison before a start does not read it. It also holds what the
actor compares before every start of the child
(`Acorn.Host.Viewer.SupervisorConfig.program`). The three refusals of a start of the
ranked core are texts: its file reads now but not as it read when this viewer started
(`Acorn.Host.Viewer.childDiffers`); its file cannot be read whole now, though it could
when this viewer started (`Acorn.Host.Viewer.childUnreadable`); its file could not be read
whole when this viewer started (`Acorn.Host.Viewer.childUnread`). Each says what clears
the refusal and directs no run. A private function of the actor (`Supervisor.refusal`) gives why
the configuration's child may not be started now, and nothing when it may. A fixed command is
never refused there. The ranked core is refused when its file could not be read whole when this
viewer started, cannot be read whole now, or reads now otherwise than it did then, whether or
not the state file can hold a record of the child. The actor asks once before each start, the
first and every restart, before the launch is recorded.

Each case of the actor's call (`Supervisor.call`) performs the native operation its call names,
except that before recording a launch it checks `Supervisor.refusal` first.
The reading is made before the launch is recorded, when the call's argument says the state to
write is the one that marks a launch as attempted (`Acorn.Host.Viewer.Pending.launch`). A
refusal there writes nothing and spawns nothing: the call's result is the write's error with the
reason, which the step treats as a launch that could not be recorded, so the run stops. Every
refusal is printed on standard error and reported in the page by the step, as the reason of the
failed call. The actor hands the step an operator's Start only for a Start queued by
`Acorn.Host.Viewer.Supervisor.submit` (the `--start` flag) or
`Acorn.Host.Viewer.Supervisor.submitControl` (the HTTP control endpoint),
and the bootstrap passes the state it built
or read to `Acorn.Host.Viewer.Supervision.start`. The supervisor is constructed
(`Acorn.Host.Viewer.Supervisor.new`) only after the bootstrap has admitted the initial
state. A state built with no state file, or read from a file of the current version with the
intent that file records, is published there, before the listener binds. A state read from an
earlier version's file, whatever intent it records, or from a file of the current version whose
running intent was given for another child, is not published there. A launch relies on no unpublished state either way, since the attempted launch
is saved before the spawn. The first control record is the start's.

The bootstrap. The bootstrap admits configuration and durable state, binds loopback HTTP, then
drives the serial supervisor. It gives the supervisor a running intent only from a state file
that holds one, names the current schema and names the record of the child this launch starts.
The one reading of the ranked core's program (readProgram in `lean/NativeApp/Viewer.lean`) is
the length and the digest of the content read whole from the file at the executable's path, and
none when the file cannot be read whole. The bootstrap's configuration of the supervisor
(supervisorConfig in the same file) gives the supervisor's child, what is compared before it is
started, and its record. The ranked child is the core beside the viewer's program, named by its
path with explicit arguments. The configuration holds the action that reads its file and the
reading that action gave at start. The comparison is held in memory and does not depend on the
record, on the run directory's path or on what the state file can hold. The record written to
the state file is the path, that reading and the arguments at the reference launch, and none
when the file could not be read or the state file cannot hold those words. Whether the viewer
leaves the state file as it is until its listener is bound is
`Acorn.Host.Viewer.StartSource.kept`. The one line that says why the run a viewer starts
with is shown stopped, and nothing when it is not, is `Acorn.Host.Viewer.startAccount`,
so a person who finds the run stopped is told why and what starts it. The relay of standard
input under `--control-stdin` is `/bin/cat` (`Acorn.Host.StopFlag.withCommands`).
