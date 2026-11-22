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
available. The bootstrap status that decides this builds nothing, writes only the
launcher's own override file and asks Lake whether the FloatLib modules the proof
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
empty `.acorn-launch/` directory, then rerun the launcher with the options it
was first given; in work on a change, a rerun that launches needs the owner's
authorization as the first launch did. Preserve `acorn-run/`.
Do not manually launch another viewer against a directory already in use.

### Build and verification failures

If a tool is missing, install the named prerequisite before retrying, under the
condition on installing that [platform setup](#platform-setup) states. On macOS,
check that `xcode-select -p` points to an installed, usable developer toolchain.
If verification reaches its 360-second deadline, retain the failing command
and diagnostic for a focused report; do not raise the limit or treat a partial
run as a pass. Run the complete command to check all verification owners.

## Compiler and execution boundary

Every discovered Lean source must be a module of the libraries Acorn,
AcornVerif, NativeApp, AcornDocument or Entry, which Lake's globs assign, or a
listed tool module. The [Regula audit](#regula-audit) claims the first four with
Bootstrap; Entry holds the executables' roots. Every retained native target is
built and checked against Lake's evaluated targets and compiled entry owners;
each executable root must be a maintained module with a non-empty module
docstring. Ownership admission refuses a facet-qualified build key in the root
package's Lake configuration. The [Lake configuration](../lean/lakefile.lean)
documents the restriction and its pinned-Lake rationale. Before any Lake
command, `Bootstrap.lean` must elaborate with no message, and Lake runs with
`--wfail`, so any warning, including a header-time warning such as a deprecated
import, fails the build. Source/compiled admission checks imports, capability
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

The build tools discover every Lean source below lean and check explicit
inventories of the tool modules and of the native entries. Runtime `--research-profile` selects
agent mechanisms; it does not change verification. Resource, route and compiler
flag admission, browser byte generation, corpus and declaration checks always
run. Missing files fail admission.

Numerical proofs use the executing Lean definitions. Native admission checks
their compiler IR, primitive calls, resource contracts and compiler flags.
Primitive IEEE interpretation remains a native assumption.

The merge gate is `./scripts/gate.sh`. The no-mistakes pipeline runs it
(`.no-mistakes.yaml`) before a pull request opens, on the exact commit it
validates, in a checkout that holds only tracked files. GitHub runs the same
script at each event that gives a pull request its head, within the limits
described after the frame check below. The gate provisions the pinned dependencies,
then runs the command twice, from cold project outputs, each run under its own
360-second deadline. The first, `./scripts/verify.sh build-executing`, admits the
sources as the complete command does, then selects every module outside the proof
library `AcornVerif` except `AcornTools.AxiomPins`, and every executable. It builds
these targets and their dependencies, with native objects where applicable, and
admits nothing after the build. The axiom pins import the proof library, so they
remain in the second stage despite belonging to the tools. The second is the
identical complete command, which selects every discovered module: Lake
reuses an output of the first only where its trace matches the checked-out
source, toolchain and options, and builds the rest. So in the gate the cold
build and the checks no longer share one deadline: the first bounds the build of
the executing library, the tools except the axiom pins, and their dependencies;
the second bounds the remaining proof build, the axiom pins and every check.
On a four-processor machine the cold build with the checks beside
it inside one deadline left too little margin. The gate then runs the
[Regula audit](#regula-audit), lean-intent's two checks and the frame
check on the same commit, each also when an earlier step failed, and passes only
when both runs, the audit and the checks pass. When ordinary verification
passed, lean-intent's two checks and the frame check run one after another in a
background subshell beside the Regula audit, because every module and executable
is already built and all three read the finished build without writing to
`lean/.lake/`; when verification failed, all three run one after another.

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
value. The check lists that directory and admits only regular files ending in
`.lean` and regular files ending in `.frame`; any other entry, a subdirectory or
a symbolic link included, fails it and is named. The check reads declarations
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
refused as no source of this package, and an entry below the package directory
that is neither a directory nor a regular file fails the inventory and the
check with it. The command that prints a pin file requires the same things
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

The pipeline stores the provisioned dependency checkouts and their build outputs
once for each default-branch commit a run starts from, and gives a run a private
copy only while the run's toolchain and lock files equal that commit's; Lake
rebuilds whatever its traces do not show current. Acorn's own outputs are never
carried from one run to another.

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
and never falls back to the merge of the head with its base. From that checkout
it runs `./scripts/gate.sh provision` to provision the pinned dependencies, then
`./scripts/gate.sh` to run the same gate as the pipeline's Test step.
No step of the workflow names a Lake target, a module, a package or another
script of the project, so the job relies on the
head only for that script and its two forms. So the dependencies and the checks
on GitHub are the script's own, with no second list to keep equal to it, and a
head whose script or Lake configuration is older or newer than the one on main
is provisioned and checked by its own. A failing check fails the job, and the
job's result is shown on the pull request. The job
runs for a pull request to any base branch, so that one later retargeted to main
keeps the run made on its head, and nothing runs after a merge.

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
`gate: lean-intent checks exited N; frame check` and `gate: frame check exited N`
(when verification passed, those last three lines are printed in order once both
the Regula audit and the background subshell finish).
It prints `gate: every merge check passed` last, and only when every status
is 0. A head that holds another revision of the script runs that revision's
checks and prints that revision's lines, which the head's own `scripts/gate.sh`
gives: a revision from before the frame check prints no line for it.

For each check, the only evidence that it ran on the head and failed is a
`gate:` line that reports its exit status as other than 0, and the only evidence
that it ran and passed is such a line with the status 0. The only evidence that
every check of the head's script passed is the line
`gate: every merge check passed`. Each attempt of a run is read by its own log.
In the attempt being read, a check with no line that reports its status has no
verdict, and an attempt without the passing line is no pass of the gate. So an
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

**Module inventory: the tools refuse more.** Lake's glob decides which library has
a source. A new source below Acorn, AcornVerif or NativeApp is therefore a module
of that library, the claim covers it, and Acorn's boundary predicates class it by
its name. The tools keep no written list of these modules. A new source below
`lean/AcornTools` is a module of a tool library outside the claim: ownership
admission requires each discovered source outside the five libraries that Lake's
globs assign to be an entry of `toolingModules`, and each entry to be a source. A
source below lean that no library has is outside the claim unless a claimed
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
what the report or short review holds and when work is complete. The gate establishes that the
proofs of a change are sound and that its checks pass on a commit. It
establishes nothing about whether a theorem states what its pull request
claims, which the referee reads, and nothing about whether a referee or a
reviewer was assigned as the protocol requires. The trace of the protocol is the pull
request itself: the comment that records the assignment and each referee's
report or short review. One GitHub account serves the owner and the organization's agents, so under
individual maintainer-led assignment GitHub does not show that the agent that
assigned a referee or a reviewer is another than the one that did the work; the
assignment comment states who assigned. Under the single-maintainer interim
provision (confirmed on 2026-11-21 while Acorn has one human maintainer), a
truthful assignment comment can instead record the owner's standing designation
of the no-mistakes validation pipeline's external analyzer/verifier, its model
family, and the exact head commit without identifying a separate per-PR
assigning agent, alongside its unedited exact-head report or short review. The
provision prohibits same-family self-review (disqualifying that model if chosen
for author-side review, advice, writing or fixing while permitting re-reads
after findings issued in its designated referee/verifier role), falls back to
another model family or an uninvolved person under the general rule when
disqualified, and retires once Acorn has more than one human maintainer; no
check enforces model-family separation, designated-role vs. author-side advice,
or multi-maintainer retirement, leaving those checks as accepted risk in the
written protocol. A
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
gate with its own bound; the deadline is not raised. Verification also admits the site's source
inventory and requires `site/lake-manifest.json` to lock every dependency of
`lean/lake-manifest.json` to the same revision, because both packages share one
set of dependency checkouts.

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

Every decision the supervisor makes about the core process and the run's published state is
made by one pure step, `Acorn.Host.Viewer.Supervision`: a closed state, the events the native
actor `Acorn.Host.Viewer.Supervisor` hands it, and one step per event or per outcome of the call
it waits for, which returns the next state and the effects to perform. The actor reads the
world, performs the effects in order and then the call, and hands the call's outcome back before
it reads anything else; it is effects, with no theorem of its own. A supervision is sealed by
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
installs a run other than the one it retires (`Acorn.Host.Viewer.Core.replaced_identity`); and
every result first installs its own lifecycle and publishes its control record from it
(`Acorn.Host.Viewer.Stepped.effects_settle`). The operating system's process, signal and wait
semantics, the file system's durability, the Lean runtime's IO, mutexes and clock, the identity
a core reports, and the actor's mapping of each effect to the native operation it names remain
the trusted base.

The viewer starts its core only on an explicit act: the `--start` flag, a Start the page
sends, or a state file whose running intent an earlier Start set. The state the bootstrap builds
when the run directory holds no state file intends to stay stopped
(`Acorn.Host.Viewer.PersistedState.unstarted`). For every Clear configuration, every durable
state that intends to stay stopped, and every state reached from the start on it by steps on
events that hold no operator's Start and by outcomes of the pending calls: the lifecycle admits no
reservation at any instant and intends to stop, and the call the state waits for, if any, is no
spawn and writes no state that intends to run
(`Acorn.Host.Viewer.Reached.stopped_spawns_nothing`;
`Acorn.Host.Viewer.Reached.unstarted_spawns_nothing` states it for the state built with no
state file). The states reached from a start by steps and outcomes are the states of a run and no
others
(`Acorn.Host.Viewer.Reached.ran`, `Acorn.Host.Viewer.Ran.reached`). The statement is not
empty: from the start on every durable state that admits a launch, there are events that hold a
Start and a state reached by them that waits to spawn the first generation
(`Acorn.Host.Viewer.Core.start_spawns`), and the state built with no state file admits a launch
for every seed within the browser's integers (`Acorn.Host.Viewer.Core.unstarted_launch`). The
control record of the start on the state built with no state file says the run is desired
stopped and actually stopped (`Acorn.Host.Viewer.Core.start_control`). A state file whose
schema version does not read as the current one, because the member is absent, is not a natural
number or spells another number, is decoded with intent stopped whenever it is decoded
(`Acorn.Host.Viewer.PersistedState.decode_earlier`), so the decoder returns a running intent
only under the current version (`Acorn.Host.Viewer.PersistedState.decode_running`), and the
statement above holds of the supervisor started from what such a file decodes to
(`Acorn.Host.Viewer.Reached.earlier_spawns_nothing`): before the file carried a version, the
viewer wrote a running intent in it when it found no file, with no Start, so such a file cannot
show that a Start set its intent. The viewer publishes the state it starts from, in the schema
it writes, before it supervises, so the file names the schema from then on; this is read from the
actor and not proved, and so is that the text the viewer writes reads back as the state written.
Three more things are read
from the code and not proved: the actor hands the step an operator's Start only for a command
that was submitted to its queue, which the bootstrap does for the `--start` flag and the HTTP
server for an admitted control request; the bootstrap hands the supervisor the state it read or
built; and a state file it refuses constructs no supervisor. That a running intent in a state
file follows a Start in some earlier viewer is argued from the write clause above by induction
over the viewers that owned the run directory, and is not proved.

The cases of a state file are four. With no file the run is stopped. A file whose schema version
is absent or is not a natural number is read as an earlier version's file: stopped, once, as
above. A file that names the schema version the viewer writes
(`Acorn.Host.Viewer.stateSchema`) starts the run with the intent it records, so a running one
resumes. A file that names another natural number is refused by the decoder
(`Acorn.Host.Viewer.PersistedState.decode_other`), like an unreadable or malformed one: the
viewer exits before it serves anything, constructs no supervisor and leaves the file as it is,
because a file another version wrote is not guessed at and reading it as stopped would publish
over it. Whenever the run a viewer starts with is shown stopped, the viewer says why in one line
(`Acorn.Host.Viewer.startAccount`): on its standard output, before it publishes its start
state and so before an earlier version's file is replaced, and as the reason of its first
control record. It says nothing when the run is not shown stopped, as when it was launched with
the `--start` flag or resumes a running state.

The statement starts from a durable state that intends to stay stopped, so it does not cover a
Stop that the viewer has acknowledged but not yet written to its state file when the viewer
crashes, or whose write failed: the file then still says running, by the earlier Start, and the
next viewer resumes it. Holding the acknowledgement of a Stop until it is written would close
that window and is a change to the control interface. Nor does it say who may submit a Start:
the viewer serves its page on the loopback interface to whoever loads it.
