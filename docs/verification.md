<!-- Generated from site/AcornDocs/Verification.lean by ./scripts/verify.sh site write. Edit that source, not this file. -->

# Verification

This guide describes Acorn's compiler, proof and execution checks. Each theorem
states the property and assumptions it checks. For installation and a first run,
start with the [README](../README.md#start-with-the-live-viewer).

Run `./scripts/verify.sh` in the actual Git checkout after provisioning the pinned
Lean, Mathlib, FloatLib and Verso dependencies, a C compiler, OpenSSL 3, ShellCheck
and GNU coreutils.
Each run of the command has a hard 360-second deadline, which includes the
project compilation the run does and every ordinary check; from cold project
outputs that is the whole build. [CI](#build-and-source-inventory) splits the
cold build over two runs, each with its own deadline. The deadline uses
process-group SIGKILL with no grace period or budget override; missing, skipped
or timed-out checks fail. OS scheduling and signal delivery are the trusted
mechanisms that enforce this deadline.

Project instruction changes have no live Acorn runtime surface. The complete
verification command remains required for documentation changes.

## Platform setup

Use `./scripts/start.sh` for automatic setup and launch, or
`./scripts/start.sh --prepare-only` to prepare and build without learning.
It uses Homebrew on macOS and apt-get on Ubuntu/Debian. It installs missing
prerequisites and provisions the pinned Lean, Mathlib and FloatLib dependencies;
repeat launches use the offline bootstrap when those dependencies are already
available. The bootstrap status that decides this builds nothing, writes only the
launcher's own override file and asks Lake whether the FloatLib modules the proof
bridge imports and the Regula modules the decision registries import are current.
The first setup may need network access, a package-manager password prompt or
the macOS command-line tools installation dialog. It never runs Acorn as root
and does not change the global Xcode selection or Lean default toolchain.

The [CI workflow](../.github/workflows/verify.yml) runs on GitHub's standard
`ubuntu-24.04` x64 image. It installs no system package: it admits by name the
packages that image provides, and takes elan from a release pinned by the SHA-256
of its archive, which the dependency cache keeps. Every workflow step that
reaches the network has its own time limit, so a stalled download fails that
step. Dependency caches include the Ubuntu release and runner architecture.
Automatic local setup supports macOS and Ubuntu/Debian Linux.

For manual setup, install macOS command-line tools and the packages below
([Homebrew installation](https://brew.sh/)):

```sh
brew install coreutils shellcheck openssl@3 elan
```

For Ubuntu, install:

```sh
sudo apt-get update
sudo apt-get install -y build-essential curl git libgmp-dev openssl shellcheck coreutils elan
```

Ensure Lean and Lake are available in your shell, then run
`(cd lean && lake exe cache get && lake build Mathlib regula/lint regula/axiomGate floatlibBridge regulaInterface)` from the
repository root to provision the pinned toolchain/dependencies; the build compiles
only Mathlib modules absent from the upstream cache, plus Regula's lint driver
and audit worker. FloatLib publishes no cache, so the same command compiles the
FloatLib modules that the proof bridge imports, and the two Regula interface modules
that the decision registries import.
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

`./scripts/start.sh --no-browser` prints the actual bound loopback URL.
`--run-dir DIR` selects another run directory and `--port N` selects a port;
the default port is allocated by the OS. Browser opening is optional and its
failure does not stop the agent. Use `./scripts/start.sh --help` for the launcher
options. Raw viewer options are documented in [the viewer specification](viewer-ux.md).

### Interrupted-launch recovery

The launcher keeps `.acorn-launch/` outside the run directory so that Clear
cannot remove its ownership lock. An ordinary exit removes the lock. A forced
termination or machine crash may leave it behind. A second launcher refuses
to displace an uncertain owner.

Read `.acorn-launch/pid` and inspect that process and its viewer/core descendants.
Only after confirming that no process still owns this run, remove the lock's
temporary files (control, pid and installer.sh) and the
empty `.acorn-launch/` directory, then rerun the launcher. Preserve `acorn-run/`.
Do not manually launch another viewer against a directory already in use.

### Build and verification failures

If a tool is missing, install the named prerequisite before retrying. On macOS,
check that `xcode-select -p` points to an installed, usable developer toolchain.
If verification reaches its 360-second deadline, retain the failing command
and diagnostic for a focused report; do not raise the limit or treat a partial
run as a pass. Run the complete command to check all verification owners.

## Compiler and execution boundary

Every discovered Lean source must be a module of the libraries Acorn, AcornVerif or
NativeApp, which Lake's globs assign and the [Regula audit](#regula-audit) examines,
or a listed tool module. Every retained native target is built and checked against
Lake's evaluated targets and compiled entry owners; each executable root must be
a maintained module with a non-empty module docstring. Ownership admission
refuses a facet-qualified build key in the root package's Lake configuration.
The [Lake configuration](../lean/lakefile.lean) documents the restriction and its
pinned-Lake rationale.
Before any Lake command, `Bootstrap.lean` must elaborate with no message, and
Lake runs with `--wfail`, so any warning, including a header-time warning such
as a deprecated import, fails the build. Source/compiled admission checks
imports, capability owners, artifact origins and native routes. The Regula audit, not
ordinary verification, checks the axioms that each declaration of the claimed
libraries depends on. The theorem inventory counts the theorem declarations and
refuses a native replacement. Every proof passes through the kernel.

The modules that compose the agent import no world. Source and compiled admission
refuse a declared module that imports a host module, or references a declaration
owned by one, unless it is one of a world's own declared modules. The grid world's are
Acorn.Handcrafted.Observation, Acorn.Handcrafted.Cumulants and Acorn.Handcrafted.GridWorld. The Microduck
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

No theorem states that every number of a parsed text is read: that rests on the parser,
which builds a number in one place, from the spelling of a scanned numeral.
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
that send (`Acorn.Host.Microduck.Command.line_asked`). This is the one theorem about
the parser. No theorem states what it reads of a line of a daemon, and none is about what a
daemon sends or accepts, so none states that the text of a frame is read correctly.

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
reviewed build/gate tools, cryptographic tools and OS remain trusted boundaries.

## Build and source inventory

The build tools discover every Lean source below lean and check explicit
inventories of the tool modules and of the native entries. Runtime `--research-profile` selects
agent mechanisms; it does not change verification. Resource, route and compiler
flag admission, browser byte generation, corpus and declaration checks always
run. Missing files fail admission.

Numerical proofs use the executing Lean definitions. Native admission checks
their compiler IR, primitive calls, resource contracts and compiler flags.
Primitive IEEE interpretation remains a native assumption.

CI provisions dependencies separately and runs the command twice in one job on
one runner, from cold project outputs, each run under its own 360-second
deadline. The first, `./scripts/verify.sh build-executing`, admits the sources as
the complete command does, then builds every module outside the proof library
`AcornVerif` with its native object, and every executable; it admits nothing
after the build. The second is the identical complete command: Lake reuses an
output of the first only where its trace matches the checked-out source,
toolchain and options, and builds the rest. So in CI the cold build and the
checks no longer share one deadline: the first bounds the build of the
executing library and the tools, the second the proof library's build and every
check. The job passes only when both runs pass. The cold build keeps all four
processors of the runner busy, and with the checks beside it inside one deadline
a slow runner left too little margin. No output is carried from one CI run to
another. A second job runs the [Regula audit](#regula-audit) on the same head,
from cold project outputs. The workflow has read-only repository permissions, no
secrets, no privileged pull-request trigger, and pinned action revisions. Both
jobs must pass on the exact proposed head before merge.

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
native, browser-kernel, ownership and site admission after it. Each of these
prints the output of a step whole when the step ends, and all of them are reaped
before a failure is reported. The build requests modules first and executables
after them. An executable whose Lake configuration names another target it needs
is held back with its root module: both are requested after every other module
and executable, because Lake waits for that target before it reads the next
request, so every other job is scheduled first. Each compiler process of the
build uses at most two threads, where the default is one for each processor;
this limits how far the processes Lake runs at once compete for the same
processors.

## Regula audit

[Regula](https://github.com/rbeauchamp/regula) is a strict linter for Lean with a
published standard. Acorn requires the release pinned in `lean/lakefile.lean` and
starts its lint driver through the offline bootstrap:

```sh
./scripts/lean.sh lint
```

Only that outer lint command goes through the bootstrap. Regula's driver then
runs Lake itself to build, query and enter the workspace environment, without
the bootstrap's path overrides or its no-cache and warnings-as-failures flags.
Those invocations resolve dependencies through the Git lock in
`lean/lake-manifest.json`. The bootstrap checks no dependency's revision: it
admits each by the presence of its files, and the FloatLib modules the proof
bridge imports and the Regula modules the decision registries import by Lake's
build traces. Lake therefore fetches a dependency whose
checkout is not at the locked revision.

The command exits 0 when the audit is accepted, 1 on a violation, 2 on an invalid
configuration and 3 when the audit is incomplete. Regula writes scratch copies
of Lean sources to .lake/regula-scratch under
lean; a killed run leaves them until the next Regula run removes them. Git ignores
.lake, and the module inventory, the native source inventory and the corpus walk
skip it as Lake's build directory.

`lean/foundation_manifest.json` states what is audited. A claim names the
strongest axioms any declaration of a library may depend on. Acorn, AcornVerif,
NativeApp and Bootstrap, with the twelve application executables, claim Regula's
standard-logical profile: propext, Quot.sound and Classical.choice, and no other
axiom. No stricter profile is attainable, because Lean's core definitions of
binary32 and binary64 arithmetic depend on Classical.choice, as do the Mathlib
analysis in AcornVerif and the core string and JSON operations that Bootstrap
uses. Acorn, NativeApp and Bootstrap claim compiled code in
Regula's checked mode: the audit fails on any extern, replacement, unsafe or
partial boundary that their compiled code reaches outside the Lean toolchain's
own trusted base. AcornVerif claims report mode, where each boundary is reported
and not failed: its compiled definitions reach the recursors that Mathlib
compiles for Bool, List and Option, boundaries Mathlib owns, so checked mode
rejects them. One bridge module in AcornVerif is the only importer of FloatLib,
a proof dependency whose theorems use the same three axioms and whose compiled
functions reach the same Mathlib-owned boundaries; the boundary audit refuses a
FloatLib import by any executing module. The compiler, native runtime, operating
system and spawned processes stay trusted in both modes. AcornTools is excluded
with the six tool executables; it is the reviewed tooling trust boundary.

`lean/Acorn/Decisions.lean` registers the library's decision functions for which
a property of the accepted or refused result is proved. A decision function is
an admission, parser or validity test: its result accepts or refuses an input. A
registration is a Regula executable contract about the executing definition
itself, with the kind its proof establishes. A two-way kind states that the
function accepts exactly the inputs that satisfy the written specification, with
one accepted and one refused input as witnesses. Regula's decision attribute
makes the contract a requirement of the function, so the audit fails when a
contract is removed while its function stays registered. A decision procedure
whose result type is `Decidable` carries both directions in its type and is
registered with no contract. An admission with an argument or result type that
depends on an earlier argument, and a decision that takes its element type as an
argument, carry a kind in the forms that Regula reads for them. The kind is
stated about the function applied to every field of a structure of its arguments
and, where the result type depends on the input, about whether the result holds
a value, with the value forgotten. A statement of the value of an accepted
result stands beside such a kind as a requirement with no kind. A function keeps
a requirement with no kind where no kind is true of it or where Regula refuses
the kind, and the ownership audit requires the contract by name. The module
documentation of `lean/Acorn/Decisions.lean` gives the four reasons: a function
that accepts every input or whose accepted inputs no theorem states; an input
that holds a state whose invariant names tests that the function runs ([Regula
issue 270](https://github.com/rbeauchamp/regula/issues/270)); a specification
about a function with such tests; and kinds that are stated in the proof
library, which Regula does not count toward a registration ([Regula issue
271](https://github.com/rbeauchamp/regula/issues/271)). A requirement with no
kind is a statement that the Regula audit does not examine: that audit checks
only that its theorem is proved about the executing definition. Such a statement
can fix one direction only, and it need not show that both outcomes occur for
its function. Kinds for the functions of the second and the third reason are
remaining work of [issue 105](https://github.com/rbeauchamp/acorn/issues/105). A
contract states only what its theorem proves.

A kind compares a function with its specification as the two are defined now.
Where the two call one test, a defect of that test changes the two sides
together, and the proof of the kind can stay valid.
[RG1009](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1009/) therefore
refuses a contract with a kind whose specification reaches a test that the
function or the acceptance predicate also reaches. A test is a function with a
result of `Bool`, or a definition of an instance of BEq, Lean's class of
equality tests, outside Lean's own library. The projection function of a
structure field is no test, whatever the type of the field: it reads stored
data. The rule reads the specification at any depth. Acorn states each such
condition as a proposition, with a theorem that connects the test with it:
`Binary32.Negative` for the sign bit, `Binary32.IsNaN` and `Binary64.IsNaN`, the
strict orders `Binary32.Less` and `Binary64.Less`, `Host.TileKind.Walkable`,
`Host.Inventory.Owns`, `Host.InBox` and `FeatureProfile.Resumable`. A function
that a specification reaches, such as the signed key `Binary32.key`, decides the
proposition through an instance that runs the test, so the executed comparison
is the same one. The rule compares names: it does not find a copy of a test
under a second name. It refuses nothing for a projection function, so
`inventory_craft` is not refused for the fields `Host.Inventory.axe` and
`Host.Inventory.boat`, which its specification and its function both read. It
refuses nothing for a shared function with another result than those two, such
as `Binary32.key` or `Host.terrain`. Those functions stay a matter of review.
For a contract with a kind, the account of the audit names each such function
where the specification reaches it first. It does not name a function that the
specification reaches only through a named one, and it does not name a
projection function. The module documentation of `lean/Acorn/Decisions.lean`
names each proposition with its theorem.

Regula's audit does not find a decision function that is not registered, and no
check of Acorn does. The module documentation of `lean/Acorn/Decisions.lean`
lists the groups of definitions with a `Bool`, `Option`, `Except` or `Decidable`
result that carry no contract, with the reason for each group. That list has no
check of completeness: a new definition with such a result can arrive with no
contract and no entry. A report of the definitions with no contract is work of
Regula ([issue 115](https://github.com/rbeauchamp/regula/issues/115)).
`Acorn.Decisions` cannot register a function of another library, such as a
NativeApp parser. No kind says that a specification is the intended one.
`Acorn.Decisions` belongs to the Acorn library because Regula decides a
registered function against the contracts of the function's own library. It is
the only module that imports Regula's decision attribute. No module imports it,
so no entry point links what it declares; the boundary audit admits it with the
proof sources and refuses an import of it. `AcornVerif.Decisions` states the
contracts whose proofs need the proof library. Regula does not count them toward
a registration, so their functions are not registered, and the ownership audit
requires each contract by name. Among them are the certificate checkers. No
checker is complete, so each contract states what an accepted certificate
establishes: the blocked checker and the stance checker carry the sound kind.
The replay checker keeps a requirement with no kind, because its specification
is about runs of the executed world step, which the checker runs. The module
documentation of `lean/AcornVerif/Decisions.lean` lists the functions of that
module that keep no kind, with the reason for each and which of them are also
remaining work of issue 105.

The driver builds every claimed module with warnings as failures, then inspects
the compiled environments. It rejects holes, project axioms, unsafe or partial
definitions, an axiom outside the claim, a module that no library includes, and
a claimed target whose Lake options weaken the required set. That set turns
automatic implicits off and turns on the missing-docstring linter and Mathlib's
standard linter set, whose header linter checks each module's copyright and
license lines.

The audit is a second required check and is not part of `./scripts/verify.sh`.
It compiles the claimed modules again and replays them in the kernel, which does
not fit beside the ordinary checks inside the 360-second deadline. CI requires
the job of the audit beside the job of ordinary verification before a merge. An
accepted audit covers Regula's mechanical rules for the claimed surfaces; it does
not replace review.

### What Regula checks in place of Acorn's tools

Acorn's tools under `lean/AcornTools` are outside the claim, so no proof covers
them. They check a compiled declaration or the Lake configuration only where no
Regula rule refuses at least the same inputs for the same libraries. Each
paragraph below takes one property: the rule of the pinned Regula release, the
libraries that the rule covers under `lean/foundation_manifest.json`, and what
the tools check. Where the tools refuse more, the paragraph gives an input that
shows it, and that check stays.

Ordinary verification alone therefore does not refuse a project axiom, a
dependency on an axiom outside propext, Quot.sound and Classical.choice, a
compiler-trusting proof, or a compiled unsafe or partial declaration. The Regula
audit refuses each of them, and its CI job is required. Run
`./scripts/lean.sh lint` for it before proposing a change to a Lean source.
Ordinary verification still refuses the words `axiom`, `sorry`, `unsafe`,
partial and `native_decide` in every executing and proof source, through source
admission, and a proof hole through the build, where a warning is an error.

**Project axioms.** [RG1001](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1001/) refuses an axiom declared in a module of Acorn,
AcornVerif, NativeApp or Bootstrap. The tools make no such check. A check over
the compiled declarations of the project modules covers Acorn, AcornVerif and
NativeApp, so Regula is stronger: it covers Bootstrap as well.

**Axioms that a declaration depends on.** [RG1003](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1003/) refuses a declaration of
those four libraries with a transitive axiom outside propext, Quot.sound and
Classical.choice. [RG1005](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1005/) refuses one whose axioms exceed the claim of its
library, which is the standard-logical profile for each. Both rules examine every
declaration: theorems, definitions and instances. The tools make no such check.
A check over theorems examines fewer declarations, so Regula is stronger. The
proof module AcornVerif.Axioms still pins the exact axiom sets of selected
theorems in the build.

**Proof holes and compiler-trusting proofs.** [RG1002](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1002/) refuses a declaration
that depends on Lean's proof-hole axiom, directly or through an import.
[RG1004](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1004/) refuses a declaration that depends on a native proof: the axiom
that `native_decide` or a related tactic adds, or one of Lean's three
compiler-trust axioms. Both rules read the transitive axiom set, which holds
every such axiom that a declaration names. The tools make no such check. A check
of the constants that a declaration names directly refuses fewer declarations,
so Regula is stronger.

**Unsafe and partial declarations.** [RG1006](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1006/) refuses an unsafe or partial
declaration in a module of the four libraries, in both execution modes. It
admits the partial helper that Lean generates for a terminating recursive
definition only when Lean's recursion compiler regenerates the definition from
the helper and the kernel checks the recursion equation, with the definition
safe and in the helper's module. The tools make no such check. Admission of that
helper by its name and its parent admits every helper that the rule admits, so
Regula is stronger. The rule has one more exception: an unsafe constructor-index
wrapper of an inductive type, admitted only when the constructor-index function
of the type names the wrapper as its replacement. The check of the next
paragraph refuses that pair in Acorn, AcornVerif and NativeApp.

**Native replacements: the tools refuse more.** The theorem inventory refuses each
declaration of a module of Acorn, AcornVerif or NativeApp that carries a
replacement attribute or an extern attribute, whatever reaches it and whatever
is proved about it. [RG3002](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG3002/) refuses, in the libraries that claim checked
mode (Acorn, NativeApp and Bootstrap), a replacement or an extern outside the
Lean toolchain that an execution root reaches and that has no kernel-checked
equality with its reference. A root is each computable, safe definition of the
library that has no internal name and is not a proposition, used or not, and an
extern never has that equality. [RG3001](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG3001/) refuses an execution path that the audit cannot resolve,
in both modes. Three inputs pass Regula and not the inventory: a replacement or
an extern in AcornVerif, which claims report mode; a replacement in Acorn or
NativeApp with a proved equality to its reference; and a declaration with either
attribute that is no root and that no root reaches. Source admission refuses
both attributes as words in every executing and proof source, so the inventory
adds the declarations that elaboration generates. This check runs once, in the
theorem inventory. A copy in the compiled boundary admission would repeat the
same predicate for a subset of the same modules in the same command,
`./scripts/verify.sh`.

**Reach of each entry: the tools refuse more.** The ownership audit follows the
compiler's intermediate code from the entry point of each executable, the tool
executables among them. It refuses an extern or a proof hole in a maintained
module on the way, and requires that the entry reaches each definition that
`entryUses` lists for it. Regula examines no excluded target, so an extern that
only a tool executable reaches passes the audit, and no rule requires that a
root reaches a definition.

**Module inventory: the tools refuse more for tool modules.** [RG2002](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG2002/)
refuses a root library that the manifest does not classify. [RG2004](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG2004/)
refuses a module of the package outside exactly one classified library, and a
module that a claimed module imports and that no claimed target has. Lake's glob
decides which library has a source. A new source below Acorn, AcornVerif or
NativeApp is therefore a module of that library, the audit examines it under the
library's claim, and Acorn's boundary predicates class it by its name. The
tools keep no written list of these modules. Two inputs pass Regula and not the tools. A new source below
`lean/AcornTools` is a module of an excluded library, which no rule examines:
ownership admission requires each discovered source outside the three libraries
to be an entry of `toolingModules`, and each entry to be a source. A source
below lean that no library has is invisible to the audit unless a claimed module
imports it: the same requirement refuses it, and Lake refuses the build request
for a module that no library has.

**Executable inventory: the tools refuse more.** Ownership admission refuses a
Lake executable whose target name and root module are not a pair of
`executables`, and a listed pair that Lake does not have. It also requires that
a module declares `main` exactly when it is the root module of an executable or
is Bootstrap, the interpreted build launcher. [RG2002](https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG2002/) refuses an
executable that the manifest does not classify, a manifest name that is no Lake
target, and an executable that is not classified with the library of its root.
The manifest holds the names and no root: an exchange of the root modules of two
executables of one library changes nothing that the rule reads. The list is also
the Lean owner of the executable names that the build order and this document
read.

Regula has no rule for the import layers of the learned-only boundary, the
capability owners, source syntax admission, the departures register, native
admission, the corpus checks or the required proof links. Those checks are
Acorn's own.

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

The site check runs after the project build, beside the other admissions of the
finished build and inside the deadline of `./scripts/verify.sh`; the command above
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
fitting the verification deadline, it becomes a separate required check with its
own bound; the deadline is not raised. Verification also admits the site's source
inventory and requires `site/lake-manifest.json` to lock every dependency of
`lean/lake-manifest.json` to the same revision, because both packages share one
set of dependency checkouts.

The site package is documentation tooling outside the Regula claim.
[Verso](https://github.com/leanprover/verso), pinned in `site/lakefile.toml`, and
Lean's elaborator are trusted to build it. The build establishes that each
reference exists, has the stated type and shows its owner's current value; review
still decides whether the prose describes that owner faithfully.

## Mutation diagnostics

**Pinned digest: `29dde0eb2b6f1ba7`**

```sh
lean/.lake/build/bin/acorn-core audit --expect 29dde0eb2b6f1ba7
```

Paired checksum `53f0f2909b71c8ce`. The deployed arm runs the ranked profile
with the declared D6 exploration rate. The optional ./scripts/verify.sh diagnostics
command runs all three fixed arms under the same deadline. All three pins record
the published generate-and-test tester and task-reading generator (PAR-11, D7),
off-policy option learning (PAR-17), option expectation models with planning under
the current values (PAR-13, PAR-14) and, in the checksums, every option's off-policy
questions (PAR-18). Every pin also records persistent exploration by whichever layer
selects the action, a run interrupting the option whose draw began it and closing its
meta span there (PAR-8, D3);
the declared-rate and differential pins also record the stable, sign-correct
reward-respecting subtasks, assigned at every free decision boundary, and the
declared-rate dynamics decision. The fixed audit arms
are compared through these paired digests. Run these optional diagnostics
when investigating a dynamics change.

## Checkpoint admission

Format 19 holds the exact image of the agent:
every field of its temporal state, the option models, each option's off-policy questions
(PAR-18), primitive credit, the rate schedule and every process-local reference included.
Earlier formats are refused. Load checks dimensions, identifiers, criterion and step order
in the header, then reads the image with every stored word in its own domain, every
learner through the check of its invariant and the agent's two invariants. An incompatible
image is refused and writes to that file are disabled. Loading the bytes that a save of a
state writes returns that state, for every state of the resumable construction
(`AcornVerif.CurrentCheckpoint.load_saved`). The world restarts, and the host begins a
new session of the predictive-agreement evaluator. Filesystem persistence relies on the
narrow C fsync helper, native IO and the operating system.

## Viewer ownership boundaries

The viewer observes telemetry and supervises process lifecycle. Only a stop
request enters the core, at an attempt boundary. Source/compiled ownership
prevents learned code from reaching host control. Browser numeric and lifecycle
contracts have executable owners and generated bytes; see
[the viewer specification](viewer-ux.md).
Predictive agreement compares forecasts with settled finite returns within the
current process. Incomplete horizons and unavailable state are reported as unknown.
