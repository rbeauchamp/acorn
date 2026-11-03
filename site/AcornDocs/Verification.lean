/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import VersoManual
import AcornSite
import AcornTools.Boundary.Audit
import Acorn.Constants
import Acorn.Host.Checkpoint.Admission
import AcornVerif.CurrentCheckpoint
import AcornVerif.CurrentConstants
import AcornVerif.GridCorrespondence
import AcornVerif.DrawFirst
import AcornVerif.StepParts
import Acorn.Host.Microduck.Bridge
import Acorn.Host.Microduck.Sensing
import Acorn.Host.Microduck.Session
import Acorn.Host.Microduck.Loop
import Acorn.Host.Microduck.Wire
import Acorn.Host.Viewer.Supervision
import AcornVerif.Decimal

open Verso.Genre Manual
open AcornSite

#doc (Manual) "Verification" =>
%%%
tag := "verification"
%%%

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

# Platform setup
%%%
tag := "platform-setup"
%%%

Use `./scripts/start.sh` for automatic setup and launch, or
`./scripts/start.sh --prepare-only` to prepare and build without learning.
It uses Homebrew on macOS and apt-get on Ubuntu/Debian. It installs missing
prerequisites and provisions the pinned Lean, Mathlib, FloatLib and lean-intent dependencies;
repeat launches use the offline bootstrap when those dependencies are already
available. The bootstrap status that decides this builds nothing, writes only the
launcher's own override file and asks Lake whether the FloatLib modules the proof
bridge imports, the lean-intent modules the intent bridge imports and the Regula
modules the decision registries import are current.
The first setup may need network access, a package-manager password prompt or
the macOS command-line tools installation dialog. It never runs Acorn as root
and does not change the global Xcode selection or Lean default toolchain.

The [verification workflow](../.github/workflows/verify.yml) runs only when
started by hand, on GitHub's standard `ubuntu-24.04` x64 image. It installs no
system package: it admits by name the packages that image provides, and takes
elan from a release pinned by the SHA-256 of its archive, which the dependency
cache keeps. Every workflow step that reaches the network has its own time
limit, so a stalled download fails that step. Dependency caches include the
Ubuntu release and runner architecture. Automatic local setup supports macOS and
Ubuntu/Debian Linux.

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
`(cd lean && lake exe cache get && lake build Mathlib regula/lint floatlibBridge regulaInterface leanIntentBridge)` from the
repository root to provision the pinned toolchain/dependencies; the build compiles
only Mathlib modules absent from the upstream cache, plus Regula's lint driver.
FloatLib and lean-intent publish no cache, so the same command
compiles the FloatLib modules that the proof bridge imports, the lean-intent modules
that the intent bridge imports, and the two Regula interface modules that the
decision registries import.
The offline bootstrap asks Lake whether every artifact those imports need is
current and refuses to run until it is: verification never compiles a dependency
inside its deadline. Verification also builds the
[documentation site](#documentation-site): run
`(cd site && lake build verso/VersoManual verso/VersoManual:shared)` once to provision pinned Verso and its shared library, which
verification likewise requires to be built already. Do not use `lake update` to
resolve a missing dependency; that changes the selected versions.

Build with {spliceCode}`s!"./scripts/lean.sh build {executable "acorn-viewer"}"`; Lake also builds its declared
core and checkpoint-helper dependencies. OpenSSL is required for build-time
source hashing. The launcher adds Homebrew's OpenSSL 3 to its own environment;
manual builds need a usable OpenSSL on PATH.

## Headless and advanced launch
%%%
tag := "headless-and-advanced-launch"
%%%

`./scripts/start.sh --no-browser` prints the actual bound loopback URL.
`--run-dir DIR` selects another run directory and `--port N` selects a port;
the default port is allocated by the OS. Browser opening is optional and its
failure does not stop the agent. Use `./scripts/start.sh --help` for the launcher
options. Raw viewer options are documented in [the viewer specification](viewer-ux.md).

## Interrupted-launch recovery
%%%
tag := "interrupted-launch-recovery"
%%%

The launcher keeps `.acorn-launch/` outside the run directory so that Clear
cannot remove its ownership lock. An ordinary exit removes the lock. A forced
termination or machine crash may leave it behind. A second launcher refuses
to displace an uncertain owner.

Read `.acorn-launch/pid` and inspect that process and its viewer/core descendants.
Only after confirming that no process still owns this run, remove the lock's
temporary files (control, pid and installer.sh) and the
empty `.acorn-launch/` directory, then rerun the launcher. Preserve `acorn-run/`.
Do not manually launch another viewer against a directory already in use.

## Build and verification failures
%%%
tag := "build-and-verification-failures"
%%%

If a tool is missing, install the named prerequisite before retrying. On macOS,
check that `xcode-select -p` points to an installed, usable developer toolchain.
If verification reaches its 360-second deadline, retain the failing command
and diagnostic for a focused report; do not raise the limit or treat a partial
run as a pass. Run the complete command to check all verification owners.

# Compiler and execution boundary
%%%
tag := "compiler-and-execution-boundary"
%%%

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
native replacement. Every proof passes through the kernel.

The modules that compose the agent import no world. Source and compiled admission
refuse a declared module that imports a host module, or references a declaration
owned by one, unless it is one of a world's own declared modules. The grid world's are
{splice}`proseList (AcornBoundaryAudit.gridOwners.toList.map toString)`. The [Microduck](https://github.com/pollen-robotics/microduck)
world's is {splice}`proseList (AcornBoundaryAudit.microduckOwners.toList.map toString)`,
which binds that world to the interface; the host's sensing builds its percepts, which the
executable microduck-host runs, and no theorem states what it feeds a learner. The last of the grid world's modules binds the
grid world to the agent's interface.
{decl}`Acorn.Handcrafted.Agent.grid_inputs` states what that binding feeds each
learner, in terms of the host's own channel, signal and potential definitions, for
every agent state, observation and reward word:

{statement Acorn.Handcrafted.Agent.grid_inputs}

{leanModule}`AcornVerif.GridCorrespondence` keeps the agent's composition over host
observations, as it was before the interface, as a frozen reference that no executing
module imports. {decl}`AcornVerif.GridCorrespondence.act_eq` states that the
interface agent's decision on the grid percept returns the same next state and
decision as that reference:

{statement AcornVerif.GridCorrespondence.act_eq}

{decl}`AcornVerif.GridCorrespondence.callback_eq` and
{decl}`AcornVerif.GridCorrespondence.initial_eq` state the same for the host's step and
construction. Restoration has no frozen reference, since restoration is exact
({decl}`Acorn.Handcrafted.Agent.restore_exact`). The reference covers the composition; the
storage types beneath it are the executed ones at the grid's action count.

The executed step is two functions under a declared step order:
{decl}`Acorn.Handcrafted.Agent.choose` selects, and
{decl}`Acorn.Handcrafted.Chosen.learn` completes the step from the value the first
returned. {decl}`Acorn.Handcrafted.Agent.act_parts` states that under the default
order they compose to the executed step, for every agent state and percept, in every
world:

{statement Acorn.Handcrafted.Agent.act_parts}

Under the order that plans after the action,
{decl}`Acorn.Handcrafted.TemporalControl.atBoundary_unplanned` states that the meta
draw of a free dispatch reads the meta-controller before that frame's planning,
and {decl}`Acorn.Handcrafted.Agent.actOrdered_undrawn` that a step whose decision
records no meta decision is the executed step under that order and the default one.
With no planning selected, {decl}`Acorn.Handcrafted.Agent.actOrdered_unplanned` states that
the two orders are one step: the same next agent and the same decision for every agent
state and percept. {decl}`AcornVerif.StepParts.loop_unplanned` states that they then have
one closed loop in every world that waits for the agent.

Under the order that acts before it learns, the first part makes every draw and takes
no reward word. {decl}`Acorn.Handcrafted.Agent.choose_reward` states that two percepts
with one frame give the same temporal state, decision and record of owed writes,
whatever their reward words. The frame carries the achievement event, which the first
part reads, so the statement does not make the action independent of that event.
{decl}`AcornVerif.DrawFirst.actThenLearn_planAfterAct` states that
this step is the step that plans after the action wherever the decision starts no
option and no option closes at a free dispatch under the discounted criterion:

{statement AcornVerif.DrawFirst.actThenLearn_planAfterAct}

{decl}`AcornVerif.DrawFirst.drawBoundary_start` and
{decl}`AcornVerif.DrawFirst.dispatchMeta_start` state what the first action of an
option that starts reads in each case. The second also states that selection makes the
writes of the start with {decl}`Acorn.Handcrafted.TemporalControl.startOption`, and
{decl}`Acorn.Handcrafted.TemporalControl.settle_started` that the owed writes make them
with the same function. {decl}`AcornVerif.DrawFirst.drawBoundary_unplanned` states what
the meta draw of this order reads, and {decl}`AcornVerif.DrawFirst.drawFirst_assigns`
that the assignment refresh precedes its draws.
{decl}`AcornVerif.DrawFirst.selectWithOperations_form` and
{decl}`AcornVerif.DrawFirst.drawFirst_form` state, for every state, frame and reward word
and on every branch, that selection and the draw-first dispatch followed by its owed
writes are one specification, {decl}`AcornVerif.DrawFirst.dispatchForm`, in two modes.
That specification reads its mode in two places, so those are the places where the two
orders can differ. The first is the free dispatch, and
{decl}`AcornVerif.DrawFirst.boundaryForm_frozen` states that in a frozen profile it gives
one result in both modes, also when its meta draw starts an option. The other place is
an option that closes under the discounted criterion.

Under every order {decl}`Acorn.Handcrafted.Agent.choose_keeps` states that the first
part writes neither the primitive controller nor a prediction demon, and
{decl}`Acorn.Handcrafted.Chosen.learn_rng` that the second part draws nothing from the
action generator.

A host releases the action after both parts or between them.
{decl}`Acorn.Host.DecisionInput.chooseOwned_release` states that one pass of the host
protocol gives the same result either way, on acceptance and on a refusal.
{decl}`Acorn.Host.runAttempt_complete` states that every value either native loop of
an attempt returns agrees with one pure fold of whole steps,
{decl}`Acorn.Host.Attempt.complete`, in its run state and outcome, or in its refusal
with the learned stage of a refused pass ({decl}`Acorn.Host.AttemptAgrees`,
{decl}`Acorn.Host.Attempt.complete_learned`). The terminal frame and the resource
counters are outside the agreement:

{statement Acorn.Host.runAttempt_complete}

A world declares its timing in its interface: it waits for each action, or it moves on
a wall clock with a declared cycle and a latency in cycles.
{decl}`Acorn.Handcrafted.Grid.interface_timing` states that the grid world declares that
it waits. For a wall-clock declaration, {decl}`Acorn.Pace.meets_index` states the verdict
on the instant an action is released at: the deadline is met exactly when the release
falls in a cycle before the one the deadline starts. {decl}`Acorn.Pace.outcome` gives, for
what a host holds, a world's default and an instant, the action in force and whether a
fault holds. {decl}`Acorn.Pace.step_fault` states that in one step a fault holds exactly
from the deadline to the release:

{statement Acorn.Pace.step_fault}

{decl}`Acorn.Pace.step_holds` states that the preceding action is in force at every
instant of the fault at which it has not lapsed, which is every instant in a world whose
actions do not lapse, and {decl}`Acorn.Pace.step_lapsed` that from its lapse the fault has
the world's default. {decl}`Acorn.Pace.step_faultless` states that no instant has a fault
exactly when the release meets the deadline. An instant is a natural number of
nanoseconds, so this arithmetic is exact. The statements are about these functions. The
grid world declares no wall clock; the Microduck's world declares one, and its host keeps a
standing in its pure transitions.

The Microduck world has an action table and a bridge's state, as pure definitions, which the
host's transitions call. The type of the commands a bridge can send is closed: enable, one of
four velocities, one of five skills. {decl}`Acorn.Host.Microduck.Action.commands_powered`
states that the release of an action never sends the enable command.
{decl}`Acorn.Host.Microduck.Action.next_covers` states, for every release, timely or
late, that the cycle the next percept is computed to have starts no earlier than the
release plus the action's declared duration and a transit allowance:

{statement Acorn.Host.Microduck.Action.next_covers}

That a sensed percept cannot precede that cycle is in the pure transitions of a host: a
percept is sensed only in a cycle that is not before that one, and from a state frame heard
since the release ({decl}`Acorn.Host.Microduck.Idle.sense_iff`); it can be sensed in a later
cycle. While the percept awaits its action, a reading of the clock sends the velocity of the
action that the deadline rule names in force, up to the end of its hold, and nothing from
then ({decl}`Acorn.Host.Microduck.Awaiting.tick_named`).
A host is in one of two phases, each a type whose values are reached from the start by the
transitions, and its verdict at every instant is the deadline rule's for its last step: a
fault holds from the deadline to the release, the instant of the release included
({decl}`Acorn.Host.Microduck.Awaiting.release_fault`), and the latch of the goal is the fold
of the adapter's rule over the readings sensed ({decl}`Acorn.Host.Microduck.Reached.latch`).
The pure core of the host's loop calls the transitions with the agent's two step parts, and the action released for a percept is the agent's choice on it ({decl}`Acorn.Host.Microduck.Loop.step_release`). The executable `microduck-host` runs that loop over three nc child processes, the trusted transport, at readings of the monotonic clock, and hands it a finished choice or learning only after the runtime answered that its task finished, with the reading taken after that; it is effects, with no theorem of its own. A bridge's state stores the record of its release, and the
cycle of the next percept and the end of the hold are functions of that record, so
{decl}`Acorn.Host.Microduck.Bridge.next_covers` holds of every state.
{decl}`Acorn.Host.Microduck.Bridge.ticks_named` states that over any list of readings of
the clock every command sent is the velocity of the action that the standing after the
release names at that reading, and {decl}`Acorn.Host.Microduck.Bridge.tick_lapsed` that
from the end of the hold that standing names the world's default and nothing is sent. At
the instant of a release itself the deadline rule still names the preceding action, by its
convention that an action is in force after the instant of its release.
{decl}`Acorn.Host.Microduck.Bridge.fault_named`
states the action in force during a fault: the preceding action up to the end of its
hold, and the default from it. {decl}`Acorn.Host.Microduck.Bridge.tick_fresh` and
{decl}`Acorn.Host.Microduck.Bridge.Fresh.age` bound the age of the last send of a
velocity inside its hold. Five things are assumptions of those statements' use and not
theorems: the daemon's expiry of a velocity, the time from a send to the daemon's receipt,
the gap between two readings of the host's clock, that the posture a caller states is the
body's, and that a declared duration covers what the body takes.

What the Microduck senses is kept as bounded integers, also as pure definitions, which the
readers of a daemon's line call when the executable microduck-host hears a frame. The daemon reports a measured quantity as the decimal text of a JSON
number, and {decl}`Acorn.Host.Microduck.Decimal.fixed` converts such a number to an integer
of a declared scale by integer arithmetic alone. What it computes is stated over the
rational value of the decimal, {decl}`AcornVerif.Decimal.value`, and the predicate
{decl}`AcornVerif.Decimal.Nearest`, which name none of the conversion's arithmetic: the
result is the integer nearest to the value in the units of the scale, at a tie the one
farther from zero, saturated to the bounds of the scale.

{statement AcornVerif.Decimal.fixed_nearest}

{decl}`AcornVerif.Decimal.Nearest.unique` states that at most one integer is nearest, and
{decl}`AcornVerif.Decimal.rounded_nearest` that the rounding of the executed arithmetic is.
The statement holds for an exponent of any size. The conversion decides by two comparisons
of integers when a decimal rounds to zero and when it saturates
({decl}`Acorn.Host.Microduck.Decimal.fixed_clamp`), and between them it forms two powers
of ten: the exponent of the one that multiplies the digits is below the width of the
scale, and the exponent of the one that divides is at most the width of the digits
({decl}`Acorn.Host.Microduck.Decimal.shift_between`). The bounds of the result are part of
its type.

{decl}`Acorn.Host.Microduck.Decimal.read` gives the decimal of one JSON value. It scans the
spelling that the JSON parser keeps with the parser's own scanner,
{decl}`Acorn.Json.Numeral.scan`, and reads exactly the numbers whose spelling is the whole
spelling of a numeral that has the form of a number in RFC 8259, section 6
({decl}`Acorn.Host.Microduck.Decimal.read_iff`). The number that a numeral writes,
{decl}`AcornVerif.Decimal.written`, is stated by a table of the ten digits and the place of
each digit, with none of the reader's arithmetic. The integer kept for a value that is read
is nearest to that number in the units of the scale, at a tie the one farther from zero,
saturated to the bounds of the scale:

{statement AcornVerif.Decimal.read_nearest}

No theorem states that every number of a parsed text is read: it follows from
{decl}`Acorn.Json.parse_sound`, whose grammar spells each number of an accepted text as an
{decl}`Acorn.Json.Grammar.Number`, with {decl}`Acorn.Json.Grammar.number_iff` and
{decl}`Acorn.Host.Microduck.Decimal.read_iff`, by an induction over the derivation that no theorem
states.
{decl}`Acorn.Host.Microduck.Reading.age_exact` states the age of the depth frame
that a reading is paired with. A parsed JSON value is read into these types by
{decl}`Acorn.Host.Microduck.State.read` and {decl}`Acorn.Host.Microduck.Depth.read`, and a
frame is read exactly when it is what the value writes, member by member
({decl}`Acorn.Host.Microduck.State.read_iff`, {decl}`Acorn.Host.Microduck.Depth.read_iff`).
A whole parsed line is read by {decl}`Acorn.Host.Microduck.Line.read` as exactly one case
of declared criteria, which are taken from JSON-RPC 2.0 and are not the whole of it: a
notification, as a frame of its stream or as a notice
({decl}`Acorn.Host.Microduck.Line.read_state`, {decl}`Acorn.Host.Microduck.Line.read_depth`),
a response with a result or with an error ({decl}`Acorn.Host.Microduck.Line.read_result`,
{decl}`Acorn.Host.Microduck.Line.read_fault`), and invalid for every other value
({decl}`Acorn.Host.Microduck.Line.read_invalid`).

A host writes each request as the text of a JSON value of two levels, and the parser of
this repository reads the text of every such value back as the value:

{statement Acorn.Json.parse_request}

So for every identifier and command the parser reads the line of a send as the request of
that send ({decl}`Acorn.Host.Microduck.Command.line_asked`). A second theorem states what every
text that the parser accepts is: a JSON text of the grammar of RFC 8259,
{decl}`Acorn.Json.Grammar.Text`, with a derivation that gives the value that the parser returns
({decl}`Acorn.Json.parse_sound`). So a line of a daemon that the parser accepts is read as a value
that the grammar gives its text. No theorem states that the parser accepts every text of the
grammar, and none is about what a daemon sends or accepts.

Acorn's executable definitions and their state invariants are under lean/Acorn.
AcornVerif contains contracts importing those definitions and supporting
mathematics with explicit hypotheses. {leanModule}`Acorn.Constants` owns the shared machine
words; {leanModule}`AcornVerif.CurrentConstants` checks the stated correspondence with rational and
dimensional inputs used by the mathematical proofs. For example,
{decl}`AcornVerif.CurrentConstants.explore_rate_value` states that the binary32 word of the
declared exploration rate denotes the rational those proofs use:

{statement AcornVerif.CurrentConstants.explore_rate_value}

Each theorem's actual type owns its domain, hypotheses and guarantee. Binary32
and Binary64 proofs concern admitted finite words or explicitly stated conversion
semantics; real/rational identities do not automatically establish machine
rounding equivalence. Universal program properties are limited to their checked
implementation linkage. Compiler/native runtime, filesystem stability, the
reviewed build/gate tools, cryptographic tools and OS remain trusted boundaries.

# Build and source inventory
%%%
tag := "build-and-source-inventory"
%%%

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
validates, in a checkout that holds only tracked files; GitHub Actions runs no
check on a pull request or a push. The gate provisions the pinned dependencies,
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
[Regula audit](#regula-audit) on the same commit, also when verification failed,
and passes only when both runs and the audit pass.

The pipeline stores the provisioned dependency checkouts and their build outputs
once for each default-branch commit a run starts from, and gives a run a private
copy only while the run's toolchain and lock files equal that commit's; Lake
rebuilds whatever its traces do not show current. Acorn's own outputs are never
carried from one run to another. The workflows that ran these checks on GitHub
stay available to start by hand; they have read-only repository permissions,
no secrets, no privileged pull-request trigger, and pinned action revisions.

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

# Regula audit
%%%
tag := "regula-audit"
%%%

[Regula](https://github.com/rbeauchamp/regula) is an audit of Lean builds. Acorn
requires its release v0.12.0, pinned in `lean/lakefile.lean`, and the merge gate
requires the Regula audit:

```sh
./scripts/regula.sh
```

Regula's release names three commands for its proof verdict, run in order on one
build: `lake build --wfail`, `lake check --inadvisably-no-sandbox` and
`lake lint`. The second exports every constant of the whole imported
environment, Mathlib's included, used by a claimed constant or not: here 496,347
constants from 5,585 modules, which it replays from an export held in memory. On
Acorn's claim it had not finished after 3 hours 45 minutes on a 24 GiB machine,
its memory footprint at 39 GB, so it does not fit the machines that run the
gate. The script runs the first and the third in lean, each from that directory
with no option of Lake's, and in the place of the second Acorn's kernel replay,
`lake exe kernel-replay`. So the audit obtains Regula's rules under the profile
and that replay, not Regula v0.12.0's proof verdict as the release defines it.
The departure is interim: when a release of Regula makes its proof verdict
obtainable for a project that imports Mathlib, the gate returns to Regula's own
commands and the kernel replay is retired. The other passages of Acorn's
documents that describe the gate's Regula step refer to this one.

The first command fails on any warning. The kernel replay reads the build with
Regula's own code, as `lake lint` reads it, and takes its claim from there:
every constant that Regula's rules read as claimed, with the constants each
claimed module's own data lists. It replays each of them, with every constant
that it depends on, in Lean's kernel from an empty environment. It then compares
the quotient constants with the kernel's, as Lean's own checker does, and
refuses an axiom other than propext, Quot.sound and Classical.choice that a
replayed constant uses, by the function that `lake check` uses. It prints
Regula's line of what it read, and the script fails unless `lake lint` prints
the same line, so a build that changed between the two fails. It leaves out an
unsafe or partial claimed constant, as `lake check` does, and the constants of
the imported environment that no claimed constant depends on. A kernel check of
a claimed constant looks up only the constants that the terms it checks name and
the kernel's own built-in constants, which the replay holds, and a name that the
replayed environment lacks makes the kernel refuse: that is an assumption about
Lean's kernel. The replay reads the build's compiled modules in its own process,
where `lake check` replays an export in a process that maps none of them. The
third command is Regula's checker. It exits 0 for a pass, 1 for a fail and 2 for
an incomplete run, and its last line states the verdict; a pass ends that line
with the directory it audited. The script passes only when the kernel replay
accepts, the two lines of what was read agree, and `lake lint` exits 0 with its
last line the pass on lean. The commands resolve dependencies through the Git
lock in `lean/lake-manifest.json`, without the bootstrap's path overrides, so
Lake fetches a dependency whose checkout is not at the locked revision.

A pass of the audit means that Lean's kernel accepts the proofs of the claimed
modules and that they use only the axioms of the profile. It says nothing about
what a compiled program runs, which the checks of ordinary verification below
cover, or about whether a theorem states what was meant, which review reads.
Regula's
[README](https://github.com/rbeauchamp/regula/tree/v0.12.0#what-a-pass-means)
states what a pass of its own proof verdict rests on.

The claim is the modules of the default targets of the Lake configuration and
every module of the package that their imports reach. The default targets are
the libraries Acorn, AcornVerif, NativeApp, Bootstrap and AcornDocument. They hold
every Acorn theorem: the executing definitions with the theorems stated beside
them, the proof library, the native application, the build launcher, and the
names that the document audit admits from outside the project with the theorem
that states what an admitted name is. A theorem can mention only declarations of
the modules its own module imports, so every definition of the package that a
claimed theorem is about is claimed as well. The kernel replay and `lake lint`
import the claimed modules into one environment, where Lean refuses two
declarations of `main`. So Bootstrap, which `lean --run` interprets before anything is built,
declares the one top-level `main` of the claim, and the root of each of the
{splice}`numberWord applicationExecutables.length` application executables is a
module of the library Entry, outside the claim. Its `main` applies the entry
function of a claimed module, such as `Acorn.SwiftTdDriver.main`, and it holds
nothing else; the theorem inventory refuses a theorem in it. AcornTools, the
reviewed tooling trust boundary with the
{splice}`numberWord toolExecutables.length` tool executables, and the
[documentation site](#documentation-site) are also outside the claim and hold no
theorem.

The profile is standard-logical: propext, Quot.sound and Classical.choice, and no
other axiom, for the whole claim. No stricter profile is attainable, because
Lean's core definitions of binary32 and binary64 arithmetic depend on
Classical.choice, as does the Mathlib analysis in AcornVerif. One bridge module in
AcornVerif is the only importer of FloatLib, a proof dependency whose theorems
use the same three axioms; the boundary audit refuses a FloatLib import by any
executing module. A second bridge module in AcornVerif is the only importer of
lean-intent, the proof dependency in which the intent records under
`AcornVerif.Intent` are stated; it depends on nothing beyond Lean's own
libraries, and the boundary audit refuses a lean-intent import by any other
module. The compiler, native runtime, operating system and spawned processes stay
trusted.

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
differ, replays the claim with every constant it depends on in the kernel and
runs Regula's checker, which does not fit beside the ordinary checks inside the
360-second deadline. The
gate runs it after ordinary verification and requires both before a merge. A pass
covers Regula's rules and the kernel replay for the claimed modules; it does not
replace review.

## What Regula checks in place of Acorn's tools
%%%
tag := "regula-scope"
%%%

Acorn's tools under `lean/AcornTools` are outside the claim, so no proof covers
them. They check a compiled declaration or the Lake configuration only where no
part of the Regula audit refuses at least the same inputs for the same modules.
Each paragraph below takes one property: what the Regula audit refuses for the
claimed modules, and what the tools check. Where the tools refuse more, the
paragraph gives an input that shows it, and that check stays.

Ordinary verification alone therefore does not refuse a project axiom, a
dependency on an axiom outside propext, Quot.sound and Classical.choice, a
compiler-trusting proof, or a compiled unsafe or partial declaration. The Regula
audit refuses each of them, and the merge gate requires it. Run
`./scripts/regula.sh` for it before proposing a change to a Lean source.
Ordinary verification still refuses the words `axiom`, `sorry`, `unsafe`,
partial and `native_decide` in every executing and proof source, through source
admission, and a proof hole through the build, where a warning is an error.

*Project axioms.* RG1001 refuses an axiom declared in a claimed module. The tools
make no such check.

*Axioms that a declaration depends on.* RG1003 refuses a constant of a claimed
module with a transitive axiom outside propext, Quot.sound and Classical.choice,
and RG1005 one whose axioms exceed the standard-logical profile. Both rules
examine every constant: theorems, definitions and instances. The kernel replay
refuses an axiom outside the same three that a replayed constant uses. The tools make
no such check. The tool module AcornTools.AxiomPins still pins the exact axiom
sets of selected theorems in the build, with message guards around
`#print axioms`; it imports the proof library and lies outside the claim with the
other tools.

*Proof holes and compiler-trusting proofs.* RG1002 refuses a constant that
depends on Lean's proof-hole axiom, directly or through an import, and RG1004 one
that depends on an axiom that `native_decide` or a related tactic adds. Both rules
read the transitive axiom set. The tools make no such check.

*Unsafe, partial and looping declarations.* RG1006 refuses an unsafe or partial
constant of a claimed module, a constant with the name of a recursion helper
without the form that Lean gives the helper of a terminating recursive
definition, and a constant whose value mentions the loop constructs that while
and repeat compile to. The tools make no such check of compiled declarations.
The host's loops that run until something outside the program happens, such as
the end of a stream or a stop request, iterate over `Acorn.Host.forever`, whose
iteration in IO and BaseIO is a fixed-point definition with the one-step
unfolding of Lean's own loop (`Acorn.Host.forIn_io`). The viewer's stream of
live frames runs in Std's Async monad, which runs a continuation in a task, so
no such definition exists for it; it calls Std's own loop of that monad, the
one that repeat reaches there, and that loop is part of the trusted toolchain.

*Kernel replay.* The kernel replay checks every constant of the claim, and every
constant it depends on, in Lean's kernel again from an empty environment, so a
proof that the build's own kernel check skipped is checked there. Regula's
specification records a module that added a theorem of False with the kernel
check skipped: it passed `lake build` and `lake lint`, and `lake check` refused
it. The kernel replay sends such a theorem to the kernel as well, which refuses
a proof of False. The tools make no such check.

*Native replacements: the tools refuse more.* The theorem inventory refuses each
declaration of a module of Acorn, AcornVerif, NativeApp, AcornDocument or Entry
that carries a replacement attribute or an extern attribute, whatever reaches it
and whatever is proved about it. The Regula audit reads no replacement or extern:
a pass says nothing about what a compiled program runs. Source admission refuses
both attributes as words in every executing and proof source, so the inventory
adds the declarations that elaboration generates. This check runs once, in the
theorem inventory. A copy in the compiled boundary admission would repeat the
same predicate for a subset of the same modules in the same command,
`./scripts/verify.sh`.

*Reach of each entry: the tools refuse more.* The ownership audit follows the
compiler's intermediate code from the entry point of each executable, the tool
executables among them. It refuses an extern or a proof hole in a maintained
module on the way, and requires that the entry reaches each definition that
`entryUses` lists for it, the claimed entry function first. Regula examines no
compiled code.

*Module inventory: the tools refuse more.* Lake's glob decides which library has
a source. A new source below Acorn, AcornVerif or NativeApp is therefore a module
of that library, the claim covers it, and Acorn's boundary predicates class it by
its name. The tools keep no written list of these modules. A new source below
`lean/AcornTools` is a module of a tool library outside the claim: ownership
admission requires each discovered source outside the five libraries that Lake's
globs assign to be an entry of `toolingModules`, and each entry to be a source. A
source below lean that no library has is outside the claim unless a claimed
module imports it: the same requirement refuses it, and Lake refuses the build
request for a module that no library has.

*Executable inventory: the tools refuse more.* Ownership admission refuses a Lake
executable whose target name and root module are not a pair of `executables`,
and a listed pair that Lake does not have. It also requires that a module
declares `main` exactly when it is the root module of an executable or is
Bootstrap, the interpreted build launcher. The list is also the Lean owner of the
executable names that the build order and this document read.

*Decision registrations.* The ownership audit requires a contract with a kind for
each registered decision function whose result is not `Decidable`, as stated
above, and counts only a contract about the whole function: its subject is the
function applied to nothing but the arguments its type takes implicitly, so a
contract about one application does not count. Regula reads no registration.

Regula has no rule for the import layers of the learned-only boundary, the
capability owners, source syntax admission, the departures register, native
admission, the corpus checks or the required proof links. Those checks are
Acorn's own.

# Documentation site
%%%
tag := "documentation-site"
%%%

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

# Mutation diagnostics
%%%
tag := "mutation-diagnostics"
%%%

*Pinned digest: {spliceCode}`digest .declared`*

```spliced sh
s!"lean/.lake/build/bin/{executable "acorn-core"} audit --expect {digest .declared}"
```

The expected digest has one form, `0x` and exactly sixteen lowercase hexadecimal digits:
it is a hash identifier, not a number, so it is not read as a command-line number and
digit-only text such as `10` is refused.
Paired checksum {spliceCode}`checksum .declared`. The deployed arm runs the ranked profile
with the declared D6 exploration rate. The optional ./scripts/verify.sh diagnostics
command runs all {splice}`numberWord auditArms.length` fixed arms under the same deadline. All {splice}`numberWord auditArms.length` pins record
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

# Checkpoint admission
%%%
tag := "checkpoint-admission"
%%%

Format {splice}`toString Acorn.Checkpoint.formatVersion` holds the exact image of the agent:
every field of its temporal state, the option models, each option's off-policy questions
(PAR-18), primitive credit, the rate schedule and every process-local reference included.
Earlier formats are refused. Format 19 has this layout, but its weights were placed by the
hashes that read their first two words only through their XOR, so a saved weight can sit at
the slot of another feature; the loader refuses it
({decl}`AcornVerif.CurrentCheckpoint.previous_generation_unloaded`). Load checks dimensions,
identifiers, criterion and step order
in the header, then reads the image with every stored word in its own domain, every
learner through the check of its invariant and the agent's two invariants. An incompatible
image is refused and writes to that file are disabled. Loading the bytes that a save of a
state writes returns that state, for every state of the resumable construction
({decl}`AcornVerif.CurrentCheckpoint.load_saved`). The world restarts, and the host begins a
new session of the predictive-agreement evaluator. Filesystem persistence relies on the
narrow C file-sync helper, native IO and the operating system; `lean/Acorn/Host/Checkpoint/IO.lean`
states what a saved report establishes on each platform and what stays accepted risk.

# Viewer ownership boundaries
%%%
tag := "viewer-ownership-boundaries"
%%%

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
({decl}`Acorn.Host.Viewer.Ran.invariant`): a run directory that moved with no replacement owned is
never acted on again ({decl}`Acorn.Host.Viewer.Supervision.retired_untouched`), a configuration that
disables Clear never archives ({decl}`Acorn.Host.Viewer.Supervision.clear_disabled`), a closing viewer
starts nothing ({decl}`Acorn.Host.Viewer.Supervision.closing_starts_nothing`), and a spawn waits on a
durable state that records its launch ({decl}`Acorn.Host.Viewer.Supervision.spawn_recorded`). A spawn
follows only the successful write of that state, takes the generation one above the last, and
only when the lifecycle is idle, intends to run, has no Clear pending and its restart budget
admits a launch at that instant ({decl}`Acorn.Host.Viewer.Core.resume_launch`); no event and no other
outcome reserves a generation or waits to spawn ({decl}`Acorn.Host.Viewer.Core.step_calm`,
{decl}`Acorn.Host.Viewer.Core.resume_calm`). A Stop winds a live process up whether or not its intent
is saved ({decl}`Acorn.Host.Viewer.Core.stop_winds_up`); a core's exit never closes the viewer,
which closes at a later tick that the actor hands after it attributes the identity the core's
readers delivered ({decl}`Acorn.Host.Viewer.Core.step_finished_defers_close`); every lifecycle
value with an exhausted restart budget intends to stay stopped
({decl}`Acorn.Host.Viewer.Lifecycle.exhausted_stopped`), and the published control reasons retain
the capped cause and explain giving up after three failed starts
({decl}`Acorn.Host.Viewer.controlTelemetry_reasons`); Clear
installs a run other than the one it retires ({decl}`Acorn.Host.Viewer.Core.replaced_identity`); and
every result first installs its own lifecycle and publishes its control record from it
({decl}`Acorn.Host.Viewer.Stepped.effects_settle`). The operating system's process, signal and wait
semantics, the file system's durability, the Lean runtime's IO, mutexes and clock, the identity
a core reports, and the actor's mapping of each effect to the native operation it names remain
the trusted base.
