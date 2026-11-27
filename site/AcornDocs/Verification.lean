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
import Acorn.Host.Viewer.ExplicitStart
import Acorn.Host.Viewer.Supervisor
import Acorn.Host.Viewer.Options
import Acorn.Host.Viewer.StopDurability
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
Lean, Mathlib, FloatLib, lean-intent and Verso dependencies, ShellCheck `0.11.0`,
a C compiler, OpenSSL 3 and GNU coreutils.
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
elan and ShellCheck (`0.11.0`, `scripts/shellcheck.pin`) from releases pinned by the SHA-256 of their archives. Every workflow step
that reaches the network before the gate, the merge-gate step itself and the
overall job each carry an explicit time limit, so a stalled download or a
duration regression fails promptly. The workflow keeps no cache: each run provisions the
dependencies from their pinned sources. Automatic local setup supports macOS and
Ubuntu/Debian Linux and downloads pinned ShellCheck (`0.11.0`) from `scripts/shellcheck.pin` with SHA-256 verification when not already on PATH.

For manual setup, which changes the machine's package manager state and so is
done by an agent only where the person it works for has agreed to it, install
macOS command-line tools and the packages below
([Homebrew installation](https://brew.sh/)):

```sh
brew install coreutils openssl@3 elan
```

Then install pinned ShellCheck `0.11.0` (`scripts/shellcheck.pin`, `shellcheck-v0.11.0.darwin.aarch64.tar.gz` on Apple silicon or `shellcheck-v0.11.0.darwin.x86_64.tar.gz` with its matching SHA-256 from `scripts/shellcheck.pin` on Intel) after verifying its SHA-256 digest before extracting:

```sh
(
  set -eu
  tmp=$(mktemp -d)
  trap 'rm -rf -- "$tmp"' EXIT
  cd "$tmp"
  curl --fail --location --proto '=https' --tlsv1.2 -o shellcheck.tar.gz \
    https://github.com/koalaman/shellcheck/releases/download/v0.11.0/shellcheck-v0.11.0.darwin.aarch64.tar.gz
  printf '%s  shellcheck.tar.gz\n' 339b930feb1ea764467013cc1f72d09cd6b869ebf1013296ba9055ab2ffbd26f | shasum -a 256 -c
  tar -xzf shellcheck.tar.gz shellcheck-v0.11.0/shellcheck
  mkdir -p "$HOME/.local/bin"
  install -m 0755 shellcheck-v0.11.0/shellcheck "$HOME/.local/bin/shellcheck"
) && export PATH="$HOME/.local/bin:$PATH"
```

For Ubuntu, under the same condition, install:

```sh
sudo apt-get update
sudo apt-get install -y build-essential curl git libgmp-dev openssl coreutils elan
```

Then install pinned ShellCheck `0.11.0` (`scripts/shellcheck.pin`) on x86-64 ahead of any distro package on PATH:

```sh
(
  set -eu
  tmp=$(mktemp -d)
  trap 'rm -rf -- "$tmp"' EXIT
  cd "$tmp"
  curl --fail --location --proto '=https' --tlsv1.2 -o shellcheck.tar.gz \
    https://github.com/koalaman/shellcheck/releases/download/v0.11.0/shellcheck-v0.11.0.linux.x86_64.tar.gz
  printf '%s  shellcheck.tar.gz\n' b7af85e41cc99489dcc21d66c6d5f3685138f06d34651e6d34b42ec6d54fe6f6 | sha256sum --check --strict
  tar -xzf shellcheck.tar.gz shellcheck-v0.11.0/shellcheck
  sudo install -m 0755 shellcheck-v0.11.0/shellcheck /usr/local/bin/shellcheck
)
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

Build with {spliceCode}`s!"./scripts/lean.sh build {executable "acorn-viewer"}"`; Lake also builds its declared
core and checkpoint-helper dependencies. OpenSSL is required for build-time
source hashing. The launcher adds Homebrew's OpenSSL 3 to its own environment;
manual builds need a usable OpenSSL on PATH.

## Headless and advanced launch
%%%
tag := "headless-and-advanced-launch"
%%%

In work on a change a launch needs the owner's authorization, with or without a
browser. `./scripts/start.sh --no-browser` prints the actual bound loopback URL.
`--run-dir DIR` selects another run directory and `--port N` selects a port;
the default port is allocated by the OS. Browser opening is optional and its
failure does not stop the agent. Use `./scripts/start.sh --help` for the launcher
options. `--help` and `--prepare-only` stop before the launch. Raw viewer options are documented in [the viewer specification](viewer-ux.md).

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
empty `.acorn-launch/` directory; the launcher can then be run again with the
options it was first given. In work on a change, the conditions for running it
again are those of the first run, which
[running a program](../CONTRIBUTING.md#running-a-program) states. Preserve `acorn-run/`.
Do not manually launch another viewer against a directory already in use.

## Build and verification failures
%%%
tag := "build-and-verification-failures"
%%%

If a tool is missing, install the named prerequisite before retrying, under the
condition on installing that [platform setup](#platform-setup) states. On macOS,
check that `xcode-select -p` points to an installed, usable developer toolchain.
If verification reaches its 360-second deadline, retain the failing command
and diagnostic for a focused report; do not raise the limit or treat a partial
run as a pass. Run the complete command to check all verification owners.

# Compiler and execution boundary
%%%
tag := "compiler-and-execution-boundary"
%%%

Every Git-tracked Lean source below `lean/` must be a regular file and a module
of the libraries Acorn, AcornVerif, NativeApp, AcornDocument or Entry, which
[the Lake configuration](../lean/lakefile.lean) assigns only from tracked
modules, or a listed tool module. The [Regula audit](#regula-audit) claims the
first four with Bootstrap; Entry holds the executables' roots. Every retained
native target is built and checked against Lake's evaluated targets and compiled
entry owners; each executable root must be a maintained module. Ownership
admission refuses a facet-qualified build key in the root package's Lake
configuration. In Lake of Lean v4.36.0 (Lake/Build/Target/Fetch.lean, lines 54 to 67;
leanprover/lean4#15435), PartialBuildKey.fetchInCoreAux fetches a facet-qualified key
from an asynchronous bindM continuation, which races other fetches on the unsynchronized
build store so a second job can run on the same output file; a facetless key is resolved
through its package and fetched synchronously, so it is the form admitted. Before any Lake command, `Bootstrap.lean` must elaborate with no message,
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

Both {decl}`AcornVerif.Decimal.ofNumeral_value` and {decl}`AcornVerif.Decimal.read_nearest` apply to
formed numerals only (`Acorn.Json.Numeral.Formed`): for a character that is not a decimal digit,
{decl}`AcornVerif.Decimal.digit` returns zero while {decl}`Acorn.Host.Microduck.spelled` subtracts
48 from the character code, so no claim is made about unformed numerals.
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
of declared criteria, which are taken from JSON-RPC 2.0 (JSON-RPC Working Group,
*JSON-RPC 2.0 Specification*, 2010, updated 2013, sections 4, 4.1, 5, and 5.1) and are not
the whole of it (for example, notification params can be any value and extra members are
not refused): a notification, as a frame of its stream or as a notice
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
({decl}`Acorn.Json.parse_sound`), using RFC 5234 DIGIT (`%x30-39`) and case-insensitive HEXDIG
(2008, section 2.3 and appendix B.1), host UTF-8 decoding before parsing (RFC 8259 §8.1),
lone-surrogate rejection because Lean Char holds Unicode scalar values (RFC 8259 §8.2),
distinct object-member names rejecting duplicate decoded keys before object construction
(RFC 8259 §4), and a zero-based value-depth nesting limit of 128 (RFC 8259 §9: a top-level
value starts at depth 0, empty arrays and objects return at their own depth so 129 nested
arrays are accepted when the innermost array is empty at depth 128, and placing any value
inside it reaches depth 129 and is refused); {decl}`Acorn.Json.unicodeWhitespace` matches Unicode
White\_Space for manifest {decl}`Acorn.Json.Value.text` admission rather than RFC 8259's four
whitespace characters ({decl}`Acorn.Json.Grammar.Space`). So a line of a daemon that the parser accepts
is read as a value that the grammar gives its text. No theorem states that the parser accepts
every text of the grammar (and grammar-value uniqueness follows from the completeness theorem
tracked in [issue 163](https://github.com/rbeauchamp/acorn/issues/163)), and none is about what a
daemon sends or accepts.

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
rounding equivalence. Across the executing floating-point proof modules,
`AcornVerif.CurrentArithmetic`, `AcornVerif.CurrentOrder`, `AcornVerif.CurrentFloat`,
`AcornVerif.CurrentOperations`, `AcornVerif.CurrentDivision`, `AcornVerif.CurrentPower`,
`AcornVerif.CurrentBackupBounds`, `AcornVerif.CurrentModelArithmetic`,
`AcornVerif.CurrentRetirementRounding`, and `AcornVerif.CurrentLifetimeArithmetic`
unfold Lean v4.36.0's logical floating-point model
(`Init/Data/Float/Model/{Float,Unpacked/Round,Unpacked/Pack/Basic}.lean` and
`Unpacked/Operations/{OfNat,Add,Sub,Mul,Div}.lean`) directly against Acorn's wrappers,
keeping `AcornVerif.CurrentArithmetic.unpackedValue` total on exceptional words (which
require separate classification), excluding 1-bit exponent formats in
`AcornVerif.CurrentArithmetic.model_unpack_format`, proving `AcornVerif.CurrentFloor.floor32_spec`
algebraically in binary64-subnormal units without native reflection, input enumeration, or a
trusted floor primitive (preserving zero signs, with exceptional words handled separately),
preserving negative normal representable upper bounds even across packing exponent overflow in
`AcornVerif.CurrentRetirementRounding.normalize_negative_bound`, establishing a finite result
and conservative `2^-35` enclosing-quotient error bound for binary64 division on finite operands
with a nonzero divisor and exact quotient magnitude `|left / right| ≤ 2^16` in
`AcornVerif.CurrentDivision.binary64_div_finite_error` (without claiming the tight half-unit
bound proved separately via FloatLib in `AcornVerif.FloatLibBridge.binary64_div_half_unit_error`),
establishing a finite result and subtraction error `≤ 2^-37` on finite operands with
`|diff| ≤ 2^16`, truncation toward zero on finite inputs, and inactive 32-bit clamping for finite
`|x| ≤ 2^16` in `AcornVerif.CurrentOperations`
(`binary64_sub_finite_error`, `numerical64_trunc_toward_zero`, `numerical64_toI32_trunc`),
quantifying unit-interval power and negative-zero parity over every natural and 32-bit unsigned exponent
in `AcornVerif.CurrentPower` (`powLoop_unit`, `pow_unit`, `pow_negative_zero`), and handling full
64-bit unsigned lifetime counts beyond exact `2^53` integer conversion in
`AcornVerif.CurrentLifetimeArithmetic` (`count_model`, `count_relative`, `mul_positive_relative`,
`add_nonnegative`). For portable functions and state rails, `AcornVerif.CurrentReduction`
(`expReduce_contract` mapping `[-104, 89]` into exponents `[-151, 129]` and remainder
`|r| ≤ 0.349`, `expReduce_zero_remainder` preserving finite inputs' numerical values including
`-0.0` at exponent 0,
and `exp_admitted_reduction`), `AcornVerif.CurrentExponential`, `AcornVerif.CurrentSeries`,
`AcornVerif.CurrentIntervals`, `AcornVerif.CurrentPortable`, `AcornVerif.CurrentLogarithm`
(`ln_total_contract` returning exact exceptional words `0x7fc00000`, `0xff800000`, and `0x7f800000`),
`AcornVerif.CurrentPrediction`, and `AcornVerif.CurrentState` establish machine-domain range,
monotonicity, and exception contracts rather than ideal transcendental approximation accuracy,
and `AcornVerif.CurrentState`'s projected-state contracts give no bound on raw transient
registers. Universal program properties are limited to their checked
implementation linkage. Compiler/native runtime, filesystem stability, the
reviewed build/gate tools, cryptographic tools and OS remain trusted boundaries,
and the Regula audit's pass rests on the assumption about Acorn that the
[Regula audit](#regula-audit) states.

# Build and source inventory
%%%
tag := "build-and-source-inventory"
%%%

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
`scripts/regula.sh`), while `scripts/verify.sh` admits `scripts/shellcheck.pin`,
requires `shellcheck --version` to match the pinned `0.11.0` release (failing
closed with both the found and admitted versions on any mismatch or absence),
and invokes `SHELLCHECK_OPTS='' shellcheck --norc` so ambient configuration cannot alter
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
admission. In `lean/Bootstrap.lean`, `AcornBootstrap.overrides` inspects every
locked manifest dependency entry even when an earlier dependency is absent, so
missing provisioning cannot hide a later schema or filesystem refusal; both
`AcornBootstrap.packageDir` and `lean/AcornTools/Gate.lean` resolve each locked
dependency directory as Lake of Lean v4.36.0 does (reading the name with
String.toName and mapping it via Name.toString with escape disabled, matching
PackageEntry.dirName), so escaped manifest names such as `«lean-intent»` resolve
to `lean-intent`. `AcornDocument.external` (`lean/AcornDocument.lean`) admits
external prose names strictly by exact equality with
`AcornDocument.externalSymbols` (after normalizing `::` to `.`), so listing a
namespace or type admits no other member of its namespace (every qualified
external name must be listed in full), and the module imports only Lean's
prelude so the Regula proof claim covers it and `AcornDocument.external_listed`.
In `lean/AcornTools/Corpus/Browser.lean`, `AcornBrowserAudit.code` conservatively
strips JavaScript comments, strings, and regex literals and fails closed on
unterminated constructs; its specification table check requires a unique line
containing the Appendix A title with exact heading
`## Appendix A · Constants this document quotes`, then scans from that heading
to the end of `docs/viewer-ux.md` (without stopping at a later heading),
requiring the generated constants table to appear consecutively once and
rejecting any other line containing `|` after that heading.

Numerical proofs use the executing Lean definitions. Native admission checks
their compiler IR, primitive calls, resource contracts and compiler flags. In `lean/AcornTools/Native/Audit.lean`, definition scanning matches `static` rather
than `"LEAN_EXPORT"` for compiler-hoisted `_init_…` constant initializers, and compile
flag admission permits `-fPIC` supplied on Linux because it does not authorize
floating-point reassociation. `AcornVerif.Resource.WordKernel`
(`lean/AcornVerif/Resource/WordKernel.lean`) is a control and resource
abstraction of admitted compiler IR rather than a second implementation of
numerical functions: `lean/AcornTools/Native/Resources.lean` extracts formal
`WordTree` values from typed compiler IR (Lean.IR.FnBody) for finite scalar
operations and the checked u32 halving recurrence (`Acorn.Portable.powLoopWord`,
33 body visits via `AcornNativeResourceAudit.checkHalving` and
`AcornNativeResourceAudit.extractHalving`), plus startup and first-use once-cell
and eager-initializer closures (at most 68 distinct cached initializers and unit
startup/first-use credit at most 575). Weighted costs retain primitive and callee
identities (`CostModel`); the unit interpretation is only a structural regression
budget (no unit denotes seconds, bytes, energy, or a hardware instruction, and
`WordTree.costExec_le_cost` does not assert that an assignment describes a
physical machine without a justified external platform model). Ordinary roots
exclude heap operations except explicit bounded integer egress, startup admits
reviewed constructors (`InitExec`, deduplicated by compiler identity
`InitCell.name`), unknown calls and cycles are rejected with the separately
checked halving loop (`HalvingExec`), and extraction, compiler lowering, and
reviewed native primitives remain trusted boundaries. Because Lean's closed-term
cache is not persistent across imports, `AcornNativeResourceAudit.readOnceSymbols`
reads emitted C under `.lake/build/ir/` using the pinned compiler's symbol
mangling (matching a `static lean_once_cell_t` initializer line with a
corresponding `static` scalar or object declaration) and re-checks scalar types
against IR; the `4096` extraction fuel bounds the extractor only and never serves
as a claimed program execution bound. Primitive IEEE interpretation remains a native assumption.

Native build provenance embeds source, toolchain, and audit identifiers into
`NativeApp` (`lean/NativeApp/Build.lean`), which is a build/OS bootstrap
boundary outside the core algorithm library `Acorn`. In `lean/lakefile.lean`,
the `NativeApp` library and the `acorn-core` and `acorn-viewer` executables
declare Lake's nativeProvenance target (alongside checkpointSync) in
extraDepTargets, so provenanceJob runs before `NativeApp` compiles and
contributes its trace to `NativeApp.Build`. provenanceJob admits
`lean/Acorn/Host/AuditPins.lean` and `viewer/static/index.html` as Git-tracked
regular files, collects tracked regular entries under `lean/` via nativeSources
(every `.lean` and `.c` file, including `lean/Acorn/Host/AuditPins.lean` and
`lean/os/checkpoint-sync.c`, plus `lean/lean-toolchain` and
`lean/lake-manifest.json`), appends `viewer/static/index.html`, resolves real
paths, and sorts them. nativeDigests (shared by singleton hashing in
nativeDigest) rejects paths containing newlines, hashes the list in one
`openssl dgst -sha256 -r` invocation, and requires one lowercase
64-hex-character SHA-256 digest per input in order with the matching path.
provenanceJob requires every resolved real path to lie beneath the repository
root, writes the sorted repository-relative inventory (`acorn-lean-source-v2`)
to `.lake/build/native-source-inventory.txt`, and hashes it to produce the
64-hex-character source digest. It also queries `lean --version`,
`leanc --version`, and `cc --version` (refusing any non-zero exit), writes those
outputs together with the shared strict floating-point flags nativeFloatFlags
(`-ffp-contract=off`, `-fno-fast-math`), the `checkpoint-sync` C compiler flags
checkpointFlags, and the `source=` digest line (`acorn-lean-build-v1`) to
`.lake/build/native-build-identity.txt`, and hashes that file to produce the
64-hex-character build digest. Finally, it reads
`lean/Acorn/Host/AuditPins.lean` (the single owner of
`Acorn.Host.AuditPins.declaredDigest`), requires a unique
`def declaredDigest : UInt64 := 0x` literal with 16 lowercase hexadecimal digits
followed by a newline, and writes the source, build, and audit lines to
`.lake/build/native-provenance.txt`, keying Lake's dependency trace on the
binary contents of all collected sources together with the compiler/flag
settings and sorted source paths. `lean/NativeApp/Build.lean` embeds those three
files at compile time through `include_str`: the private provenance triple,
`NativeApp.sourceInventory` (the source framing for explicitly requested
scientific execution), and `NativeApp.buildRecord` (the compiler settings
recorded beside the source identity). `NativeApp.decodeBuildIdentity` admits the
embedded provenance into `Acorn.Host.Viewer.TelemetryBuild` only when it
consists of exactly three newline-terminated lowercase hexadecimal strings of
lengths 64, 64, and 16; `NativeApp.buildIdentity` supplies that decoded record
to shared telemetry and execution, and `NativeApp.runCore`'s streaming campaign
path (`lean/NativeApp/Core.lean`) and `NativeApp.executeMutationAudit`
(`lean/NativeApp/MutationAudit.lean`) refuse to run when
`NativeApp.buildIdentity` fails admission. Compiler, native toolchain, OpenSSL
hashing, and Lake build orchestration (including trace freshness and that the
build files read by `include_str` correspond to the compiled binary) remain
trusted boundaries: Lean code does not verify that a supplied or embedded build
digest identifies the executing binary
(`lean/Acorn/Host/Viewer/CoreTelemetry.lean`). These digests establish raw byte
identity and mutation detection only; they never supply cryptographic
authenticity, tamper resistance against an untrusted build environment, or a
correctness theorem.

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
[Regula audit](#regula-audit) (360-second deadline), lean-intent's two checks
(180-second deadline) and the frame check (120-second deadline) on the same
commit (each also when an earlier step failed), and, only when ordinary
verification succeeded (so un-admitted sources are never elaborated), the pinned
`no-comments` check (`.no-comments.json`, `comment-ratchet.json`,
`lean/no-comments.pin`, 60-second tracked-file admission deadline and 300-second
execution deadline), passing only when both runs, the audit and all four
post-checks pass. Every post-verification deadline uses GNU coreutils timeout
with process-group SIGKILL and no grace period, matching `scripts/verify.sh`
(exit status `137` on deadline SIGKILL or external SIGKILL fails the check and
the gate). `scripts/gate.sh` isolates every phase's temporary directory (provisioning, both
verification stages and every post-verification check) under a parent-owned
scratch directory removed on exit or cancellation, runs provisioning functions
and external phases in dedicated process groups with interruptible waits (using
direct process replacement so `scripts/verify.sh`'s GNU timeout and its
descendants share the recorded group) so SIGINT/SIGTERM cancellation signals
and reaps active child groups (subject to POSIX Bash's normal
launch-to-PID-recording boundary), and reaps any surviving group members after
each wait returns.
When ordinary verification passed, `scripts/gate.sh` first verifies
`no-comments` cache containment, offline SHA-256 against `lean/no-comments.pin`
(for `darwin-arm64` and `linux-x86_64`) and bounded tracked-file admission
(`admit-no-comments`, timed and bounded separately under its 60-second deadline)
of `.no-comments.json` and its configured ratchet path, workspace directories,
Lake flags (refusing reconfiguring/rehashing flags such as `-R`,
`--reconfigure`, `--rehash` and `--old`), empty tool/workspace-exclude prefixes
and Verso-scoped exclude prefixes alongside `lean/no-comments.pin` and both
workspaces. It then runs the Regula audit in the foreground while lean-intent's
two checks, the frame check and (when admitted) the `no-comments` check run one
after another in a background subshell, passing only when every check and the
background supervisor itself exit cleanly (recording missing timing data as
unavailable rather than zero). Because ordinary verification has
already built every module and executable and synchronized Lake's configuration
cache, the generated override file and the tracked-module stamp inside
`lean/.lake/`, those compiled and cached build artifacts stay unmodified across
the overlapped phase: `sync-config` writes its comparison file inside temporary
storage and creates no files under `lean/.lake/` on a stamp hit (writing an
exclusive staging file beside the stamp only on a stamp miss),
`.no-comments.json` admission forbids Lake reconfiguring flags, and each
bounded phase writes temporary/staging files inside its isolated parent-owned
scratch directory. In that overlapped phase
`no-comments` runs with `--jobs` set to one less than the host CPU count,
clamped between `1` and `6` (3 workers on a four-processor runner and 6 on
larger hosts), leaving a core for Regula's single-threaded kernel replay and
limiting concurrent worker parallelism; the worker cap is a concurrency bound
and does not enforce a hard combined-memory ceiling (measured on macOS arm64,
the overlapped post-verification phase peaked at 6.31 GiB physical footprint at
`--jobs 3` and 6.95 GiB at `--jobs 6`, while Ubuntu runner memory headroom
rests on the 16 GiB runner image). When verification failed, Regula,
lean-intent and the frame check run one after another under their individual
deadlines, and the `no-comments` check is refused without executing the binary.
When executed, `no-comments` checks all scoped `.lean`
files across `lean/` (including `lean/lakefile.lean`) and `site/` code
(`site/AcornSite.lean`, `site/AcornSite/`, and `site/Main.lean`, excluding
`site/AcornDocs.lean` and `site/AcornDocs/` Verso prose), using explicit
`-f lakefile.lean` and `-f lakefile.toml` workspace configuration flags in
`.no-comments.json`, against `comment-ratchet.json` for exact head sync, plus
unconditional monotonic non-growth against the merge-base ratchet alongside
rejecting newly excluded files that still hold comments at the merge base
(tracked files with zero comments carry no ratchet entry). The pinned
`lean-no-comments` v0.3.1 release batches Lake workspace setup and reuses a
persistent worker process across files sharing an identical import header and
environment (spawning fresh processes across distinct headers); while exact
inventory agreement with v0.2.0 is verified on the repository tree and governed
executing/proof modules are barred from defining unsafe or native-plugin
initializers by `lean-boundary-audit`, process reuse across matching-header
files (including tooling modules, site code and imported libraries) rests on
the upstream tool's documented trust assumption that elaborated commands and
imported plugins or initializers do not depend on per-file isolation of
process-global mutable state within a batch.

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
behalf by the agent supervising Acorn's research on 2026-11-03, since the intent-first method
confirms a record before its implementation exists, and it remains until the
listed deliverables migrate to lean-intent's awaiting-implementation
declaration (rbeauchamp/lean-intent#52). That the modules Lake lists are all those of the
package, and that the constant an implementation names is what an executable runs,
are trusted. Each check runs under a `2,000,000` heartbeat budget in Lean's unit
of a thousand (ten times Lean's `200,000` per-declaration default) because
confirmation renders each record and every definition its answers' predicates
reach; the runner is `unsafe` solely so Lean executes module initializers to load
environment extensions when importing compiled modules.

The frame check runs from `lean/AcornTools/Frame.lean`. A target's file freezes
the target's text. A pin file beside it, a regular file ending in `.frame` in
`lean/AcornVerif/Targets/`, freezes what that text reads: it names the target, the
names a submission may change, the names kept and not followed, and, for every
other declaration of the project that the target reaches through types and
definitions, the SHA-256 digest of its printed kind, universe parameters, type and
value. The checker implements SHA-256 directly over UTF-8 bytes
(AcornFrameCheck.roundConstants, AcornFrameCheck.initialHash,
AcornFrameCheck.padded, AcornFrameCheck.compress, and AcornFrameCheck.sha256)
following NIST's
[FIPS 180-4](https://doi.org/10.6028/NIST.FIPS.180-4)
(Secure Hash Standard, August 2015, §4.1.2, §4.2.2, §5.1.1, §5.3.3, and §6.2).
Before AcornFrameCheck.run reads any pin file, AcornFrameCheck.vectorsHold
checks three published digests: the empty message (zero bytes, NIST CAVP
[SHA-256 byte-oriented test vectors](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing),
SHA256ShortMsg.rsp, Len = 0), "abc", which pads to one 64-byte block, and a
56-byte message, which pads to two 64-byte blocks (both from NIST's published
[SHA-256 examples](https://csrc.nist.gov/csrc/media/projects/cryptographic-standards-and-guidelines/documents/examples/sha256.pdf),
one-block and two-block message samples); passing those three digests is a
startup self-check rather than a proof of FIPS 180-4 equivalence. The check
enumerates Git-tracked regular files under
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
since, are trusted. Because AcornFrameCheck.current compares real paths for the
named root module alone before AcornFrameCheck.imported loads its dependency
closure (a boundary shared by verification and `frame-check print`), Lean's
search path, which the bootstrap's `lake exe` sets with the workspace's own
library directories first, is also trusted to resolve the pinned module's
imports to the compiled artifacts Lake checked. The check relies besides, as every check of the gate does,
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

The arrangement on GitHub differs from the pipeline's as follows. Separate steps of
the workflow download elan's and ShellCheck's (`0.11.0`, `scripts/shellcheck.pin`) pinned releases in every run and install each only
after its archive's SHA-256 matches. The script's provisioning runs in a step
of its own, whose 12-minute limit bounds a stalled download and is no check's
deadline, and the script's provisioning in the last step then finds the
dependencies current. Nothing is stored between runs: every run
provisions everything from its pinned sources and builds from cold project
outputs. A copy stored by an earlier head of a pull request, which controls its
own workflow, could otherwise be restored and trusted by a later head whose own
changes show nothing of it. The merge-gate step runs `exec ./scripts/gate.sh` (so runner cancellation
signals reach the gate directly) under an 18-minute
`timeout-minutes` limit and the workflow's gate job carries a 30-minute `timeout-minutes`
limit, where the pipeline's Test step has none; a successful provisioning step
requires its duration handoff to `$GITHUB_OUTPUT` to succeed, while cancellation
reporting stays best effort; each of verification's two stages
keeps its 360-second deadline, and `scripts/gate.sh` individually bounds
`no-comments` admission (60 seconds), the Regula audit (360 seconds),
lean-intent checks (180 seconds), frame check (120 seconds) and `no-comments`
execution (300 seconds). On every run that reaches the provisioning or merge-gate step (including
provisioning failure/cancellation and gate failure/cancellation after
`scripts/gate.sh`'s pre-execution admission and trap setup, while the runner
can still publish step outputs; failures in earlier workflow steps such as
commit check, checkout, package admission or elan provisioning, or pre-trap
startup admission, exit without writing a phase table), the workflow and
`scripts/gate.sh` print a per-phase timing summary line, write a per-phase
duration table (provisioning, dependency re-check, verification stages 1 and 2,
`no-comments` admission, Regula, lean-intent, frame, `no-comments` execution,
post-verification wall time, merge-gate total and workflow elapsed time from
commit identification through gate completion, excluding runner setup and
post-job checkout cleanup, recording actual phase starts and completions and
marking unreached or interrupted phases explicitly) to `$GITHUB_STEP_SUMMARY`
when set to a non-symlink regular file path (failing a normal gate run if
writing that summary fails), and emit GitHub Actions `::warning::` budget
annotations when a phase or total exceeds its early-warning target
(provisioning over 8 minutes, verification stages 1 and 2 combined over 6
minutes, Regula over 4 minutes, `no-comments` execution over 3 minutes, merge
gate over 10 minutes, or workflow elapsed time over 15 minutes) so slowdowns
surface before hitting the hard ceilings. Warnings surface creeping duration
regressions without loosening any check; hitting a per-check, step or job hard
limit fails the check or job. This cold-provisioned single-job shape, slower
than two jobs with stored dependencies, was decided on the owner's behalf by the
agent supervising Acorn's research.

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
`gate: verification exited 0; Regula audit beside lean-intent, frame and no-comments checks`
(or `gate: verification exited 0; Regula audit beside lean-intent and frame checks`
when `no-comments` fails pre-execution integrity or admission checks, or
`gate: verification exited N; Regula audit` when verification exited
non-zero) for verification's two stages together,
`gate: Regula audit exited N; lean-intent checks`,
`gate: lean-intent checks exited N; frame check`,
`gate: frame check exited N; no-comments check` and
`gate: no-comments check exited N` (or
`gate: no-comments check refused (integrity check failed)` when the cached
binary fails cache-containment or offline SHA-256 verification before starting,
`gate: no-comments check refused (admission check failed, exit N)` when
`admit-no-comments` fails before starting the binary, or
`gate: no-comments check refused (verification failed)` when either stage of
ordinary verification failed); if the background supervisor exits without
producing an observed integer status for a check, the script reports
`status unavailable (background supervisor exited N)` for that check rather
than synthesizing an exit status, and fails the gate. A check terminated by its
hard process-group SIGKILL deadline or by an external SIGKILL reports exit
status `137`. When verification passed, the
verification-exited line prints before the overlapped post-verification checks
start, while the Regula, lean-intent, frame and `no-comments` status lines wait
until both the Regula audit and the background subshell finish. Before the final
exit check it prints `gate: phase timings (s): ...` with each phase's measured
duration, and it prints `gate: every merge check passed` last, and only when
every status is 0. A head that holds another revision of the script runs that revision's
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
`gate: no-comments check refused (integrity check failed)`,
`gate: no-comments check refused (admission check failed, exit N)` or
`gate: no-comments check refused (verification failed)` before starting the
binary, or reports `status unavailable` when the background supervisor fails to
record a child exit status, each of which still fails the gate), and an attempt without the passing line is
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
and reuse loaded dependency regions (`lean/AcornTools/OwnershipAudit.lean` keeps
importModulesCore shared dependency regions alive with leakEnv set until the
bounded audit process exits so sibling environments do not free shared regions).
Each IR reference must belong to that
entry's actual compiled import closure; data loaded for another entry cannot
satisfy this check. Shared regions live only for the audit process, and no prior
acceptance result is cached. In `lean/AcornTools/Boundary/Audit.lean`,
`AcornBoundaryAudit.flushOLeanCache` evicts compacted-region Name keys from Lean
v4.36.0's oleanRootCacheRef (Lean/Util/Path.lean, lines 134 to 147) before
withImportModules unmaps `.olean` regions by calling findOLean on the static
literal Init under two distinct search paths and then restoring searchPathRef;
`AcornBoundaryAudit.command` runs compiled admission before source admission
because source admission keeps its parser environment mapped until exit and an
already-mapped module cannot be mapped again (later environments would read and
relocate it in full), and every import resets initializer execution so
initializers run only for the trusted parser environment. Source, boundary, native-route and browser checks
remain required. Standalone ownership, theorem and corpus commands remain
available for focused diagnostics.

Checks that do not depend on one another run at once: the two source admissions
with Lake's target inventory before the project build, and compiled boundary,
native, browser-kernel and ownership admission after it. Each of these
prints the output of a step whole when the step ends, and all of them are reaped
before a failure is reported. The site check runs after these admissions, also
when one of them fails, because `site/lakefile.toml` requires `../lean` by path
and building the documents can rebuild this package's modules into the build
directory under `lean/.lake` that the admissions read. The build
requests library modules first, ordinary executables next, and executables whose
Lake configuration names a target in needs together with their root modules last:
Lake resolves the build graph on one thread in request order and waits for needs
before reading the next request (Module.recFetchPreSetup, Lake of Lean v4.36.0),
and a root-module request resolves to its executable (Package.findTargetModule?),
so every other job is scheduled first.
In `lean/lakefile.lean`, passing `-j2` through weakLeanArgs bounds each compiler
process to two threads, where the default is one for each processor, as a weak
trace-neutral flag that changes no module elaboration; debug.skipKernelTC stays
at its default (false), so the build kernel-checks every proof term alongside
Regula's `lake lint` replay; `AcornVerif` sets allowNonModules to true solely to
suppress Lake's requiresModuleSystem warning from Mathlib because `AcornVerif`
imports non-module `Acorn` files (refused inside module files), changing no
elaboration; and the generator-only `world-certificates` executable excludes
agent composition, the campaign runner and the random-policy comparator from its
import closure (`AcornBoundaryAudit.generatorOnly`,
`AcornBoundaryAudit.generatorExcluded`), though its closure holds the attempt
protocol and campaign admission through the curriculum and no audit enforces that
the tool starts no attempt.

# Regula audit
%%%
tag := "regula-audit"
%%%

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
contract by name. `docs/decision-contracts.md` gives
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
feature bank, stated as SplitMix64 on Lean core's bit vectors. `docs/decision-contracts.md` names those statements, the groups
of shared definitions that have none yet, and each proposition with its theorem.

No check of Acorn finds a decision function that is not registered. `docs/decision-contracts.md` lists the groups of definitions with
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
test with the checker. `docs/decision-contracts.md` lists the functions of `lean/AcornVerif/Decisions.lean` that keep no
kind, with the reason for each and which of them are also remaining work of
issue 105.

The audit is a second check of the merge gate and is not part of
`./scripts/verify.sh`. It builds the claimed modules again where Lake's traces
differ and runs Regula's checker, whose replay of the claim's cone does not fit
beside the ordinary checks inside the 360-second deadline. The gate runs it
after ordinary verification, under its own 360-second deadline, and requires
both before a merge. A pass is Regula's
proof verdict, with the meaning and the assumption that the section above
states; it does not replace review.

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
compiler-trusting proof, or a compiled unsafe or partial declaration outside
RG1006's exempted forms (a partial recursion helper of a terminating recursive
definition, or the unsafe implementation half of a verified compiler-generated
constructor-index pair). The Regula audit refuses each of them, and the merge
gate requires it. Run `./scripts/regula.sh` for it before proposing a change to
a Lean source.
Ordinary verification still refuses the words `axiom`, `sorry`, `unsafe`,
partial and `native_decide` in every executing and proof source, through source
admission, and a proof hole through the build, where a warning is an error.

*Project axioms.* RG1001 refuses an axiom declared in a claimed module. The tools
make no such check.

*Axioms that a declaration depends on.* RG1003 refuses a constant of a claimed
module with a transitive axiom outside propext, Quot.sound and Classical.choice,
and RG1005 one whose axioms exceed the standard-logical profile. Both rules
examine every public, private and generated constant—theorems, definitions and
instances—and read what each constant mentions as Lean's kernel checks it, so
an axiom that a claimed constant reaches only through an inductive type's block
counts, and new declarations cannot bypass the audit through namespace aliases
or source formatting. The tools make no such check across all claimed constants.
To complement RG1003 and RG1005, the tool module `AcornTools.AxiomPins` pins
the exact transitive axiom sets of selected theorems (`AcornTools.AxiomPins.pins`)
during elaboration via a compile-time command-elaboration check
(`AcornTools.AxiomPins.verifyPins`, backed by Lean's Lean.Elab.Command and
Lean.collectAxioms) that fails the build if the pin table is empty, any pinned
declaration is missing from the environment, any pinned declaration or expected
axiom is duplicated, or a declaration's sorted transitive axiom set differs in
either direction (extra unexpected axiom or missing expected axiom) from its
pinned set. Verification builds every discovered module, `AcornTools.AxiomPins`
included, so any drift in a pinned dependency set fails the build; the module
imports the proof library and lies outside the Regula claim with the other tools.

*Proof holes and compiler-trusting proofs.* RG1002 refuses a constant that
depends on Lean's proof-hole axiom, directly or through an import, and RG1004 one
that depends on an axiom that `native_decide` or a related tactic adds. Both rules
read the transitive axiom set. The tools make no such check.

*Unsafe, partial and looping declarations.* RG1006 refuses a constant of a
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

*Kernel replay.* `lake lint` checks every constant of the claim's cone in Lean's
kernel again from an empty environment, so a proof that the build's own kernel
check skipped is checked there. Regula's specification records a module that
added, with the kernel check skipped, a theorem of False whose name Lean marks
as internal and that nothing mentions: Regula v0.12.0's three commands passed
it, and v0.13.0's `lake lint` gives an incomplete verdict, RG2001, with the
kernel's refusal. The tools make no such check.

*Native replacements: the tools refuse more.* The theorem inventory refuses each
declaration of a module of Acorn, AcornVerif, NativeApp, AcornDocument or Entry
that carries a replacement attribute or an extern attribute, whatever reaches it
and whatever is proved about it, except a verified compiler-generated
constructor-index replacement that Lean v4.36.0 emits for every safe, non-Prop,
non-builtin inductive type whose constructor count is not one
(`AcornTheoremCount.isCompilerCtorIdx`, matching Lean v4.36.0's
Lean/Meta/Constructions/CtorIdx.lean, lines 40 to 141, and Regula v0.13.1's
structural check Regula.Load.ctorIdxFormOf and Regula.Closed.Tables.ctorIdxPair
on the pair and its toolchain constructor-tag helper). The Regula audit
reads replacement and extern attributes only to qualify RG1006's exempted forms
(recursion helpers and constructor-index pairs) and has no general rule refusing
them on safe declarations: a pass says nothing about what a compiled program
runs. Source admission refuses both attributes as words in every executing and
proof source, so the inventory adds the declarations that elaboration generates.
This check runs once, in the theorem inventory. A copy in the compiled boundary
admission would repeat the same predicate for a subset of the same modules in
the same command, `./scripts/verify.sh`.

*Reach of each entry: the tools refuse more.* The ownership audit follows the
compiler's intermediate code from the entry point of each executable, the tool
executables among them. It refuses an extern or a proof hole in a maintained
module on the way, and requires that the entry reaches each definition that
`entryUses` lists for it, the claimed entry function first. Regula examines no
compiled code.

*Module inventory: the tools refuse more.* The Lake configuration sets
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

*Executable inventory: the tools refuse more.* Ownership admission refuses a Lake
executable whose target name and root module are not a pair of `executables`,
and a listed pair that Lake does not have. It also requires that a module
declares `main` exactly when it is the root module of an executable or is
Bootstrap, the interpreted build launcher. The list is also the Lean owner of the
executable names that the build order and this document read.

*Decision registrations.* The ownership audit requires a contract with a kind for
each registered decision function whose result is not `Decidable`, as stated
above, and counts only a contract about the whole function whose condition
applies its kind to that function (`lean/AcornTools/OwnershipAudit.lean`). Its
subject (wholeFunction) must be a constant instantiated solely with the arguments
its type takes implicitly, rejecting explicit applications such as `f x₀`. Its
condition (appliesKind) accepts only two closed forms for Regula.Decides,
Regula.DecidesSoundly and Regula.DecidesCompletely: `K accepts spec` lacking the
final explicit argument (which the contract supplies with the implementation), or
`fun g => K accepts spec t` whose final explicit argument mentions the bound
variable; any other form, such as `fun _ => K accepts spec id`, which ignores its
argument and decides the identity function, does not count. Regula reads no
registration.

Regula has no rule for the import layers of the learned-only boundary, the
capability owners, source syntax admission, the departures register, native
admission, the corpus checks or the required proof links. Those checks are
Acorn's own.

# Review protocol and the rule on runs
%%%
tag := "review-protocol-and-the-rule-on-runs"
%%%

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
guide. Rendering in `site/AcornSite/Markdown.lean` is total and fails closed by
refusing unrendered Verso constructs (unordered, ordered and definition lists,
block quotations, mathematics, footnotes, images and unrecognized extensions) by
name rather than dropping or approximating them. The rendered pages stay in the working copy; nothing is published.

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

# Mutation diagnostics
%%%
tag := "mutation-diagnostics"
%%%

*Pinned digest: {spliceCode}`digest .declared`*

In work on a change, the command below is run only on the owner's authorization
for that run.

```spliced sh
s!"lean/.lake/build/bin/{executable "acorn-core"} audit --expect {digest .declared}"
```

The expected digest has one form, `0x` and exactly sixteen lowercase hexadecimal digits:
it is a hash identifier, not a number, so it is not read as a command-line number and
digit-only text such as `10` is refused.
Paired checksum {spliceCode}`checksum .declared`. The deployed arm runs the ranked profile
with the declared D6 exploration rate. `NativeApp.AuditArm.executeCampaign` runs
the `annealed` incumbent arm with `NativeApp.AuditArm.construction`'s
spatial-subtask profile via `AgentConstruction.runCampaign` without telemetry or
checkpoint authority, while the declared and differential arms traverse the
ordinary public native campaign. The optional ./scripts/verify.sh diagnostics
command runs all {splice}`numberWord auditArms.length` fixed arms under the same deadline. All {splice}`numberWord auditArms.length` pins record
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

# Checkpoint admission
%%%
tag := "checkpoint-admission"
%%%

Format {splice}`toString Acorn.Checkpoint.formatVersion` holds the exact image of the agent:
every field of its temporal state, the option models, primitive credit, the rate schedule
and every process-local reference included. Every earlier format is refused
({decl}`AcornVerif.CurrentCheckpoint.previous_generation_unloaded`). Format 20 stores, after
each option slot's trajectory, that option's off-policy questions, which the agent no longer
holds (PAR-18, retired). Format 19 has the layout of format 20, but its weights were placed by
the hashes that read their first two words only through their XOR, so a saved weight can sit
at the slot of another feature. Load checks dimensions,
identifiers, criterion and step order
in the header, then reads the image with every stored word in its own domain, every
learner through the check of its invariant and the agent's two invariants. An incompatible
image is refused and writes to that file are disabled. Loading the bytes that a save of a
state writes returns that state, for every state of the resumable construction
({decl}`AcornVerif.CurrentCheckpoint.load_saved`). The world restarts, and the host begins a
new session of the predictive-agreement evaluator. Filesystem persistence relies on the narrow C file-sync helper (`lean/os/checkpoint-sync.c`), native IO, and the operating system (`Acorn.Checkpoint.Store.save` in `lean/Acorn/Host/Checkpoint/IO.lean`). `Store.save` admits only supported profiles within `maximumBytes`, reserves an exclusive temporary file `.oak-{pid}-{seq}.tmp` up to 64 retries via mutex-serialized sequence numbers (assuming stable parent directories and temporary names against external mutation, with concurrent writers resolving last-rename-wins and no compare-and-swap guarantee), writes and flushes the buffer, and reports success only after three steps in order: invoking `checkpoint-sync file` on the complete temporary file, renaming it onto the destination (failures before or during rename trigger best-effort removal of the reserved temporary file without replacing the original error and rethrow without inspecting or restoring the destination: failures before rename never touch the destination under the stable-path assumption, whereas a rename error leaves the destination untouched only where the filesystem guarantees that the failed rename did not take effect, because a filesystem can report an error after performing the rename; cleanup ends once rename succeeds, after which the temporary path no longer names this writer's file, so directory-sync failure attempts no temporary removal), and invoking `checkpoint-sync directory` on `destination.parent.getD "."` (since `Acorn.Checkpoint.temporaryPath` extends the destination filename, the rename's entry lies in the destination's parent, or in the inherited working directory when the destination has no separator). Where each sync reaches permanent storage, ordering temporary-file sync before rename keeps an image whose bytes are not yet there from being named by the destination and ordering directory sync before the report keeps the report from preceding the entry, so a power loss at any earlier point leaves no report and leaves the destination naming either the previous image or the new complete one.

Each sync establishes what the platform's own documentation says of the call `checkpoint-sync` makes, and only that. On Apple platforms, the build requires F\_FULLFSYNC in `<fcntl.h>`. macOS fsync(2) states that fsync moves data from the host to the drive, which may hold it and lose it on power loss, whereas fcntl(2) states that F\_FULLFSYNC does the same as fsync and "then asks the drive to flush all buffered data to the permanent storage device" (naming HFS, MS-DOS (FAT), UDF, and APFS as implementing it and listing no error for it). A successful save establishes only that those flush requests succeeded when F\_FULLFSYNC actually succeeded for both the file and the directory, not proof that the drive persisted the bytes to permanent storage; moreover, because `checkpoint-sync` ignores warning-write failures and requestSync suppresses stderr-forwarding errors, a silent fallback to fsync can succeed without a visible warning, so absence of stderr output does not identify which sync path ran. Moreover, the macOS manuals do not discuss directories apart from files; that a directory sync covers its entries is inferred from fsync(2)'s "all modified data and attributes". On a macOS filesystem lacking F\_FULLFSYNC, `lean/os/checkpoint-sync.c` falls back to fsync on ENOTTY, ENOTSUP, or EINVAL and prints a stderr warning forwarded by requestSync (failing to print the warning does not change that success); in XNU (`bsd/kern/kern_descrip.c`, `xnu-12377.121.6`, lines 3978–3987, error-code check at lines 3982–3983), that same error-code triple promotes F\_BARRIERFSYNC to F\_FULLFSYNC rather than failing unsupported filesystems directly. A success then establishes only what fsync(2) states—that the data reached the drive, which can lose it or write it out of order on power loss—and losing both this save and the replaced image is accepted risk on such a filesystem in exchange for keeping a save that a refusal would discard; every other F\_FULLFSYNC error, EIO included, fails the save. On every other platform, `checkpoint-sync` invokes fsync directly and fails on any error. Linux fsync(2) states that the transfer "includes writing through or flushing a disk cache if present", that the directory entry requires an explicit fsync of the directory, and that older kernels and lesser-used filesystems do not know how to flush disk caches. POSIX leaves the nature of the fsync transfer implementation-defined, so elsewhere a successful fsync establishes only what that operating system documents, and a filesystem whose fsync does not flush the disk cache stops at the drive as below.

Where a sync stops at the drive (the macOS fsync fallback, or a Linux or other filesystem that does not flush the disk cache) or a drive ignores or misreports a flush (fcntl(2) notes certain FireWire drives, which no software here can detect), the sync order does not order what reaches permanent storage: macOS fsync(2) states that the drive "may also re-order the data so that later writes may be present, while earlier writes are not", so a power loss before or after a successful report can leave the destination naming an incomplete image with the replaced image gone (losing both the previous save and this one), and not every incomplete image need raise a load error because frame checksums detect accidental mutation only and body completeness rests on image admission (`lean/Acorn/Host/Checkpoint/Frame.lean`). A failed directory sync fails the save after rename has already pointed the destination at the new complete image with durability unconfirmed. No report covers these accepted risks: non-flushing filesystems and drives that ignore or misreport a flush; entries of parent directories above the destination's parent directory, which are not synced so power loss soon after creating them can lose them and the checkpoint with them; and crash-atomic rename, which is assumed of the filesystem. On the read side, readChunks in `Acorn.Checkpoint.readBounded` reads `min (remaining + 1) 65536` bytes per call up to `maximumBytes + 1` (continuing short reads to EOF and failing oversized inputs without trusting a file-supplied length), `Acorn.Checkpoint.loadFile` invokes `Acorn.Checkpoint.resume`, and `Acorn.Checkpoint.Store.hooks` maps `.noFileOrDirectory` to `.missing` and every other load error to `.refused` (disabling writes through `Acorn.Host.WritableCheckpoint.admit` while save errors remain visible to the runner's failure counter).

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

Every lifecycle decision the supervisor makes about the core process and the run's published state
is made by one pure step, `Acorn.Host.Viewer.Supervision`, except the actor's pre-launch check of
the ranked core's executable file below: a closed state, the events the native
actor `Acorn.Host.Viewer.Supervisor` hands it, and one step per event or per outcome of the call
it waits for, which returns the next state and the effects to perform. The actor reads the
world, performs the effects in order and then the call, and hands the call's outcome back before
it reads anything else; it is effects, with no theorem of its own. Each serving turn
({decl}`Acorn.Host.Viewer.Supervisor.step`) reads, while nothing is pending: the identity a
process reported, at most one queued command, the process slot, the identity again, so that a
reaped process's last report is attributed before any launch or archival, and then a tick; a
closing turn (`Supervisor.closeTurn` in `lean/Acorn/Host/Viewer/Supervisor.lean`) takes no
command from the queue and closes the command mailbox. The state the step returns is stored before its effects run, so a native error that
stops the effects after it leaves that state, and the next turn goes on from it, as a restarted
viewer goes on from the state file. A supervision is sealed by
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
installs a run other than the one it retires ({decl}`Acorn.Host.Viewer.Core.replaced_identity`);
the instants recorded by steps and outcomes do not go back, whatever the clock reads
({decl}`Acorn.Host.Viewer.Core.instant_later`, {decl}`Acorn.Host.Viewer.Core.step_last`,
{decl}`Acorn.Host.Viewer.Core.resume_last`); and
every result first installs its own lifecycle and publishes its control record from it
({decl}`Acorn.Host.Viewer.Stepped.effects_settle`). The operating system's process, signal and wait
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
({decl}`Acorn.Host.Viewer.PersistedState.unstarted`). For every Clear configuration, every durable
state that intends to stay stopped, and every state reached from the start on it by steps on
events that hold no operator's Start and by outcomes of the pending calls: the lifecycle admits no
reservation at any instant and intends to stop, and the call the state waits for, if any, is no
spawn and writes no state that intends to run
({decl}`Acorn.Host.Viewer.Reached.stopped_spawns_nothing`;
{decl}`Acorn.Host.Viewer.Reached.unstarted_spawns_nothing` states it for the state built with no
state file). The relation these statements are about covers one supervisor's lifetime: one start,
its steps on events and the outcomes of its pending calls. It ends with that viewer; it reads no
state file and starts no second viewer. The states it reaches are the states of a run and no
others ({decl}`Acorn.Host.Viewer.Reached.ran`, {decl}`Acorn.Host.Viewer.Ran.reached`). The
statement is not empty: from the start on every durable state that admits a launch, there are
events that hold a Start and a state reached by them that waits to spawn the first generation
({decl}`Acorn.Host.Viewer.Core.start_spawns`). That is a statement of existence, whose witness has
every call between the Start and the spawn succeed; a Start whose intent cannot be written reaches
no spawn. The state built with no state file admits a launch for every seed within the browser's
integers ({decl}`Acorn.Host.Viewer.Core.unstarted_launch`), and the control record of the start on
that state says the run is desired stopped and actually stopped
({decl}`Acorn.Host.Viewer.Core.start_control`).

A state file is decoded only when it is a JSON object that holds the six members of the state,
each admitted, and beside them at most a schema version and a child record; any other is refused.
Two things then decide whether the intent it records is kept. The first is the version: the
natural number that the `schema_version` member spells in decimal digits alone, of any size
({decl}`Acorn.Host.Viewer.stateVersion`). A member that is absent, or that is spelled any other
way, as a string or as a number with a sign, a fraction or an exponent such as `3e0`, is no
readable version and marks an earlier version's file. Every state the decoder returns for a state
file whose schema version does not read as the current one intends to stay stopped
({decl}`Acorn.Host.Viewer.PersistedState.decode_earlier`), and the statement above holds of the
supervisor started from a state that was successfully decoded from an earlier version's file
({decl}`Acorn.Host.Viewer.Reached.earlier_spawns_nothing`). Before the file carried a version, the
viewer wrote a running intent in it when it found no file, with no Start, so such a file cannot
show that a Start set its intent. For a file that names another natural number the decoder returns
an error ({decl}`Acorn.Host.Viewer.PersistedState.decode_other`), and so it does for a file whose
schema version is a number whose digits spell two to the power 64 or more
({decl}`Acorn.Host.Viewer.PersistedState.decode_wide`).

The second is the child. With every state it saves, a viewer writes the record of the child its
supervisor would start ({decl}`Acorn.Host.Viewer.childRecord`): the executable's path, its length
in bytes, the 64-bit FNV-1a digest of every byte of the file
({decl}`Acorn.Host.Viewer.fileDigest`), and the argument vector at a reference launch. One action
reads the file at that path, its length and its digest, and a file that cannot be read whole gives
no record; the bootstrap reads it with that action when the viewer starts. A launch under `--cmd`
has
no record, because the process a shell starts for a command depends on the working directory, the
environment and the files the command names. The decoder returns a running intent only for a file
that names the current version and the record of the launch that reads it, which must have one
({decl}`Acorn.Host.Viewer.PersistedState.decode_running`). Every state it returns to a launch with
no record, or with another record than the file names, intends to stay stopped
({decl}`Acorn.Host.Viewer.PersistedState.decode_unbound`), and the statement above holds of the
supervisor started from such a state ({decl}`Acorn.Host.Viewer.Reached.unbound_spawns_nothing`).
So a running intent saved while the supervisor's child was one process is not taken as a Start for
another: a Start given under a fixed command does not start the ranked core at a later launch, and
neither does one given for a core at another path, of another length or content, or with
other arguments. Sameness is equality of the two records and no more. This part is read from the
code and not proved: before the ranked core is started, the first time and at every restart, the
actor reads the executable's file again by the same action and compares its length and digest
({decl}`Acorn.Host.Viewer.ProgramReading`) with what the viewer read when it started, whether or not
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
({decl}`Acorn.Host.Viewer.PersistedState.launch`: a run that has started a process needs a next
agent epoch within the browser's integers) and the writes and the spawn that follow succeed.

The rest is read from the code and not proved. The actor hands the step an operator's Start only
for a command that was submitted to its queue, which the bootstrap does for the `--start` flag and
the HTTP server for an admitted control request. The bootstrap hands the supervisor the state it
read or built. Every state the actor writes carries the record of its own child. Of the text the
viewer writes, the other fields of a state read back as written, and a running intent reads back
as running exactly for a launch with the same, present record: a running intent written under
`--cmd`, which has no record, reads back stopped, by design.
{decl}`Acorn.Host.Viewer.RunDirectory.readState`
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
what the decoder ({decl}`Acorn.Host.Viewer.PersistedState.admit`) returns as its source. A state
built with no file ({decl}`Acorn.Host.Viewer.StartSource.absent`), or read from a current-version
file taken with the intent it records ({decl}`Acorn.Host.Viewer.StartSource.saved`),
is written in the supervisor's construction, before the listener binds. An earlier version's
file, whatever intent it records ({decl}`Acorn.Host.Viewer.StartSource.earlier`), and a
current-version file with a running intent, when this launch lacks a child record (including a
`--cmd` launch, whose own running file records `"child":null`) or its record does not match the
file's ({decl}`Acorn.Host.Viewer.StartSource.other`), are left on disk exactly as they are
({decl}`Acorn.Host.Viewer.StartSource.kept`) until the listener is bound. The bootstrap then
prints and flushes the line that says why the run is shown stopped, under the `--start` flag as
well, and only then publishes the stopped state it started from, in the current schema with this
launch's record,
before it prints the ready line, before the `--start` flag submits its Start and before any
command is processed. If the line cannot be written or flushed, the viewer exits before the
publication and the file is still the original. So a start-up that fails before that publication, with or without the
`--start` flag, leaves the next viewer the same file and the same reason, and such a file is read
as an earlier version's ({decl}`Acorn.Host.Viewer.StartSource.earlier`), or as an unbound running
intent ({decl}`Acorn.Host.Viewer.StartSource.other`), once: in the first launch that publishes
the stopped state. That is the boundary, and no other: the reason is not lost by a failure before
the publication, and after the publication it has been given, in that launch's first control
record and on standard output, and is not given again. After it, a viewer of the earlier version started on the directory meets a file
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
line that says why ({decl}`Acorn.Host.Viewer.startAccount`) is in the reason of the first control
record the supervisor publishes, under the `--start` flag too. A page that connects while that
record is current shows the line; one that connects after a later transition has published its
record is sent that record and shows that transition's reason. The viewer also prints the line on its standard output, at most once in a launch: for a file
left as it is until the bind ({decl}`Acorn.Host.Viewer.StartSource.kept`: an earlier version's,
whatever intent it records, or a current-version file with a running intent when this launch
lacks a child record — including a `--cmd` launch — or its record does not match the file's)
the line is printed and flushed after the listener is bound and before the stopped state is
published, under the `--start` flag as well; for no state file, or a file of the current version
that says stopped, it is printed after the ready line and not under the flag. Under the flag the Start is submitted after the listener binds and is handled at a later
turn of the actor. The viewer says nothing of this kind when the start state is running.

The explicit-start statement above starts from a durable state that intends to stay stopped;
browser Stop persistence closes the crash window between acknowledging a browser Stop and
writing `desired = .stopped` to `state.json`. In the control endpoint
(`lean/Acorn/Host/Viewer/HttpServer.lean`) and supervisor actor
(`lean/Acorn/Host/Viewer/Supervisor.lean`), {decl}`Acorn.Host.Viewer.Supervisor.submitControl`
holds an admitted `stop` request behind a promise until the supervisor actor completes the
state-file write rather than replying on queue admission alone (and
{decl}`Acorn.Host.Viewer.Supervisor.submit` refuses `.stop` so callers cannot bypass durable
dispatch). For the pure supervisor step,
{decl}`Acorn.Host.Viewer.Core.step_no_ackStop` shows no step emits
{decl}`Acorn.Host.Viewer.Follow.ackStop`; {decl}`Acorn.Host.Viewer.Core.resolve_ackStop_spec`
and {decl}`Acorn.Host.Viewer.Core.resume_ackStop_spec` establish that
{decl}`Acorn.Host.Viewer.Follow.ackStop` is emitted only upon a successful write
whose written {decl}`Acorn.Host.Viewer.PersistedState` has `desired = .stopped`,
and {decl}`Acorn.Host.Viewer.Core.resume_error_no_ackStop` ensures every
write-error outcome omits {decl}`Acorn.Host.Viewer.Follow.ackStop`.
{decl}`Acorn.Host.Viewer.Core.stop_acknowledges_or_refuses` covers every supervisor state
(idle or busy, open or closing/closed, current or retired owner, with or without a waiting
replacement): stepping `.command .stop` either refuses immediately via
{decl}`Acorn.Host.Viewer.Follow.refuseStop` without emitting
{decl}`Acorn.Host.Viewer.Follow.ackStop`, or schedules a `.writeState` of a stopped
{decl}`Acorn.Host.Viewer.PersistedState` (without acknowledging on the step) whose resolution
emits {decl}`Acorn.Host.Viewer.Follow.ackStop` on write success and
{decl}`Acorn.Host.Viewer.Follow.refuseStop` without {decl}`Acorn.Host.Viewer.Follow.ackStop`
on write error. Under an interleaving state machine over disk updates (including indeterminate state-write
rename errors via {decl}`Acorn.Host.Viewer.CrashStep.writeFailIndeterminate`), crashes between
any two steps, and reboots (including optional startup state write-back and arbitrary Clear
configurations) ({decl}`Acorn.Host.Viewer.CrashState`, {decl}`Acorn.Host.Viewer.CrashStep`,
{decl}`Acorn.Host.Viewer.CrashReached`, {decl}`Acorn.Host.Viewer.CrashState.Invariant`,
{decl}`Acorn.Host.Viewer.CrashReached.invariant`),
{decl}`Acorn.Host.Viewer.PersistedState.encode_decode_stopped`,
{decl}`Acorn.Host.Viewer.CrashReached.crashed_disk_stopped` and
{decl}`Acorn.Host.Viewer.CrashReached.startup_cannot_resume_running` prove that
once {decl}`Acorn.Host.Viewer.Follow.ackStop` has been observed in supervisor processing order
with no later Start admitted by an idle, open supervisor (ordered at the actor's acknowledging
resolution rather than browser HTTP receipt time, so a concurrent Start processed after that
resolution supersedes it), a crash at any point leaves the on-disk state
stopped (or absent mid-Clear archive), so whenever a reboot loads the state via
{decl}`Acorn.Host.Viewer.DiskState.BootState` (covering both missing-file startup and any
successful parse and decode), the loaded state has `desired = .stopped` and never resumes
running without a later explicit Start, while
{decl}`Acorn.Host.Viewer.CrashReached.stop_never_acked_on_write_error` proves that a failed
write step — whether the failure leaves the previous disk entry untouched
({decl}`Acorn.Host.Viewer.CrashStep.writeFail`) or publishes the temporary file despite
reporting an error ({decl}`Acorn.Host.Viewer.CrashStep.writeFailIndeterminate`) — leaves
`ackedStop` unchanged without emitting {decl}`Acorn.Host.Viewer.Follow.ackStop`.
{decl}`Acorn.Host.Viewer.exists_stop_crash_restart_witness` constructs a
`stop -> write -> ack -> crash` trace from every running persisted state with a conditional
boot extension for every admissible {decl}`Acorn.Host.Viewer.DiskState.BootState`, and
{decl}`Acorn.Host.Viewer.exists_stop_crash_reboot_populated` unconditionally inhabits the full
`stop -> write -> ack -> crash -> boot` trace by proving `Json.parse` and
{decl}`Acorn.Host.Viewer.PersistedState.decode` succeed on the published stopped file.
The boundary between these theorems and the host program is read from the code and not proved:
{decl}`Acorn.Host.Viewer.RunDirectory.writeState` writes and flushes an exclusively created
temporary file and renames it over `state.json` under the run directory's stable-path
assumption; neither the temporary file nor the directory is fsynced (power-loss durability is
not claimed), and visibility of complete bytes without torn files rests on local-filesystem
atomic rename semantics. Stop durability likewise rests on Acorn's exclusive single-viewer
run-directory ownership premise ([interrupted-launch recovery](#interrupted-launch-recovery) and
UX-42 in [the viewer specification](viewer-ux.md)) alongside the run directory's stable-path and
no-external-mutation assumptions: {decl}`Acorn.Host.Viewer.RunDirectory.open` allocates fresh
per-process IO mutexes on each open rather than an inter-process lock, so atomic local rename
prevents torn writes from one viewer process but cannot prevent a second concurrent viewer that
already read `desired = "running"` — or an external writer replacing the path or mutating
`state.json` — from publishing a stale state after the first viewer acknowledges Stop. Although {decl}`Acorn.Host.Viewer.CrashStep.writeFailIndeterminate`
models an ambiguous `state.json` rename failure (such as POSIX.1-2017 `rename` EIO
or Linux NFS rename-despite-error) without weakening the stopped-disk or no-ack guarantees,
{decl}`Acorn.Host.Viewer.RunDirectory.archive` (serialized with publication under the run
directory's IO mutex) moves the entire run directory — including files unknown to the current
version — onto an exclusively reserved empty destination
`<parent>/<run-name>.archive/<stamp>-<attempt>` under the sibling archive root
`<parent>/<run-name>.archive` derived by
{decl}`Acorn.Host.Viewer.RunDirectory.open` (assuming stable run and archive parents on the same
filesystem, and never replacing an existing archive). Clear does not fsync the archive root,
archive destination, or run parent directory entries, so power-loss durability is not claimed for
archival or replacement creation. Its result separates a failure before or during rename from a
failure after rename: any caught error while reserving the archive or renaming the run directory
(attempting best-effort removal of the reserved empty directory if rename throws) is classified as
{decl}`Acorn.Host.Viewer.ArchiveResult.unchanged` without re-inspecting the filesystem (assuming
on the failure side that a failed directory rename leaves the run directory at its original path),
which leaves the existing run in place and keeps the directory owner active (`Supervision.lean`
reports `Clear failed; old run remains: ...`). Once rename succeeds,
{decl}`Acorn.Host.Viewer.RunDirectory.archive` permanently retires that directory owner before
returning either {decl}`Acorn.Host.Viewer.ArchiveResult.ready` or
{decl}`Acorn.Host.Viewer.ArchiveResult.moved`, so queued publications on the old owner cannot
write into the replacement root. If creating the fresh replacement directory then fails
({decl}`Acorn.Host.Viewer.ArchiveResult.moved`), or if opening a fresh owner for the replacement
directory fails ({decl}`Acorn.Host.Viewer.Pending.reopen`), the old run is already in the archive
and the supervisor permanently retires the previous owner (`owner := .retired`, leaving it
untouched thereafter by {decl}`Acorn.Host.Viewer.Supervision.retired_untouched`) rather than
leaving the old run in place; the operator can recover the archived run under the sibling archive
layout `<parent>/<run-name>.archive/<stamp>-<attempt>`. Both replacement-failure branches emit a
supervisor failure diagnostic naming the archive path
(`old run archived at <archive>; replacement directory unavailable: ...` or
`... replacement owner unavailable: ...`), but pass it through
{decl}`Acorn.Host.Viewer.Core.report` and {decl}`Acorn.Host.Viewer.controlDiagnostic`, which retain
only the first 1,024 characters and append `" [truncated]"` when longer, so a long archive path can
be truncated and lose its identifying `<stamp>-<attempt>` suffix in the diagnostic. Mapping {decl}`Acorn.Host.Viewer.Follow.ackStop` to HTTP `202` and
definite pre-execution refusals ({decl}`Acorn.Host.Viewer.ControlResult.refused`, `busy`,
`unavailable`) versus unconfirmed Stop outcomes
({decl}`Acorn.Host.Viewer.ControlResult.unconfirmed`, serialized with `"unconfirmed":true`,
including write errors that may still request child wind-up and the 10-second `awaitControl`
timeout that ends only the HTTP wait without cancelling the Stop) to HTTP `503` in
`HttpServer.lean` and `Supervisor.lean` — where `Supervisor.performInActor` maps
{decl}`Acorn.Host.Viewer.Follow.refuseStop` to a fixed public
{decl}`Acorn.Host.Viewer.ControlResult.unconfirmed` string so HTTP `/control` JSON responses
never expose raw operating-system error messages or local run-directory/archive paths (detailed native
diagnostics remain in `Supervision.lean`'s `core.report .failed` diagnostic path and stderr) —
is likewise read from the code. On viewer shutdown interrupting an admitted Stop, the supervisor
resolves the waiter as {decl}`Acorn.Host.Viewer.ControlResult.unconfirmed` so HTTP returns `503`
(`{"ok":false,"unconfirmed":true,"reason":...}`) if the response completes before server teardown,
whereas server cancellation during shutdown can also yield an empty `503` or closed connection
without a JSON body; the browser treats both fail-closed as unconfirmed/unknown. Exiting without
starting a core on a parse or schema refusal from
{decl}`Acorn.Host.Viewer.RunDirectory.readState` in `lean/NativeApp/Viewer.lean` is likewise
read from the code.

Across the host-viewer modules under `lean/Acorn/Host/Viewer/`, several operational boundaries sit
outside proved host theorems. HttpServer.lean sets viewerHttpConfig to bind `127.0.0.1` with
maxConnections 32, maxRequests 1, enableKeepAlive false, generateDate false,
serverName none, maxBodySize and maxChunkSize equal to controlBodyCapacity (1024 bytes),
maximumRecvSize 2048, and 10000 ms headerTimeout and lingeringTimeout; HttpViewer.events calls
Broadcast.subscribe (returning HTTP `503` on capacity or sequence exhaustion) and owns one
dedicated SSE Body.stream delivery task per subscription that sends the snapshot's initial
control, map, and replay frames before handing off to liveFrames, which uses EAsync.forIn (repeat
via the ForIn instance over EAsync for Lean.Loop in Lean v4.36.0) rather than partial\_fixpoint
because async task continuations admit no fixed point and calls Subscription.poll directly (not
Subscription.receive): waiting via Selectable.one on the payload-free wake task or 5000 ms
keepalive timer and writing SSE frames (`sendLine` or `: keepalive`) to the browser occur only
after Subscription.poll releases the broadcast mutex, so a slow browser cannot block publication;
liveFrames exits on disconnect (`.closed`) or a dropped wake promise (`some none`), and stream
exit (finally), context cancellation (context.doneSelector), and response body.close each
call Subscription.close (also closing the stream on cancellation or body.close) to remove the
subscriber queue and wake an idle producer. RunDirectory.lean
(`lean/Acorn/Host/Viewer/RunDirectory.lean`) owns control-token minting through
{decl}`Acorn.Host.Viewer.mintControlToken`, which reads 16 bytes from the fixed OS entropy device
`/dev/urandom` in read mode via entropyBytes (failing on premature EOF or over-read, with no
caller-supplied path, mode, token value, or predictable fallback) and encodes them as 32 lowercase
hex characters; {decl}`Acorn.Host.Viewer.HttpViewer.new` in HttpServer.lean
(`lean/Acorn/Host/Viewer/HttpServer.lean`) calls {decl}`Acorn.Host.Viewer.mintControlToken` at
startup, so viewer startup requires OS entropy with no predictable token fallback.
ControlRequest.lean (`lean/Acorn/Host/Viewer/ControlRequest.lean`) owns token comparison and
control-request authorization: {decl}`Acorn.Host.Viewer.tokenMatches` rejects unequal UTF-8 byte
sizes and otherwise scans every byte before equality can succeed (a source-level work pattern, not
a compiler or hardware constant-time guarantee), {decl}`Acorn.Host.Viewer.ControlHeaders.authorizes`
combines header authorization (POST method, `application/json` media type, non-empty matching
token) with exact framing (Content-Length equal to the bounded body size), and
{decl}`Acorn.Host.Viewer.authorizeCommand` enforces that admission predicate before JSON decoding. Broadcast.lean
serializes replay publication, generation/identity admission, lifecycle settlement, notices,
disconnect, dequeue/wake registration, and subscriber registration behind one mutex with
connectionCapacity 16, sliding 500-frame replay history via Buffer.retain, IdentityWait overflow
marking worldPartial, and per-subscriber FIFO queues of capacity 4096 (subscriberCapacity) with
two overflow policies: Subscriber.enqueue delivers telemetry frames via Buffer.offer (refusing a
new frame without disturbing queued items when full), whereas Subscriber.enqueueControl delivers
control records (from Broadcast.settle and Broadcast.commitIdentity) and lifecycle notices (from
Broadcast.notice, backing Broadcast.announceCleared and Broadcast.announceExit) via Buffer.retain
without deduplicating, appending the new item and evicting the oldest queued item when full;
Broadcast.settle separately suppresses a byte-identical repeat of the current control record
before calling Subscriber.enqueueControl (whereas Broadcast.commitIdentity and Broadcast.notice do
not deduplicate). Broadcast.subscribe performs subscriber registration and ReplaySnapshot capture
(`identity`, `control`, `world`, and `frames`) under that same publication mutex, closing the
replay-to-live handoff gap so a published frame or control record cannot slip between the captured
replay snapshot and subsequent live-queue delivery, and refuses registration before retaining a
queue on capacity (`connectionCapacity` 16) or sequence (`2^64 - 1`) exhaustion. Each subscriber
has one bounded queue and one payload-free wake promise (`IO.Promise Unit`), with one delivery
task serving as each subscription's sole reader; publishers resolve collected wake promises only
after releasing the mutex, so a publisher never waits for a network reader, and native
mutex/promise scheduling and allocator overhead remain trusted infrastructure without a liveness
guarantee. Subscription.close removes the subscriber queue under the mutex before resolving its
wake promise outside the mutex; Subscription.poll performs one serialized dequeue (`.item`),
closed check (`.closed`), or payload-free wake registration (`.wait`) under the mutex so waiting
and network writes occur strictly outside it; and Subscription.receive (unused by
liveFrames in HttpServer.lean, which calls Subscription.poll directly) wraps Subscription.poll in a
`forever` loop without a break (ending only by returning), waiting on `.wait` outside the mutex
via IO.wait and returning `none` on either explicit disconnect (`.closed`) or a dropped wake
promise (isNone). Line.lean bounds LineDecoder lines at
lineCapacity (1 MiB, discarding oversize suffixes through newline and refusing incomplete oversized
EOF), and readLines reads one byte at a time (input.read 1) because Lean v4.36.0 Handle.read
calls buffered C fread (Lean runtime `io.cpp` lines 593–615), where multi-byte reads can block past
newline waiting for a full request or EOF; callbacks must enqueue locally and IO errors propagate
instead of synthesizing EOF. PipePump.lean filters stdout lines starting with `{`, surfaces
`"writing disabled this run"` alongside checkpointRefusalNotice, and waits for inherited-descriptor
EOF; LogPump.lean bounds queues with logTailCapacity 200 and logQueueCapacity 256.
ProcessOwner.lean consumes lastGeneration before IO.Process.spawn to avoid generation reuse on
failed spawns, relies on Lean refcounting in ProcessOwner.windUp to close stdin on drop even after
write error (no kill or wall-clock deadline), and in ProcessOwner.poll saturates uptime in Nat
and retains ownership on failed tryWait. SupervisedProcess.poll lazily attaches PipePump if
attach was skipped after spawn, and descendant processes holding pipe descriptors can delay EOF
and archival without a join deadline. RunDirectory.appendLog rotates `core.log` (logCapacity,
4 MiB) to `core.log.1` and refuses writes on rotation failure (bounding size to
logCapacity + lineCapacity under stable-path single-writer assumptions), while reserveTemporary
and reserveArchive retry exclusive creation up to 64 times. Supervisor.lean caps synchronous call
chains per drive turn at callChainBound (8) and keeps Supervisor.shutdown advancing across turn
errors; Supervision.lean sets mapInterval to 10000 ms and handles Core.command while a
replacement awaits by refusing Clear, recording `.replacement next true` on Stop, and updating
replacement.desired in memory on Start. NativeCore.lean defaults streaming to `.discounted`
rather than profile promotion and applies AgentConstruction.State.censorObservations before
final-frame emission; NativeContext.lean fixes first CheckpointAdmission via Option.or
(treating refused like missing) and saturates timestamps and uptime at `2^64 - 1`;
NativeResources.lean polls `/bin/ps` (`-o rss= -p <pid>`) every 256th non-terminal clock (requiring
kib × 1024 < 2^64, returning none on error, and reusing terminal readings); CoreTelemetry.lean
pins telemetrySchemaVersion 10 and telemetry\_drops 0; Admission.receive advances
newestTimestamp without shifting previous on `.rewound` current-identity captures (when the timestamp strictly exceeds newestTimestamp), whereas `.skipped` captures (both stale or duplicate current-identity captures and wrong-identity captures) keep previous and newestTimestamp unchanged;
and WorldMemory.seen counts non-`255` entries via countP directly from ByteArray while
WorldMemory.restore marks incomplete true.

Nor does the theorem say who may
submit a Start: the viewer serves its page on the loopback interface to whoever loads it. And that
a Start was given is a property of the program: it is separate from the owner's authorization for
a run of a learner, which [running a program](../CONTRIBUTING.md#running-a-program) governs.

The paragraphs that follow give the definitions and lemmas those statements rest on, each with
what it says. A sentence about the actor, the reader or the bootstrap is read from the code and
not proved: no theorem covers them, because the actor
(`lean/Acorn/Host/Viewer/Supervisor.lean`), the reader and the bootstrap
(`lean/NativeApp/Viewer.lean`) are effects.

The supervisor starts its child in one place, the actor's
{decl}`Acorn.Host.Viewer.Call.spawn`. The actor makes a call only as the call of the pending
operation its state waits on, after it has performed the effects of the step that produced that
state; so it makes that call only when the state waits on
{decl}`Acorn.Host.Viewer.Pending.spawn`, and it makes it then if it reaches that call. The
theorems are about the step the actor runs ({decl}`Acorn.Host.Viewer.Core.start`,
{decl}`Acorn.Host.Viewer.Core.step`, {decl}`Acorn.Host.Viewer.Core.resume`). Their proof keeps
one property of a supervisor's state, that every intent the supervisor holds is to stay stopped
({decl}`Acorn.Host.Viewer.Core.Unstarted`): the lifecycle's, the durable state's, a waiting
replacement's and the pending operation's. Its four parts are that the lifecycle intends to stop
and no Clear restores a running intent ({decl}`Acorn.Host.Viewer.Lifecycle.Unstarted`: the
lifecycle intends to stop, and a pending Clear restores no running intent); that the durable
state intends to stop; that a replacement that waits to be published intends to stop; and that
the pending operation carries no running intent and starts no process
({decl}`Acorn.Host.Viewer.Pending.Unstarted`: neither a launch nor a spawn, no Start's intent,
and no state or Clear intent that says running). The intent of every command but Start is stopped
({decl}`Acorn.Host.Viewer.Command.desired_stopped`): {decl}`Acorn.Host.Viewer.Command.desired`
computes it, and whether it is saved is the step's, since a disabled Clear changes nothing.

The start itself asks for no launch. For every durable state it is given, one that intends to
run included, and every Clear configuration, reason and reading,
{decl}`Acorn.Host.Viewer.Core.start` gives a state whose process slot is empty and which waits
on no call, whose lifecycle is the initial lifecycle of that state's identity and intent
({decl}`Acorn.Host.Viewer.Lifecycle.initial`), which holds that durable state and no
replacement, and whose detail is the initial transition with the reason given. The supervisor
publishes that detail in its first control record. A page is sent the control record that is
current when it connects ({decl}`Acorn.Host.Viewer.Broadcast.subscribe`), so it shows that reason first
only if it connects before the record of a later transition has replaced that one
({decl}`Acorn.Host.Viewer.Broadcast.settle`). What the start gives is the definition as written and not
a theorem, and the bootstrap gives it only a state that it built or admitted. So a supervisor that starts from a matching saved
running intent takes up that intent at its start and has asked for nothing there: a launch
becomes pending only in the launch check ({decl}`Acorn.Host.Viewer.Core.launchCheck`), which
the start does not make. The first constructor of {decl}`Acorn.Host.Viewer.Ran` is that start,
for every durable state, reason and reading. Whether the durable state is on disk when the
supervisor starts is a separate matter, given with the order at start-up above.

A lifecycle that intends to stop, with no running intent held for a pending Clear to restore,
admits no reservation, for every such lifecycle and every instant
({decl}`Acorn.Host.Viewer.Lifecycle.unstarted_reserve`), and it keeps both under every
transition but two: a Start request, and a running intent queued while a Clear's replacement
waits ({decl}`Acorn.Host.Viewer.Lifecycle.replacementIntent`). A stopped intent queued while a
replacement waits keeps the lifecycle so
({decl}`Acorn.Host.Viewer.Lifecycle.replacementIntent_unstarted`). An unstarted supervisor
launches nothing: for every state whose intents are all to stay stopped and every instant, the
launch check leaves the state as it is, with no change and nothing to follow
({decl}`Acorn.Host.Viewer.Core.launchCheck_unstarted`). A step on any event but an operator's
Start keeps every intent stopped, for every state whose intents are all to stay stopped, every
Clear configuration and every reading ({decl}`Acorn.Host.Viewer.Core.step_unstarted`). Every
outcome of the pending call keeps every intent stopped, for every state whose intents are all to
stay stopped, the operation it waits for and every reading
({decl}`Acorn.Host.Viewer.Core.resume_unstarted`). An unstarted supervisor starts no process and
writes no running intent: for every state whose intents are all to stay stopped, the lifecycle
admits no reservation at any instant and intends to stop, and the call the state waits for, if
any, is no spawn and writes no state that intends to run
({decl}`Acorn.Host.Viewer.Core.Unstarted.spawns_nothing`).

{decl}`Acorn.Host.Viewer.Reached` relates an origin, the events handed to the step, the most
recent first, and a state reached from the origin by steps on events and by outcomes of pending
calls. Its constructors are the origin, before any event; a step on an event; and the outcome of
the call the state waits for. Nothing in it reads a state file or starts a second viewer. The
states reached from a start are states of a run ({decl}`Acorn.Host.Viewer.Reached.ran`), and
every state of a run is reached from a start by some events
({decl}`Acorn.Host.Viewer.Ran.reached`); a run is {decl}`Acorn.Host.Viewer.Ran`, which every
{decl}`Acorn.Host.Viewer.Supervision` carries. No Start, no running intent: for every Clear
configuration, every origin whose intents are all to stay stopped, and every state reached from
it by events that hold no operator's Start, the state's intents are all to stay stopped
({decl}`Acorn.Host.Viewer.Reached.unstarted`).

The statements of the theorems in full are these. A supervisor started from a stopped intent
waits on no spawn while no Start is handed to its step: for every Clear configuration, every
durable state that intends to stay stopped, every reason and reading the viewer starts with,
every sequence of events that holds no operator's Start, and every state reached by it from that
start, the lifecycle admits no reservation at any instant and intends to stop, and the call the
state waits for, if any, is no spawn and writes no state that intends to run
({decl}`Acorn.Host.Viewer.Reached.stopped_spawns_nothing`). The three statements that follow are
that statement for particular start states. The first is for the state the bootstrap builds when
the run directory holds no state file, for every seed and whether or not a stray checkpoint was
adopted ({decl}`Acorn.Host.Viewer.Reached.unstarted_spawns_nothing`). The second is for every
state that {decl}`Acorn.Host.Viewer.PersistedState.decode` returns for a JSON value whose
`schema_version` member is absent, is not a number spelled in decimal digits alone or spells a
number other than the current version
({decl}`Acorn.Host.Viewer.Reached.earlier_spawns_nothing`). The third is for every state that
the decoder returns to a launch that has no child record, or whose record differs from the one
the JSON value's `child` member names, or that reads a value with no such record
({decl}`Acorn.Host.Viewer.Reached.unbound_spawns_nothing`). The control record of a start with no
state file says the run is stopped: for every seed, whether or not a stray checkpoint was
adopted, and every Clear configuration, reason, reading and observation, in the control record of
the start state the desired word and the actual word are both `stopped`
({decl}`Acorn.Host.Viewer.Core.start_control`); the start on a restored running state has
another desired word. By the write clause of the first statement, a supervisor waits on the write
of a running intent only after a Start was handed to its step, or from a start state that held
one.

Those statements would hold of a supervisor that never spawned. After a Start, some continuation
waits to spawn: for every Clear configuration, every durable state that admits a launch, and
every reason and reading the viewer starts with, there are events that hold an operator's Start,
and a state reached by them from that start state, that waits to spawn the first generation with
the launch the durable state admits ({decl}`Acorn.Host.Viewer.Core.start_spawns`). The proof's
witness is the Start and one tick, with every call between them succeeding. It is a statement of
existence: a Start whose intent cannot be written is another continuation and reaches no spawn.
The proof keeps a private property of a state and a launch (`Core.Poised`): a serving state with
no process, no replacement and its run directory, whose lifecycle has no Clear to go on with and
reserves its first generation at every instant, and whose durable state admits the launch. A
Start admits a reservation: for every identity, every intent native startup is given and every
instant, the lifecycle of native startup, after a Start request, reserves generation 1
({decl}`Acorn.Host.Viewer.Lifecycle.start_reserves`), and the complete retry budget admits a
launch at every instant ({decl}`Acorn.Host.Viewer.Retry.initial_ready`). The state built when no
state file exists admits a launch, for every seed within the browser's integers and whether or
not a stray checkpoint was adopted ({decl}`Acorn.Host.Viewer.Core.unstarted_launch`). The seeds
the bootstrap uses are within them: a drawn seed is below `2 ^ 48`
({decl}`Acorn.Host.Viewer.viewerSeed_bound`) and the seed beside an adopted checkpoint is 42.

The state file. {decl}`Acorn.Host.Viewer.stateSchema` is the schema version the viewer writes,
which is 2; from this version on, a viewer that finds no state file writes a stopped intent, and
before it the viewer wrote files with no `schema_version` member. The current state file has
eight members: its schema version, six of state and the record of the child of the viewer that
wrote it. The six are a seed and an agent epoch spelled as unsigned 64-bit integers, a run
identity of sixteen hexadecimal digits, an intent, an origin and the process flag. Strict JSON
syntax and exact integer admission precede identity construction. The state a viewer builds when
its run directory holds no state file ({decl}`Acorn.Host.Viewer.PersistedState.unstarted`) is a
new run of a fresh agent that intends to stay stopped, so the absence of a file gives the
supervisor no running intent; its second argument records that a stray checkpoint of an earlier
layout was adopted into the run. The version a state file names
({decl}`Acorn.Host.Viewer.stateVersion`) is nothing when the member is absent or is not a number
spelled in decimal digits alone, which {decl}`Acorn.Digits.read` reads. {leanModule}`Acorn.Digits`
(`lean/Acorn/Digits.lean`) separates {decl}`Acorn.Digits.natural` (unsigned CLI flags and native
driver arguments), {decl}`Acorn.Digits.read` (viewer request lengths, ps RSS,
{decl}`Acorn.Json.Value.natural`, and corpus-audit line numbers), and {decl}`Acorn.Digits.integer`
(arbitrary signed integer digits mapping `-0` to `0` with no bit-width bound—for example,
`9223372036854775808` succeeds—while `WorldDriver.coordinate` in `lean/Acorn/WorldDriver.lean`
and `Host.Cli.requiredCoordinate` in `lean/Acorn/Host/Cli.lean` enforce signed 64-bit
coordinate admission through {decl}`Acorn.Host.Coordinate.checked`) rather than calling Lean
core's String.toNat?, because at Lean v4.36.0 (`Std/Data/String/ToNat.lean`, String.isNat\_iff and
String.toNat?\_eq\_some\_ofDigitChars) String.toNat? accepts and strips `_` digit separators
(`"4_2".toNat? = some 42`), whereas review (not an automated gate check) keeps String.toNat? out
of the executing library; Microduck JSON numbers instead use {leanModule}`Acorn.Json`'s RFC 8259 §6 scanner,
where leading zeros are refused. The rule is about spelling: a string, `null`, and a number
spelled with a sign, a fraction or an exponent are all read as no readable version. The child record a state file names
({decl}`Acorn.Host.Viewer.stateChild`) is the words of its `child` member when that is a JSON
array of strings, and nothing when the member is absent or has any other form. Admission of the
version a state file names is decided once ({decl}`Acorn.Host.Viewer.admitVersion`): a natural
number other than the current version is refused, so that a file another version wrote is
neither guessed at nor overwritten; the current version and no readable version are admitted.
The fields of a state file ({decl}`Acorn.Host.Viewer.PersistedState.fields`) are its
`schema_version` member when it has one, whose value that admission has already judged, its
`child` member when it has one, and the six fields of state.

The complete state schema refuses unknown fields, partial identity and a schema version that is a
natural number other than the current one. For a file that is decoded, one decision
({decl}`Acorn.Host.Viewer.PersistedState.admit`) gives both the state admitted and where its
intent came from ({decl}`Acorn.Host.Viewer.StartSource`). The intent the file records is kept
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
The run directory held no state file ({decl}`Acorn.Host.Viewer.StartSource.absent`). The state
file's version does not read as the current one: an earlier version's file, whose intent was
read as stopped ({decl}`Acorn.Host.Viewer.StartSource.earlier`). The state file names the schema
this viewer writes and this launch's child, or records a stopped intent; its intent is the one
it records ({decl}`Acorn.Host.Viewer.StartSource.saved`). The state file names the schema this
viewer writes and a running intent that was not given for this launch's child: the file names
another child record or none, or this launch has none; its intent was read as stopped
({decl}`Acorn.Host.Viewer.StartSource.other`). The state admitted from a state file
({decl}`Acorn.Host.Viewer.PersistedState.decode`) is the first component of that decision, so
the state and the account of where its intent came from are one decision. A private lemma
(`PersistedState.decode_stopped`) says that a state the decoder returns intends to stay stopped
unless the file names the current schema and the child record of this launch.

The statements about the decoder in full are these. A state the decoder returns for a file whose
version does not read as the current one intends to stay stopped: for every child record a
launch may have, or none, every JSON value whose `schema_version` member is absent, is not a
number spelled in decimal digits alone or spells another number, and every state the decoder
returns for it ({decl}`Acorn.Host.Viewer.PersistedState.decode_earlier`). A state the decoder
returns for a file that does not name this launch's child record intends to stay stopped: for
every launch that has no child record, and every launch whose record differs from the one the
JSON value's `child` member names, or that reads a value with no such record, every state the
decoder returns for the value ({decl}`Acorn.Host.Viewer.PersistedState.decode_unbound`). The
decoder returns a running intent only under the current schema version and for this launch's
child: for every child record a launch may have, or none, every JSON value and every state the
decoder returns for it that intends to run, the value's `schema_version` member spells the
current version, the launch has a child record, and the value's `child` member names that record
({decl}`Acorn.Host.Viewer.PersistedState.decode_running`). The decoder returns an error for a
state file that names another schema version: for every child record a launch may have, or none,
and every JSON value whose `schema_version` member spells a natural number other than the
current version ({decl}`Acorn.Host.Viewer.PersistedState.decode_other`). The decoder returns an
error for a state file whose schema version spells a number of `2 ^ 64` or more: for every child
record a launch may have, or none, and every JSON value whose `schema_version` member is a
number whose spelling {decl}`Acorn.Digits.read` reads as a natural number of `2 ^ 64` or more
({decl}`Acorn.Host.Viewer.PersistedState.decode_wide`).

The child record. A word of a child record that the state file can hold as written is printable
ASCII with no quotation mark and no backslash, so its JSON spelling is the word between
quotation marks ({decl}`Acorn.Host.Viewer.childWordAdmitted`). The room a child record may take
in the state file, which a viewer reads within 4096 bytes, is 2048: the lengths of its words,
with three more for each word's quotation marks and comma
({decl}`Acorn.Host.Viewer.childBudget`). A child record the state file can hold has at least one
word, every word admitted, within the budget ({decl}`Acorn.Host.Viewer.childAdmitted`). The
digest of a file's content ({decl}`Acorn.Host.Viewer.fileDigest`) is 64-bit FNV-1a over every
byte, in order, a function of the bytes alone: Landon Curt Noll, Kiem-Phong Vo, Donald Eastlake
3rd and Tony Hansen, The FNV Non-Cryptographic Hash Algorithm, RFC 9923 (2026), sections 2,
5, and 8.2.2 (`https://www.rfc-editor.org/rfc/rfc9923.html`); the step and the offset basis are
those of `lean/Acorn/Rng.lean` (with {decl}`Acorn.Rng.fnv_byte` separating two byte strings differing in a
single byte). It tells two files apart against accident and not against forgery.
{leanModule}`Acorn.Rng` also implements seeded word streams after Sebastiano Vigna's SplitMix64
reference (`https://prng.di.unimi.it/splitmix64.c`, 2015, next) and David Blackman and Sebastiano
Vigna's xoshiro256\*\* reference (`https://prng.di.unimi.it/xoshiro256starstar.c`, 2018, rotl and
next), where {decl}`Acorn.Rng.SplitMix64.next` intentionally adds {decl}`Acorn.Rng.increment` both when
advancing state and inside {decl}`Acorn.Rng.mix64` ({decl}`Acorn.Rng.splitmix_two_offsets`) and raw all-zero
{decl}`Acorn.Rng.Xoshiro256` state remains admitted ({decl}`Acorn.Rng.Xoshiro256.zero`); these total
deterministic functions establish no IID or uniform-seed hypothesis, and RNG distribution results
depend on separate source-word hypotheses in `AcornVerif.CurrentRng` and `AcornVerif.Rng` (for
example, {decl}`Acorn.Rng.Xoshiro256.nextBelow` uses multiply-high scaling without rejection,
leaving 7 of the 9 grid actions with one extra preimage because `2^64 % 9 = 7`;
`AcornVerif.next_below_bin_card`, `next_below_bins_within_one`, and
`next_below_word_bins_within_one` (in `AcornVerif.Rng`) prove the exact preimage count `⌈(k+1)·W/n⌉ − ⌈k·W/n⌉` and
within-one bin bound generalized over word size `W` to avoid computing with `2^64`, yielding
`(2^64 + 2)/3` vs `(2^64 − 1)/3` preimages at `n = 3`). What a viewer reads of the file of the program its
supervisor would start ({decl}`Acorn.Host.Viewer.ProgramReading`) is the length of the file in
bytes and the digest of every byte of the file, in order. It is a function of the bytes read
alone, so it does not depend on what the state file can hold;
{decl}`Acorn.Host.Viewer.ProgramReading.of` is the reading of a file's content, read whole. The
record of the child a viewer's supervisor would start ({decl}`Acorn.Host.Viewer.childRecord`)
holds, as far as the viewer can read it before it starts it, the executable's path, the length
in bytes and the digest of the content read from the file at that path, and the argument vector
at a fixed reference launch ({decl}`Acorn.Host.Viewer.referenceLaunch`). At that launch the
words that carry the run's identity take fixed values, since the identity the state file holds
decides them at each launch. Two launches have the same child, for the purpose of a saved
running intent, exactly when both have a record and the records are equal word for word, so two
files of equal length and equal digest are taken as one. A launch has no record when sameness
cannot be established: a command given to a shell, whose process depends on the working
directory, the environment and the files the command names; an executable whose file cannot be
read whole; or words the state file cannot hold. The `child` member of a state file
({decl}`Acorn.Host.Viewer.childText`) is the record's words as a JSON array of strings, and
`null` when the launch has no record or its record cannot be held. Serialization
({decl}`Acorn.Host.Viewer.PersistedState.encode`) contains only closed spellings, numeric digits
and the admitted words of the child record of the viewer that writes it.

Reading and writing the file. Missing files and refused files have different result
constructors, so a caller cannot mistake a parse failure for a successful restore
({decl}`Acorn.Host.Viewer.StateRead`): the run directory holds no entry named `state.json`
({decl}`Acorn.Host.Viewer.StateRead.missing`); IO, syntax or schema refused the prior file, an
entry that cannot be opened included ({decl}`Acorn.Host.Viewer.StateRead.refused`); or the
complete state was admitted, with where its intent came from
({decl}`Acorn.Host.Viewer.StateRead.restored`). The read
({decl}`Acorn.Host.Viewer.RunDirectory.readState`) is bounded and preserves the distinction
between missing and malformed state. Only the absence of the directory entry, which Lean's
symlinkMetadata reads without following a symbolic link, is a missing state. An entry that
exists is opened only when it is a regular file, or a symbolic link that leads to one (Lean's
metadata follows links): anything else, such as a link whose target is gone, a directory, a pipe
or a device, is refused before it is opened, so the read never waits on an entry that cannot
supply a finite document. The two looks and the open are separate calls, so this rests on the
run directory's stable-path assumption like the rest of the reader. Every state the actor writes
goes through {decl}`Acorn.Host.Viewer.RunDirectory.writeState` with the record of its own
configuration's child. Publication uses an exclusively created temporary file under the run
directory's IO mutex and renames it onto `state.json` after a complete write and flush: failures
before the rename never replace the target, whereas an indeterminate rename error can leave
either the original or the newly renamed entry. Exclusive single-viewer run-directory ownership
(each {decl}`Acorn.Host.Viewer.RunDirectory.open` allocates fresh per-process IO mutexes),
filesystem stability, and POSIX rename remain the run directory's trust boundary; no power-loss
durability is claimed.

The actor. What the actor compares before it starts the configuration's child is
{decl}`Acorn.Host.Viewer.ChildProgram`. The bootstrap builds the constructor from the launch
itself, {decl}`Acorn.Host.Viewer.ChildProgram.ranked` for the core beside the viewer and
{decl}`Acorn.Host.Viewer.ChildProgram.fixed` for a command given to a shell, so the two are told
apart by construction and not by whether the state file can hold a record of the child. A fixed
command is spawned with no reading. The ranked constructor holds what this viewer read of the
executable's file when it started, none when the file could not be read whole, and the one
action that reads it. The bootstrap ran the action for the first and the actor runs it again
once before every start, before the launch is recorded, so what is compared was read the same
way. The configuration holds the record of the child it starts
({decl}`Acorn.Host.Viewer.SupervisorConfig.child`), written with every state this viewer saves,
and none when sameness with another launch's child cannot be established or the state file
cannot hold the record; the comparison before a start does not read it. It also holds what the
actor compares before every start of the child
({decl}`Acorn.Host.Viewer.SupervisorConfig.program`). The three refusals of a start of the
ranked core are texts: its file reads now but not as it read when this viewer started
({decl}`Acorn.Host.Viewer.childDiffers`); its file cannot be read whole now, though it could
when this viewer started ({decl}`Acorn.Host.Viewer.childUnreadable`); its file could not be read
whole when this viewer started ({decl}`Acorn.Host.Viewer.childUnread`). Each says what clears
the refusal and directs no run. A private function of the actor (`Supervisor.refusal`) gives why
the configuration's child may not be started now, and nothing when it may. A fixed command is
never refused there. The ranked core is refused when its file could not be read whole when this
viewer started, cannot be read whole now, or reads now otherwise than it did then, whether or
not the state file can hold a record of the child. The actor asks once before each start, the
first and every restart, before the launch is recorded.

Each case of the actor's call (`Supervisor.call`) performs the native operation its call names,
except that before recording a launch it checks `Supervisor.refusal` first.
The reading is made before the launch is recorded, when the call's argument says the state to
write is the one that marks a launch as attempted ({decl}`Acorn.Host.Viewer.Pending.launch`). A
refusal there writes nothing and spawns nothing: the call's result is the write's error with the
reason, which the step treats as a launch that could not be recorded, so the run stops. Every
refusal is printed on standard error and reported in the page by the step, as the reason of the
failed call. The actor hands the step an operator's Start only for a Start queued by
{decl}`Acorn.Host.Viewer.Supervisor.submit` (the `--start` flag) or
{decl}`Acorn.Host.Viewer.Supervisor.submitControl` (the HTTP control endpoint),
and the bootstrap passes the state it built
or read to {decl}`Acorn.Host.Viewer.Supervision.start`. The supervisor is constructed
({decl}`Acorn.Host.Viewer.Supervisor.new`) only after the bootstrap has admitted the initial
state. A state built with no state file ({decl}`Acorn.Host.Viewer.StartSource.absent`), or read
from a current-version file taken with the intent it records
({decl}`Acorn.Host.Viewer.StartSource.saved`), is published there, before the listener binds. A
state read from an earlier version's file, whatever intent it records
({decl}`Acorn.Host.Viewer.StartSource.earlier`), or from a current-version file with a running
intent when this launch lacks a child record (including a `--cmd` launch, whose own running file
records `"child":null`) or its record does not match the file's
({decl}`Acorn.Host.Viewer.StartSource.other`), is not published there
({decl}`Acorn.Host.Viewer.StartSource.kept`). A launch relies on no unpublished state either way, since the attempted launch
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
{decl}`Acorn.Host.Viewer.StartSource.kept`. The one line that says why the run a viewer starts
with is shown stopped, and nothing when it is not, is {decl}`Acorn.Host.Viewer.startAccount`,
so a person who finds the run stopped is told why and what starts it. The relay of standard input under `--control-stdin` is `/bin/cat` (`Acorn.Host.StopFlag.withCommands` in `lean/Acorn/Host/Control.lean`), where `Acorn.Host.controlWhitespace` trims exact Unicode White\_Space codepoints (`9..13`, `32`, `133`, `160`, `5760`, `8192..8202`, `8232`, `8233`, `8239`, `8287`, `12288`) before matching case-sensitive `"stop"`, spawning `/bin/cat` with inherited stdin, piped stdout, and null stderr (keeping core stdout/stderr uninherited, checking IO.checkCanceled around getLine, absorbing stderr write errors, and cancelling/reaping `/bin/cat` on exit without waiting on an external stdin owner); cleanup via closeCommandSource (shared by `lean/NativeApp/Core.lean` and `lean/NativeApp/Viewer.lean`) proves no shutdown deadline and no progress guarantee after native IO failure (propagating any tryWait or kill error before reaping the relay or joining the reader, and waiting without a deadline if child.wait blocks). Unbounded host loops use `Acorn.Host.forever` (`Acorn.Host.forIn_io` and `Acorn.Host.forIn_baseIO` in `lean/Acorn/Host/Forever.lean`), which defines iteration via partial\_fixpoint rather than repeat (whose toolchain partial core violates Regula rule RG1006) and specializes directly to `IO` and BaseIO (requiring Nonempty on BaseIO) so Lean v4.36.0 inlines bind and emits C self tail-jumps (`Lean/Compiler/LCNF/EmitC.lean`, lines 527–531 and 725–747) without stack growth, making no termination claim for non-exiting loop bodies.
In `lean/NativeApp/Viewer.lean`, pollBrowser clears the child handle once tryWait consumes the exit status so the child is never waited on again; desktop browser opening (openBrowser, spawned in a new session with setsid enabled) never holds a worker or blocks viewer exit and is polled once more at shutdown so a still-running detached opener survives process exit; the main `NativeApp.runViewer` loop over `Acorn.Host.forever` has no break and exits only by returning or throwing; and in its cleanup block, supervisor shutdown runs while HTTP remains alive during wind-up before the server shutdown wait releases the server's sole shutdown waiter.
