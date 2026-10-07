/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import VersoManual
import AcornSite
import Acorn.Constants
import Acorn.Host.Checkpoint.Admission
import AcornVerif.CurrentConstants
import AcornVerif.GridCorrespondence

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
Lean, Mathlib, FloatLib and Verso dependencies, a C compiler, OpenSSL 3, ShellCheck
and GNU coreutils.
The hard 360-second deadline includes project compilation and every ordinary
check. It uses process-group SIGKILL with no grace period or budget override;
missing, skipped or timed-out checks fail. OS scheduling and signal delivery
are the trusted mechanisms that enforce this deadline.

Project instruction changes have no live Acorn runtime surface. The complete
verification command remains required for documentation changes.

# Platform setup
%%%
tag := "platform-setup"
%%%

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
`ubuntu-24.04` x64 image. Dependency caches include the Ubuntu release and
runner architecture. Automatic local setup supports macOS and Ubuntu/Debian Linux.

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

The complete discovered module inventory must equal the explicitly admitted
ownership inventory. Every retained native target is built and checked against
Lake's evaluated targets and compiled entry owners; each executable root must be
a maintained module with a non-empty module docstring. Ownership admission
refuses a facet-qualified build key in the root package's Lake configuration.
The [Lake configuration](../lean/lakefile.lean) documents the restriction and its
pinned-Lake rationale.
Before any Lake command, `Bootstrap.lean` must elaborate with no message, and
Lake runs with `--wfail`, so any warning, including a header-time warning such
as a deprecated import, fails the build. Source/compiled admission checks
imports, capability owners, artifact origins and native routes. Every project theorem is checked for axiom
dependencies; only {splice}`proseList (AcornTheoremCount.admittedAxioms.toList.map toString)` are admitted. The theorem inventory reports the
checked declarations. Every proof passes through the kernel.

The modules that compose the agent import no world. Source and compiled admission
refuse a declared module that imports a host module, or references a declaration
owned by one, unless it is one of the grid world's own declared modules:
{splice}`proseList (AcornBoundaryAudit.gridOwners.toList.map toString)`. The last of
them binds the grid world to the agent's interface.
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

{decl}`AcornVerif.GridCorrespondence.callback_eq`,
{decl}`AcornVerif.GridCorrespondence.initial_eq` and
{decl}`AcornVerif.GridCorrespondence.restore_eq` state the same for the host's step,
construction and restoration. The reference covers the composition; the storage types
beneath it are the executed ones at the grid's action count.

The executed step is two functions under a declared step order:
{decl}`Acorn.Handcrafted.Agent.choose` selects, and
{decl}`Acorn.Handcrafted.Chosen.learn` completes the step from the value the first
returned. {decl}`Acorn.Handcrafted.Agent.act_parts` states that under the default
order they compose to the executed step, for every agent state and percept, in every
world:

{statement Acorn.Handcrafted.Agent.act_parts}

Under the other order planning follows the action.
{decl}`Acorn.Handcrafted.TemporalControl.atBoundary_unplanned` states that the meta
draw of a free dispatch then reads the meta-controller before that frame's planning,
and {decl}`Acorn.Handcrafted.Agent.actOrdered_undrawn` that a step whose decision
records no meta decision is the executed step under both orders.
{decl}`Acorn.Handcrafted.Agent.choose_keeps` states that the first part writes neither
the primitive controller nor a prediction demon, and
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

The build tools check one explicit source inventory, including every shared
application/proof owner and native entry. Runtime `--research-profile` selects
agent mechanisms; it does not change verification. Resource, route and compiler
flag admission, browser byte generation, corpus and declaration checks always
run. Missing files fail admission.

Numerical proofs use the executing Lean definitions. Native admission checks
their compiler IR, primitive calls, resource contracts and compiler flags.
Primitive IEEE interpretation remains a native assumption.

CI provisions dependencies separately and runs the identical ordinary command
with cold project outputs. A second job runs the [Regula audit](#regula-audit)
on the same head, also from cold project outputs. The workflow has read-only
repository permissions, no secrets, no privileged pull-request trigger, and
pinned action revisions. Both jobs must pass on the exact proposed head before
merge.

Ordinary verification shares a compiler environment for ownership, theorem/axiom
and document-symbol admission. Executable entries retain isolated `main` owners
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

# Regula audit
%%%
tag := "regula-audit"
%%%

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
NativeApp and Bootstrap, with the {splice}`numberWord applicationExecutables.length` application executables, claim Regula's
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
with the {splice}`numberWord toolExecutables.length` tool executables; it is the reviewed tooling trust boundary.

`lean/Acorn/Decisions.lean` registers the library's decision functions for which
a property of the accepted or refused result is proved. A decision function is
an admission, parser or validity test: its result accepts or refuses an input.
A registration of a function between fixed types is a Regula executable contract
about the executing definition itself, with the kind its proof establishes. A
two-way kind states that the function accepts exactly the inputs that satisfy
the written specification, with one accepted and one refused input as witnesses.
Regula's decision attribute makes the contract a requirement of the function, so
the audit fails when a contract is removed while its function stays registered.
A decision procedure whose result type is `Decidable` carries both directions in
its type and is registered with no contract. An admission with an argument or
result type that depends on an earlier argument has no kind. Neither has a
function between fixed types for which no theorem states a set of the inputs
that it accepts. Where a theorem
proves which inputs it accepts or refuses, or a property of an accepted or a
refused result, that statement is registered as a requirement with no kind, and
the ownership audit requires the contract by name. A decision that takes its
element type as an argument has no kind either and is registered in the same
way. A requirement with no kind is a statement that the Regula audit does not
examine: that audit checks only that its theorem is proved about the executing
definition. Such a statement can fix one direction only, and no statement of a
registry shows that both outcomes occur for its function. Kinds for these
functions are remaining work of
[issue 67](https://github.com/rbeauchamp/acorn/issues/67). A contract states only
what its theorem proves.

Regula's audit does not find a decision function that is not registered, and no
check of Acorn does. The module documentation of `lean/Acorn/Decisions.lean`
lists the groups of definitions with a `Bool`, `Option`, `Except` or `Decidable`
result that carry no contract, with the reason for each group. That list has no
check of completeness: a new definition with such a result can arrive with no
contract and no entry. A report of the definitions with no contract is work of
Regula ([issue 115](https://github.com/rbeauchamp/regula/issues/115)).
`Acorn.Decisions`
cannot register a function of another library, such as a NativeApp parser. No
kind says that a specification is the intended one. `Acorn.Decisions` belongs to
the Acorn library
because Regula decides a registered function against the contracts of the
function's own library. It is the only module that imports Regula's decision
attribute. No module imports it, so no entry point links what it declares; the
boundary audit admits it with the proof sources and refuses an import of it.
`AcornVerif.Decisions` states the contracts whose proofs need the proof library.
Regula does not count them toward a registration, so their functions are not
registered, and the ownership audit requires each contract by name. Among them
are the certificate checkers. No checker is complete, so each contract states
what an accepted certificate establishes: the blocked checker carries the sound
kind, and the replay and stance checkers, whose arguments have a dependent type,
a requirement with no kind.

The driver builds every claimed module with warnings as failures, then inspects
the compiled environments. It rejects holes, project axioms, unsafe or partial
definitions, an axiom outside the claim, a module that no library includes, and
a claimed target whose Lake options weaken the required set. That set turns
automatic implicits off and turns on the missing-docstring linter and Mathlib's
standard linter set, whose header linter checks each module's copyright and
license lines.

The audit is a second required check and is not part of `./scripts/verify.sh`.
It compiles the claimed modules again and replays them in the kernel, which does
not fit beside the ordinary checks inside the 360-second deadline. No Acorn gate
is retired. Boundary, ownership, native-route, corpus and theorem-axiom
admission remain required, and they overlap Regula's hole, axiom and
unsafe/partial rules as independent implementations. An accepted audit covers
Regula's mechanical rules for the claimed surfaces; it does not replace review.

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

# Mutation diagnostics
%%%
tag := "mutation-diagnostics"
%%%

*Pinned digest: {spliceCode}`digest .declared`*

```spliced sh
s!"lean/.lake/build/bin/{executable "acorn-core"} audit --expect {digest .declared}"
```

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

Format {splice}`toString Acorn.Checkpoint.formatVersion` preserves admitted learner state, generator and tester state and
assignments for supported ranked profiles. Earlier
formats are refused. Restore checks dimensions, identifiers,
criterion, step order and value domains before admitting state. An incompatible image is
refused and writes to that file are disabled. Stored learner state resumes; option
models and each option's off-policy questions (PAR-18) are not stored and start
afresh, and the world and transient process state restart. Filesystem persistence relies on the narrow
C fsync helper, native IO and the operating system.

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
