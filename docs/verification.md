<!-- Generated from site/AcornDocs/Verification.lean by ./scripts/verify.sh site write. Edit that source, not this file. -->

# Verification

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

## Platform setup

Use `./scripts/start.sh` for automatic setup and launch, or
`./scripts/start.sh --prepare-only` to prepare and build without learning.
It uses Homebrew on macOS and apt-get on Ubuntu/Debian. It installs missing
prerequisites and provisions the pinned Lean, Mathlib and FloatLib dependencies;
repeat launches use the offline bootstrap when those dependencies are already
available. The bootstrap status that decides this builds nothing, writes only the
launcher's own override file and asks Lake whether the FloatLib modules the proof
bridge imports are current.
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
`(cd lean && lake exe cache get && lake build Mathlib floatlibBridge)` from the
repository root to provision the pinned toolchain/dependencies; the build compiles
only Mathlib modules absent from the upstream cache. FloatLib publishes no cache,
so the same command compiles the FloatLib modules that the proof bridge imports.
The offline bootstrap asks Lake whether every artifact those imports need is
current and refuses to run until it is: verification never compiles a dependency
inside its deadline. Verification also builds the
[documentation site](#documentation-site): run
`(cd site && lake build verso/VersoManual)` once to provision pinned Verso, which
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

The complete discovered module inventory must equal the explicitly admitted
ownership inventory. Every retained native target is built and checked against
Lake's evaluated targets and compiled entry owners; each executable root must be
a maintained module with a non-empty module docstring. Ownership admission
refuses a facet-qualified build key in the root package's Lake configuration.
The Lake of Lean v4.34.0 stores such a key under its target as written, which is
a different entry from the target's own unless the key names its package in
resolved form, and it fetches the key concurrently with other fetches. Either
way a second job can run on the same output file
([leanprover/lean4#15435](https://github.com/leanprover/lean4/issues/15435)).
Before any Lake command, `Bootstrap.lean` must elaborate with no message, and
Lake runs with `--wfail`, so any warning, including a header-time warning such
as a deprecated import, fails the build. Source/compiled admission checks
imports, capability owners, artifact origins and native routes. Every project theorem is checked for axiom
dependencies; only propext, Classical.choice and Quot.sound are admitted. The theorem inventory reports the
checked declarations. Every proof passes through the kernel.

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
bridge imports by Lake's build traces. Lake therefore fetches a dependency whose
checkout is not at the locked revision.

The command exits 0 when the audit is accepted, 1 on a violation, 2 on an invalid
configuration and 3 when the audit is incomplete. The first run compiles Regula's
driver. Regula writes scratch copies of Lean sources to .lake/regula-scratch under
lean; a killed run leaves them until the next Regula run removes them. Git ignores
.lake, and the module inventory, the native source inventory and the corpus walk
skip it as Lake's build directory.

`lean/foundation_manifest.json` states what is audited. A claim names the
strongest axioms any declaration of a library may depend on. Acorn, AcornVerif,
NativeApp and Bootstrap, with the ten application executables, claim Regula's
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

The site check is the last step of `./scripts/verify.sh`, inside its deadline; the
command above runs that step alone. It builds the documents, renders the pages
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

**Pinned digest: `7433307b046fd16c`**

```sh
lean/.lake/build/bin/acorn-core audit --expect 7433307b046fd16c
```

Paired checksum `385b2f84db38eef2`. The deployed arm runs the ranked profile
with the declared D6 exploration rate. The optional ./scripts/verify.sh diagnostics
command runs all three fixed arms under the same deadline. All three pins record
the published generate-and-test tester and task-reading generator (PAR-11, D7)
and off-policy option learning (PAR-17);
the declared-rate and differential pins also record the stable, sign-correct
reward-respecting subtask and declared-rate dynamics decisions. The fixed audit arms
are compared through these paired digests. Run these optional diagnostics
when investigating a dynamics change.

## Checkpoint admission

Format 16 preserves admitted learner state, generator and tester state,
assignments and pending ranking requests for supported ranked profiles. Earlier
formats are refused. Restore checks dimensions, identifiers,
criterion and value domains before admitting state. An incompatible image is
refused and writes to that file are disabled. Learner state resumes; the world
and transient process state restart. Filesystem persistence relies on the narrow
C fsync helper, native IO and the operating system.

## Viewer ownership boundaries

The viewer observes telemetry and supervises process lifecycle. Only a stop
request enters the core, at an attempt boundary. Source/compiled ownership
prevents learned code from reaching host control. Browser numeric and lifecycle
contracts have executable owners and generated bytes; see
[the viewer specification](viewer-ux.md).
Predictive agreement compares forecasts with settled finite returns within the
current process. Incomplete horizons and unavailable state are reported as unknown.
