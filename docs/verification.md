# Verification

This guide describes Acorn's compiler, proof and execution checks. Each theorem
states the property and assumptions it checks. For installation and a first run,
start with the [README](../README.md#start-with-the-live-viewer).

Run `./scripts/verify.sh` in the actual Git checkout after provisioning the pinned
Lean/Mathlib dependencies, a C compiler, OpenSSL 3, ShellCheck and GNU coreutils.
The hard 360-second deadline includes project compilation and every ordinary
check. It uses process-group SIGKILL with no grace period or budget override;
missing, skipped or timed-out checks fail. OS scheduling and signal delivery
are the trusted mechanisms that enforce this deadline.

## Platform setup

Use `./scripts/start.sh` for automatic setup and launch, or
`./scripts/start.sh --prepare-only` to prepare and build without learning.
It uses Homebrew on macOS and apt-get on Ubuntu/Debian. It installs missing
prerequisites and provisions the pinned Lean/Mathlib dependencies; repeat launches
use the offline bootstrap when those dependencies are already available.
The first setup may need network access, a package-manager password prompt or
the macOS command-line tools installation dialog. It never runs Acorn as root
and does not change the global Xcode selection or Lean default toolchain.

The [CI workflow](../.github/workflows/verify.yml) runs on GitHub's standard
Apple Silicon `macos-latest` image. Dependency caches include the actual macOS
major version. Automatic local setup supports macOS and Ubuntu/Debian Linux.

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
`(cd lean && lake exe cache get)` from the repository root to provision the
pinned toolchain/dependencies. Do not use `lake update` to resolve a missing
dependency; that changes the selected versions.

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
Lake's evaluated targets and compiled entry owners. Source/compiled admission
checks imports, capability owners, artifact origins and native routes. Every
project theorem is checked for axiom dependencies; only propext,
Classical.choice and Quot.sound are admitted. The theorem inventory reports the
checked declarations. Every proof passes through the kernel.

Acorn's executable definitions and their state invariants are under lean/Acorn.
AcornVerif contains contracts importing those definitions and supporting
mathematics with explicit hypotheses. Acorn.Constants owns the shared machine
words; CurrentConstants checks the stated correspondence with rational and
dimensional inputs used by the mathematical proofs.

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
with cold project outputs. It has read-only repository permissions, no secrets,
no privileged pull-request trigger, and pinned action revisions. The workflow
must pass on the exact proposed head before merge.

Ordinary verification shares a compiler environment for ownership, theorem/axiom
and document-symbol admission. Executable entries retain isolated `main` owners
and reuse loaded dependency regions. Each IR reference must belong to that
entry's actual compiled import closure; data loaded for another entry cannot
satisfy this check. Shared regions live only for the audit process, and no prior
acceptance result is cached. Source, boundary, native-route and browser checks
remain required. Standalone ownership, theorem and corpus commands remain
available for focused diagnostics.

## Mutation diagnostics

**Pinned digest: `829aef890c81afaf`**

```sh
lean/.lake/build/bin/acorn-core audit --expect 829aef890c81afaf
```

Paired checksum `b1a076b6ac5884f0`. The optional ./scripts/verify.sh diagnostics
command runs all three fixed arms under the same deadline. The fixed audit arms
are compared through these paired digests. Run these optional diagnostics
when investigating a dynamics change.

## Checkpoint admission

Format 14 preserves admitted learner state, assignments and pending ranking
requests for supported ranked profiles. Restore checks dimensions, identifiers,
criterion and value domains before admitting state. An incompatible image is
refused and writes to that file are disabled. Learner state resumes; the world
and transient process state restart. Filesystem persistence relies on the narrow
C fsync helper, native IO and the operating system.

## Viewer ownership boundaries

The viewer observes telemetry and supervises process lifecycle. Only a stop
request enters the core, at an attempt boundary. Source/compiled ownership
prevents learned code from reaching host control. Browser numeric and lifecycle
contracts have executable owners and generated bytes; see viewer-ux.md.
Predictive agreement compares forecasts with settled finite returns within the
current process. Incomplete horizons and unavailable state are reported as unknown.
