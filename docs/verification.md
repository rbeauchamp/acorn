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

`CurrentReplacement` separates replacement predicate inhabitation from learning
execution. Its omitted-primitive result uses the actual `AgentPath` relation;
its short-invocation result composes the executing model begin/terminal callbacks
with machine arithmetic in `CurrentRetirement`. The latter's enclosing temporal
schedule is a source-linked structural argument, with explicit exposure and
input conditions. Neither result proves positive complete-reader reachability,
fair selection of every unit, or learning benefit. The exact local transaction,
alias ordering and finite history/clock limits retain their own proof owners.
Its `first_option_policy` theorem connects the executed begin/first temporal
action to unchanged policy weights, the actual drawn action's saved prediction
and a zero shared accumulator, for either criterion and arbitrary raw credit.
It does not establish the later terminal-error sign or progress margins.
`act_two_refresh_changes` is a separate machine-checked full-agent obstruction:
a discounted free-dispatch callback with a pending refresh that changes two
complete assignments retains an unselected cold model through completion. The
proof derives refusal before the actual retirement call and unchanged event
history, for arbitrary input words without a feature-count bound. It does not
prove that initialized native paths realize these assignment-change premises.
`CurrentRetirement.ZeroKnowledge` checks cold construction and zero-target
numeric begin/step/terminal closure through the actual loops, including NaN
projection and clipping without trace-finiteness assumptions. The discounted
continuation proofs connect actual agent construction and skill begin/step/close
owners; a zero terminal meta value preserves continuation zero knowledge for
arbitrary rewards. `CurrentControl.ZeroController` additionally checks actual
shared-error credit,
terminal clearing and the snapshot/draw path. Its snapshot maximum supplies the
old meta target in `zero_continuation_close_snapshot`; Demon-0 reward production,
neutral ranking and identity-preserving neutral refresh have component proofs.
`ZeroModel` covers both discounted scalar learners; their fresh predictions supply
zero planning targets, and the actual scalar fold preserves the whole controller.
`zero_gap_accumulate` reuses the universal portable-power bound for the actual
stored gap duration. Neutral terminal policy credit uses its producing old meta
snapshot, with false previous potential retained as an explicit premise.
`ZeroNeutralSkill` checks construction and concrete whole-Skill begin/first-action,
actual continuing-token and old-meta-ending composition. Its producer inversion
binds the continuing snapshot; begin and continuing endpoints return false
previous potential. `ZeroSkillState` additionally checks actual table installation,
meta dispatch, continuing phase update and close-owner frames. Neutral potential
comes from the selected actual table entry; a detached closed owner's result is
discarded without a zero-sector assumption. The active close uses the pre-close
meta snapshot and leaves idle occupancy. Other learners and the joined callback
invariant remain outside this skill-table/phase result.
`ZeroRankedState` joins it with both controllers, Demon-0 and the actual deferred
meta reward. `zero_ranked_initial` proves the actual public ranked discounted
constructor base case for every configuration, dimension and planning choice;
the other ten demons remain unrestricted. `zero_ranked_prepare` preserves the
join through actual rate/gap/model-observation preparation with arbitrary features
and signed-zero reward. `zero_ranked_draw_credit` covers consecutive actual meta
draw/credit, deriving the decision from its snapshot and reward from its owed gap.
`zero_ranked_refresh` and `zero_ranked_plan` frame actual neutral refresh and
concrete configured planning. `zero_ranked_dispatch` joins the actual produced
draw/credit with successful skill installation; `zero_ranked_boundary` composes
the successful ordinary discounted boundary with no pending close, using the
existing closing-preservation proof. `zero_ranked_serve`,
`zero_ranked_continuing` and `zero_ranked_close_active` cover actual served priority,
stored continuing-token credit and old-meta discounted close.
`zero_ranked_selection` joins preparation and all successful actual selection
branches for arbitrary features and goal under signed-zero reward.
`zero_ranked_finish` combines the actual recorded prediction view's primitive and
Demon-0 credit. Primitive per-step credit follows from the profile's stored credit
invariant, without a selected-action or ownership restriction. `zero_ranked_step`
composes the successful selector and its own completion;
`zero_ranked_aligned_step` reuses the actual aligned wrapper's step equation.
`CurrentRetirement.zero_retire` checks the actual numeric slot reset;
`zero_controller_retire` and `zero_model_retire` preserve the lifted zero sectors.
`zero_ranked_retire` covers both refusal and same-receiver replacement, including
complete consumer resets and retained temporal references. `zero_ranked_act`
composes actual clock/current-bank encoding, local step and retirement for one
zero-reward action. `RankedSurvivalPrefix` and `ranked_survival_native_step` link
successful sensing, actual callback choice and world/accounting stages to the
native attempt loop. `survival_prefix_clock` derives the carried reward from the
actual survival counter with no clock wrap under the finite attempt cap.
`zero_ranked_initial_survival` covers successful first-attempt prefixes from the
actual cold agent and successful world constructor through the goal-producing
action. It assumes the successful prefix; it proves neither nonempty execution
nor a later positive callback. `finish_carried` and `Attempt.start_carried` retain
terminal reward across a continued attempt/goal boundary. A final campaign
boundary supplies no extra learning callback. Zero-sector preservation establishes
neither beta-floor progress nor complete-reader eligibility.
`CurrentRunner.survival_plan_exists`, `initial_cursor_exists`, `achieved_next_goal`
and `standard_first_goals` check actual plan admission and cursor/curriculum
choices. `CurrentWorld.standard_config_exists`, `standard_body_translation` and
`standard_spiral_coordinates` cover standard configuration and signed coordinate
admission. Successful terrain, complete world construction and nonempty callback
execution remain unproved; no runtime feasibility claim follows from these bounds.
`CurrentRetirement.episode_sensitivity_anchor` is a conditional identity for the
executing second-loop element, including the ordered binary32 sensitivity
correction and finite meta-gradient transfer. It assumes aligned incoming
registers; no installed boundary or initialized execution path establishes those
premises. The proposed boundary and progress margins in PAR-11 remain obligations.

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
