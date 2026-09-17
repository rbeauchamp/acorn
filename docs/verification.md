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
`CurrentLearnerArithmetic.alpha_lower` checks the executed alpha lower bound
`2^-40` for every legally stored beta. Its proof connects immutable rail
identities, local argument reduction, the actual polynomial and normal narrowing;
it assumes neither ideal exponential accuracy nor monotonicity.
`trace_increment_small` retains both binary32 rounding boundaries and derives
`0 <= q <= 1.01` for a finite rate and the actual receiving denominator. Existing
ordered-alpha-sum finiteness supplies that premise in the learner. The explicit
multiplication/division error wrappers retain their sign and packing proofs.
`meta_scale_finite` checks the actual meta-step/alpha quotient is finite for every
legal beta. `discounted_demon_decay` checks the configured g99 demon's executed
decay is finite, positive and at most `0.941`. For integer `0 <= M <= 40`, the
signed `mul32_finite_error` and `sub32_finite_error` wrappers require finite inputs
and exact product/difference magnitude at most `2^M`, then derive finite packing
and error at most `2^(M-24)`. `div32_finite_error` additionally requires a numerically
nonzero denominator, bounds the exact quotient, and retains error `2^(M-22)`.
No finiteness assumption about the rounded output replaces these packing proofs.
These are numerical prerequisites, not a raw-register finiteness invariant,
exclusion of exceptional later meta products or replacement-reachability result;
the existing wider public contracts remain.
`CurrentRetirement.ColdBox` is a proof-only predicate for the single g99 discounted
demon with capacity at most 16384. It combines `ZeroKnowledge`, `CoreInv` and
eligible uniqueness with signed-zero `p`, `h`, `hOld`, `hTemp`; finite `z` in
`[-2^21,64]`; finite `zBar` of magnitude at most `2^26`; and finite `zDelta` and
`lastAlpha` in `[0,1.01]`. It does not require `Ready` at callback boundaries.
`cold_box_initial` proves the actual `NumericState.initial` base case and
`cold_box_clear` preserves the predicate through actual `clearTransient`.
The proofs derive transient bounds from zero storage, not from assumed finiteness
of arbitrary/restored registers.
The local `cold_first_weight`, `cold_first_meta` and `cold_first_beta` contracts
under `ColdBox` and signed-zero error/accumulator derive no clipping, a finite
signed-zero meta product and unchanged visited beta word. `cold_first_trace`
checks finite decay with trace upper bound 61 and nonnegative retained trace via
the actual pruning threshold. `cold_first_registers` preserves the visited
sensitivity zeros, finite Dutch-trace bound and zeroed trace increment.
`cold_first_pruned` follows the actual clear/retain decision and yields zero
knowledge, unchanged visited beta word and finite trace in `[0,61]`. Its beta
proof transports whole-state branch equalities through a nondependent raw-word
observation, preserving the exact dependent storage semantics.
`ColdWork state work` is a proof-only `ColdBox` observation with `work` installed
as eligibility. `cold_work_entry` derives it for the actual stored-empty entry;
`cold_work_contract` recovers `Supported state work`, reference legality, zero
knowledge and worklist uniqueness without assuming `CoreInv` over the empty list.
`cold_work_finish` covers final worklist installation. `cold_work_first_element`
transfers the local contracts; `cold_work_first` and `cold_work_prune` preserve
the worklist box through one member visit and actual clear/swap-remove using
existing framing, support and uniqueness proofs. Runtime storage is unchanged.
`cold_work_go_preserves` composes those steps by induction on the actual
`learnFirstLoopGo` recursion, with signed-zero error/accumulator and the configured
decay. `cold_box_first_preserves` connects the actual public entry to this proof.
The resulting `ColdBox` preserves its original register bounds, not an all-word
beta history or the stronger final trace bounds. All-word beta preservation
remains unproved across the traversal. Final per-index trace bounds `[0,61]`
require a processed-prefix numeric invariant and dormant-support zero facts;
`Ready` alone supplies neither nonnegativity nor that upper bound. Second-loop
and begin/step/terminal closure, overshoot-count consequences and current-owner
composition remain unproved.
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
action. The initialized existence theorem below discharges that successful-prefix
premise in its bounded standard domain. `finish_carried` and `Attempt.start_carried` retain
terminal reward across a continued attempt/goal boundary. A final campaign
boundary supplies no extra learning callback. Zero-sector preservation establishes
neither beta-floor progress nor complete-reader eligibility.
`CurrentRunner.survival_plan_exists`, `initial_cursor_exists`, `achieved_next_goal`
and `standard_first_goals` check actual plan admission and cursor/curriculum
choices. `CurrentWorld.standard_config_exists`, `standard_body_translation` and
`standard_spiral_coordinates` cover standard configuration and signed coordinate
admission. `word32_conversion`, `scale_word_bounds` and `standard_scale_bounds`
connect direct word conversion to the actual standard scale. `octave_scale_double`
and `standard_octave_scales` prove finite positive bounds on the executed scale
multiplications by structural induction. `coordinate_float_bound` follows actual
signed ingress and sign-bit construction; `coordinate_quotient_bound` bounds
actual binary32 division, including normalization and finite packing. These
proofs use the existing format-parametric arithmetic correspondence; native
floating-point/compiler implementations remain trusted boundaries.
`octaveLoop_success_of_samples` and `standard_terrain_of_samples` are conditional
control-flow composition: they retain sample-success hypotheses.
`floor_cast_neighbor` excludes the maximal signed endpoint after actual floor
and widening/cast, preserving the checked neighbor operation.
`standard_terrain_success` discharges the sample hypotheses for every standard
configuration and salt with both position coordinates in `[-201, side + 201]`.
`standard_tileKind_success`, `standard_observeTile_success` and
`standard_observe_success` compose actual terrain, sensor geometry and both
row-major vector traversals for every standard-world state.
`CurrentRunner.standard_sense_success` derives strict room from typed steps and
actual unfinishedness, and returns the actual owned `Attempt.sense` input.
`standard_start_sense_success` covers every positive-cap attempt start, regardless
of the carried terminal flag. These pure admission proofs assume the existing
compiler/runtime and allocation boundaries.
`CurrentWorld.standard_countKindNear_success` structurally composes the actual
two radius-four range traversals, retaining terrain and translation admissions.
`standard_considerSpawn_success` covers all candidate coordinates and prior best
values through the actual box check, scans and score branches, without assuming
walkability. `standard_selectSpawn_success` composes all three actual spawn loops,
including their optional-return/current-best accumulator and typed center
fallback. The same structural traversal bridge serves the scan and spawn proofs.
`DeerInBox` adds a proof-only coordinate predicate for the placement result;
arbitrary world states need not satisfy it. `standard_placeDeer_success` and
`standard_initializeDeer_success` preserve it through actual placement and its
finite loop, with the original world and changing population/RNG accumulator.
`standard_initial_success` derives empty-population admission and composes
actual spawn and deer construction. Existing `World.initial_fields` covers the
other fields. `PositionWithin` describes a signed coordinate envelope, with
`deerInBox_iff_positionWithin` preserving its correspondence to initialized deer
at zero steps. `standard_wanderDeer_success` proves actual single-deer admission
and a one-step envelope expansion for `n < 200`, retaining the actual RNG result.
`standard_wanderPopulation_success` composes actual ordered wandering through
checked vector/array/list correspondence. Its result includes exact length,
per-entry envelope advancement and the ordered actual-operation traversal with
the same final RNG. The original world is fixed throughout the traversal.
`standard_foodTrials_success` structurally admits the actual finite food search;
`standard_spawnFood_success` preserves the due/capacity and optional insertion
branches. `standard_passiveChange_success` composes the actual deer and food
calls, preserving deer length/envelope and explicitly linking the intermediate
RNG to the food result's final RNG. `standard_performAction_success` admits all
actual actions on arbitrary standard worlds, retaining box rejection before
terrain and the actual harvest, crafting and eat branches.
`standard_payAndAct_success` includes exhaustion recovery without a positive-energy
premise. `standard_step_success` composes the actual active result and advanced-time
passive reader: for input deer in `PositionWithin n`, `n < 200`, every action
succeeds with exact deer length and output envelope `n + 1`. Existing
`World.step_clock`, `step_goal` and `step_completion` retain the single final
wrapping clock increment, installed goal/origin and completion result.
`CurrentReplacement.standard_ranked_survival_exists` constructs actual
callback-driven prefixes from one cold/world initialization for every `n ≤ 200`
and cap at least 200. It preserves exact steps/time, goal/origin, deer length and
envelope, complete raw-result coherence, reward/completion and the joined zero
sector. Its private induction derives sensing and world success from these
checked owners. `standard_campaign_survival_exists` supplies the actual supported
standard configuration, campaign admission and first cursor, and specializes to
the native cold ranked discounted scalar constructor. These proofs concern pure
native-linked transitions, with the existing compiler/runtime and IO boundaries.
`standard_positive_callback_exists` composes actual finish/recording, the
non-stopping cursor advance to wood collection, new-attempt start/sensing and
actual callback selection. It identifies the exact terminal frame, unchanged
world/raw feedback, incoming zero sector and selected agent/action with
`Agent.act` receiving reward one and done true. World time remains 200; the new
attempt has counter zero and is unfinished, without assuming its wood goal is
unsatisfied. No additional world step or post-positive numerical invariant is
introduced. Native IO completion, runtime feasibility, terrain quality and
replacement reachability remain separate.
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
