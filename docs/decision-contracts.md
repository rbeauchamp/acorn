# Decision contracts

This document owns the selection rule, kindless-contract inventory, shared-test
rule, and unregistered-definition inventory for the decision registries in
[Acorn.Decisions](../lean/Acorn/Decisions.lean) and
[AcornVerif.Decisions](../lean/AcornVerif/Decisions.lean).

## Registered decisions of the executing library

A decision is a function whose result accepts or refuses its input: an admission,
a parser or a validity test. Each contract is a Regula executable contract about
the executing definition itself, with the kind its proof establishes: Regula's
two-way kind (Decides) states that the function accepts exactly the inputs that
satisfy the written specification, with one accepted and one refused input as
witnesses; its one-way sound kind (DecidesSoundly) states that every accepted
input satisfies the specification, with an accepted witness; and its one-way
complete kind (DecidesCompletely) states that every input satisfying the
specification is accepted, with a refused witness.
A declaration of Regula's RegisteredDecision type in `Acorn.Decisions` registers
the function, and the ownership audit requires a contract with a kind in
`Acorn.Decisions` or `AcornVerif.Decisions` for each registered function whose
result is not `Decidable`, so removing the contract while the function stays
registered fails the audit. No rule of Regula reads a contract or a registration.

### Selection rule

A decision is registered when a theorem beside its definition, or in the proof
library, proves a property of its accepted or refused results, or when the inputs
it accepts follow by unfolding its definition in `Acorn.Decisions`. The property
is the set of accepted or refused inputs where a theorem states one, and
otherwise what an accepted or a refused result is. A contract states only what
its theorem proves: a decision with one proved direction carries that direction
alone. Five groups are covered:

- Decisions of independent arguments carry a kind and a registration. A function
  of several arguments is decided on their product through uncurrying or
  a tuple wrapper.
- A decision procedure whose result type is `Decidable` carries both directions
  in its type, so it is registered with no contract.
- A decision with an argument or result type that depends on an earlier argument,
  such as `Bounded32.admit`, and a decision that takes its element type as an
  argument, such as `Host.Viewer.Buffer.offer`, carry a kind and a registration
  in the forms that Regula gives for them. The kind is stated about the function
  applied to the two fields of a pair, or to every field of a structure of its
  arguments, in order. Where the result type depends on the input, the kind is
  about `Regula.Dependent.isSome` or `Regula.Dependent.isOk` of that function:
  whether the result holds a value, with the value forgotten.
- A function with a kind can carry a second statement beside it for what its kind
  does not state: the value or postcondition of an accepted result (for example
  `cli_value_found`, `world_initial`, `world_observe`, `world_step`,
  `spawn_select`, and statements ending in a value suffix; `payload_admit_value`
  and `candidate_load_value` in `AcornVerif.Decisions` stand in the same way
  beside kindless requirements), the exact verdict on a part of the inputs
  (`capture_follows`, and `task_observed` in `AcornVerif.Decisions`), a set of
  accepted inputs beside a sound kind (`schema_covers_empty`,
  `predicate_eval_programs`), a set of refused inputs beside a one-way kind
  (`stance_certified_refused`, `stance_check_refused`, `blocked_check_refused`),
  or which of several accepted results an input has (`microduck_outcome_judged`,
  `microduck_line_read`). That statement is a requirement with no kind, and the
  ownership audit requires it by name in `AcornOwnership.anchors`.
- A function keeps a requirement with no kind where no kind is true of it, or
  where the shared-test rule below excludes the kind. The function carries no
  registration, and the ownership audit requires the contract by name in
  `AcornOwnership.anchors`, with a statement that still refers to the executing
  definition.

### Statements that keep no kind

In `Acorn.Decisions`, kindless contracts fall into four reasons (beside
non-decisions such as `Host.coordinateFloat` and `Agent.runPrefix`, which refuse
no input and carry `coordinate_float` and `agent_run_prefix`, and definitions
that specifications share with their functions):

- **No kind is true of the function, or no theorem states one.**
  `StepSizeRails.admit` accepts every configuration, whereas a complete or
  two-way kind requires a refused input. `AgentConstruction.State.restore`
  refuses no input its type admits (`CurrentCheckpoint.unresumable_unloaded`,
  `AgentConstruction.State.restore_exact`). `Host.World.initial` carries a
  registered two-way kind (`world_initial_accepts`), while `Host.World.observe`,
  `Host.World.observeTile`, `Host.World.step`, `Host.wanderPopulation`,
  `Host.foodTrials`, `Host.spawnFood`, `Host.selectSpawn`, and
  `Host.initializeDeer` carry registered one-way complete kinds over admissible
  configurations (`world_observe_accepts`, `observe_tile_accepts`,
  `world_step_accepts`, `wander_population_accepts`, `food_trials_accepts`,
  `spawn_food_accepts`, `spawn_select_accepts`, `initialize_deer_accepts`, with
  `world_observe`, `world_step`, and `spawn_select` standing beside their kinds
  for their postconditions). The attempt, ANSI, and baseline host transitions
  that delegate refusal to `Host.World.observe` or `Host.World.step`
  (`Host.OwnedStep.environment`, `Host.PreparedStep.environment`,
  `Host.PreparedStep.commit`, `Host.Attempt.sense`, `Host.Attempt.tick`,
  `Host.Attempt.finish`, `Host.Attempt.close`, `Host.Attempt.complete`,
  `Host.AnsiState.tick` which also refuses on step-counter overflow, and
  `Host.BaselineAttempt.tick`) currently state postconditions, delegation
  equalities, or single-witness acceptances with no decision-kind theorem in
  `Acorn.Decisions` or `AcornVerif.Decisions`; a specification naming
  `Host.World.observe` also reaches `Host.Inventory.owns`.
- **The specification reads a part of the input whose type declares an invariant
  that names tests that the function runs.** Under the shared-test rule below,
  reading a structure whose declared invariant reaches `Binary32.isNaN`,
  `Binary32.less`, `Binary32.negative`, or `NumericState.resumable` excludes the
  kind: `Features.Lifecycle.lessUseful`, `Features.Lifecycle.candidate`,
  `Features.Lifecycle.prefer`, `Host.Microduck.Idle.sense`,
  `Host.Microduck.Awaiting.release`, `TemporalControl.serve`,
  `TemporalControl.serveDraw`, `TemporalControl.dispatchMeta`,
  `TemporalControl.atBoundary`, `TemporalControl.selectWithOperations`,
  `TemporalControl.select`, `TemporalControl.step`,
  `TemporalControl.drawBoundary`, and `TemporalControl.drawFirst`. Kinds for
  these functions are remaining work of
  [#105](https://github.com/rbeauchamp/acorn/issues/105).
- **The verdict is the guard of the function and applies a definition with no
  independent proposition.** `Host.Viewer.Admission.receive` and
  `Host.Viewer.HealthAdmission.receive` depend on `Host.Viewer.Capture.follows`
  and `Host.Viewer.Capture.after`, and return a pair whose state depends on the
  identity (whereas `Regula.Dependent.isSome` and `Regula.Dependent.isOk` apply
  only to optional or error results).
- **The result has a dependent type that is neither optional nor an error.**
  `Costed.findIdx?` returns its index paired with the equation naming it.

In `AcornVerif.Decisions`, contracts whose proofs require the proof library are
counted toward the registrations in `Acorn.Decisions`. Registered decisions with
kinds proved in `AcornVerif.Decisions` include:

- World initialization, observation, stepping, passive updates, and spawn/deer
  generation: `Host.World.initial` (`world_initial_accepts`, two-way Regula
  Decides kind over `Regula.Dependent.isOk`, registered in `Acorn.Decisions` by
  `Host_World_initial_registered`, with `Acorn.Decisions.world_initial` stating
  the accepted initial world's fields beside it); and eight one-way Regula
  DecidesCompletely kinds over admissible configurations: `Host.World.observe`
  (`world_observe_accepts`, registered by `Host_World_observe_registered`, with
  `Acorn.Decisions.world_observe` beside it), `Host.World.observeTile`
  (`observe_tile_accepts`, registered by `Host_World_observeTile_registered`),
  `Host.World.step` (`world_step_accepts`, over `Regula.Dependent.isOk` and
  `WorldAction`, registered by `Host_World_step_registered`, with
  `Acorn.Decisions.world_step` beside it), `Host.wanderPopulation`
  (`wander_population_accepts`, registered by
  `Host_wanderPopulation_registered`), `Host.foodTrials` (`food_trials_accepts`,
  registered by `Host_foodTrials_registered`), `Host.spawnFood`
  (`spawn_food_accepts`, registered by `Host_spawnFood_registered`),
  `Host.selectSpawn` (`spawn_select_accepts`, registered by
  `Host_selectSpawn_registered`, with `AcornVerif.Decisions.spawn_select` beside
  it), and `Host.initializeDeer` (`initialize_deer_accepts`, registered by
  `Host_initializeDeer_registered`).
- Terrain generation and readers: `Host.valueNoise`, `Host.octaveLoop`,
  `Host.fbm`, `Host.terrain`, `Host.World.tileKind`, and `Host.World.enterable`
  (two-way kinds characterizing successful sampling, using
  `CurrentTerrain.PastLast` and `CurrentTerrain.LatticeAdmits`, with
  `terrain_read`, `tile_kind`, and `world_enterable` stating accepted values
  beside them); and `Host.walkableTile` (`terrain_walkable`, a two-way kind
  accepting a tile exactly when every world of the configuration can enter it).
  The walkability check rejects water and mountain even when the terrain lookup
  succeeds.
- Paid actions: `Host.performAction` and `Host.payAndAct` (two-way kinds, with
  `perform_action` and `pay_and_act` stating accepted energy and movement
  effects).
- Spawn helpers: `Host.countKindNear` and `Host.considerSpawn` (two-way kinds
  `spawn_count` and `spawn_consider`, with `spawn_count_value` and
  `spawn_consider_value` beside them).
- Certificate checkers and action replay: `Host.replayCertified`,
  `Host.ReplayCertificate.check`, and `Host.World.advanceActions` (two-way
  kinds), and `Host.regionBlocked`, `Host.BlockedCertificate.check`,
  `Host.stanceCertified`, and `Host.StanceCertificate.check` (sound kinds, with
  refusal statements beside them).
- Checkpoint and learner checks: `Checkpoint.load` and `Checkpoint.resume`
  (sound kinds, with `checkpoint_load_accepts` and `checkpoint_resume_accepts`
  beside them), `Host.Released.environment` (`released_environment_exact`,
  two-way kind), and `NumericState.clearAt` (`learner_clear`, two-way kind).

In `Acorn.Decisions`, world admission and its Boolean decision helpers carry
two-way Regula Decides contracts with independent numeric specifications
(sharing no Acorn Boolean test): `Host.isPastLast` (`is_past_last`),
`Host.scaleAdmitsOctave` (`scale_admits_octave`), `Host.scaleAdmitsRange`
(`scale_admits_range`), `Host.RawWorldConfig.admissible`
(`raw_world_config_admissible`), `Host.WorldConfig.admit` (`world_config_admit`),
and `Host.WorldConfig.standard` (`world_config_standard`).

Kindless requirements in `AcornVerif.Decisions` fall into five reasons (each
required by name in `AcornOwnership.anchors`, alongside non-decisions
`Agent.input`, `AgentConstruction.execute`, `Checkpoint.managedWords`, and
definitions shared by specifications):

- **Round-trip payload specifications that reach reader tests:**
  `Checkpoint.admitPayload` and `Checkpoint.loadCandidate` (`payload_admit`,
  `candidate_load`, with `payload_admit_value` and `candidate_load_value` beside
  them; kinds are excluded because `imagePayload` and agent-image invariants
  reach ten tests run by admission, including `NumericState.resumable`,
  `Binary32.isNaN`, and `Binary32.less`, remaining work of
  [#105](https://github.com/rbeauchamp/acorn/issues/105)).
- **Witness acceptance statements beside kindless attempt transitions:**
  `Host.Attempt.finish` (`attempt_finish_accepts`) and `Host.Attempt.complete`
  (`attempt_complete_accepts`).
- **Comparator correspondence and campaign termination bounds:**
  `Host.BaselineAttempt.tick` (`baseline_corresponds`),
  `Host.runBaselineCampaign` (`campaign_finishes`), and `Host.runRandomBaseline`
  (`random_baseline_finishes`). On admissible configurations world
  initialization and world steps never refuse (`initial_isOk_iff`,
  `admissible_step_isOk`), while these statements quantify over arbitrary
  `WorldConfig` values and bound unfinished termination on admitted plans.
- **Input invariant reaching tests:** `NumericState.resumable`
  (`learner_resumable`, checking `CurrentLearner.ScheduleInv`: zero
  non-eligible registers, finite `[0, 5]` pruning references, duplicate-free
  eligible indices, and nonzero eligible traces when a standalone second loop
  is permitted; excluded from a kind because `NumericState`'s type invariant
  reaches `Binary32.isNaN` and `Binary32.less` via `Portable.ln`, remaining
  work of [#105](https://github.com/rbeauchamp/acorn/issues/105)).
- **Dependent pair results whose verdict component is not an optional or error
  result:** `Features.beginExploration` (`exploration_begins`, specifying the
  53-bit top fraction of xoshiro256** directly in bit-vector operations after
  David Blackman and Sebastiano Vigna, xoshiro256** reference implementation,
  2018, *next*, `https://prng.di.unimi.it/xoshiro256starstar.c`, without
  claiming the resulting run or post-draw generator state),
  `Lifetime.DemonStats.advanceSlot` (`slot_settles`, where the
  `FeatureConstants.maxSettlement` age cap leaves settlement verdicts unchanged
  because `settleAfter ≤ maxSettlement`, without claiming the reported
  settlement or post-visit slot state owned by
  `AgreementLifecycle.advanceSlot_selected`), `NumericState.firstLoopElement`
  (`first_loop_prune`, where zero decay prunes any finite trace via
  `CurrentControl.stop_prunes`, without claiming updated weight, log-step-size,
  or register values owned by `NumericState.firstLoopElement_eq`), and
  `Checkpoint.loadKeeping` (`load_keeping`).

Notable scope notes for registered and helper statements in
`AcornVerif.Decisions`: `AcornVerif.Decisions.fresh` duplicates
`Acorn.Decisions.fresh` locally because no module may import `Acorn.Decisions`;
`spawn_count` (`Host.countKindNear`) has no early exit and reads every tile of
its `(2r + 1)²` square (`SquareAdmits`); `task_satisfied` (DecidesCompletely)
claims no soundness outside observations produced by `Goal.observe`;
`rank_index` (DecidesSoundly) claims no completeness; `precision_admit`
(DecidesCompletely) claims no soundness (`AgreementTelemetryPrecision.precision_fields`
states accepted fields); `squared_admit_exact` checks exact rational discrepancy
in least positive binary32 subnormal units (`2^-149`); `maximum_sum` applies
Lean core's 64-bit unsigned-to-float conversion, which is exact for counts
below `2^53` (`CurrentOrder.numerical64_ofUInt64`); `discount_gamma` relies on
binary32 spacing `2^-24` on `[1/2, 1)` making `≤ 2^-25` nearest; and
`discount_horizon` bounds `horizon * (1 - 2^-23) ≤ 1/(1 - γ) ≤ horizon`.

## Tests that a specification does not share

A kind compares a function with its specification as the two are defined now.
Where both sides call one test, a defect of that test changes both together and
the proof of the kind can stay valid. Therefore the specification of a contract
with a kind reaches no test that the function or the acceptance predicate also
reaches, read at any depth through the declarations it names and the declared
types of the parts of the input it reads. Review applies this rule; no check of
Regula or Acorn executes it.

A test is a function returning a Boolean or a definition returning a Boolean
equality instance outside Lean's own library. Structure field projections are
not tests: they read stored data (for example, `inventory_craft` may read
`Host.Inventory.axe` and `Host.Inventory.boat`).

Propositions that replace tests in specifications, each with its equivalence
theorem:

- `Binary32.Negative` (`Binary32.negative_iff`)
- `Binary32.IsNaN` and `Binary64.IsNaN` (`Binary32.isNaN_iff`,
  `Binary64.isNaN_iff`)
- `Binary32.Less` and `Binary64.Less` (`Binary32.less_iff`, `Binary64.less_iff`)
- `Binary32.LessOrEqual` (`Binary32.lessOrEqual_iff`)
- `Host.TileKind.Walkable` (`Host.TileKind.walkable_iff`)
- `Host.Inventory.Owns` (`Host.Inventory.owns_iff`)
- `FeatureProfile.Resumable` (`FeatureProfile.checkpoint_iff`)
- `Host.InBox` (`Host.inBox_iff`)
- `Host.World.GoalSatisfied` and `Host.World.Attained`
  (`Host.World.goalSatisfied_iff`)
- `Host.FoodDue` (`Host.foodDue_iff`)
- `Host.QuotientPastLast` (`Host.isPastLast_iff_units`),
  `Host.ScaleAdmitsRange` (`Host.scaleAdmitsRange_spec_iff`), and
  `Host.RawWorldConfig.Admissible` (`Host.RawWorldConfig.admissible_spec_iff`)

Functions reached by specifications decide those propositions rather than
calling the tests directly: `Binary32.key`, `Binary32.saturate`,
`Agreement.units`, `Checkpoint.imagePayload`, `Host.wanderDeer`,
`Lifetime.sumUpdate`, `Conversion.toI64Word`, `Host.floor32`, `Host.castWord`,
`Host.classifyTerrain`, `Host.World.enterable`, `PolicySnapshot.best`,
`PolicySnapshot.candidates`, `PolicySnapshot.probabilities`,
`Host.Inventory.craft`, `Host.spawnFood`, and `Host.World.step`. World
vocabulary types (`Host.Direction`, `Host.Action`, `Host.TileKind`,
`Host.Position`, `Host.BoxPosition`) derive decidable equality with no custom
Boolean equality instance.

Non-Boolean shared helpers stay a matter of review. Review admits primitive
operations of Lean's number types (`Binary32.div`, `Binary32.mul`), readers with
independent statements of their own, and direct stored-field readers
(`Weight.value`, `Features.Lifecycle.progress`,
`Host.Viewer.Lifecycle.phaseValue`). The independent statements in
`Acorn.Decisions` are `coordinate_float` (`Host.coordinateFloat`) and the
eighteen shared-definition statements (`rotate_left`, `unit_feature`,
`reach_distance`, `numeral_chars`, `fnv_hash`, `u64_codec`, `header_codec`,
`day_phase`, `snapshot_masses`, `craft_recipe`, `goal_kind_code`,
`goal_item_code`, `interface_layout`, `rank_width`, `rank_dimension`,
`world_side`, `box_position`, and `box_center`, where `box_center` stands beside
`spawn_select` and `snapshot_masses` also covers the value of
`PolicySnapshot.probabilitiesCosted`). The independent statements in
`AcornVerif.Decisions` cover `Agreement.squaredUnits`, `Lifetime.maximumSum`,
`Host.Microduck.spelled`, `Host.Microduck.Decimal.ofNumeral`,
`Host.Microduck.Decimal.fixed`, `Host.BoxPosition.facingPosition`,
`Host.Direction.delta`, `Discount.gamma`, `Discount.horizon`,
`ValueRule.domain`, `Discount.predictionRange`, `Lifetime.Quantity.bound`, and
`Agreement.envelopeUnits`. Shared readers without independent statements of
their own (`Binary32.key`, `Binary32.magnitude`, `Binary32.negate`,
`Binary64.key`, `Binary64.magnitude`, `Conversion.widen`, `Host.World.step`,
`Host.World.setGoal`, `Host.terrain`, plus helpers applied by kindless
statements) are remaining work of
[#67](https://github.com/rbeauchamp/acorn/issues/67).

In particular, the two-way kinds of `Host.isPastLast`, `Host.scaleAdmitsOctave`,
`Host.scaleAdmitsRange`, `Host.RawWorldConfig.admissible`,
`Host.WorldConfig.admit`, and `Host.World.initial` and the eight one-way
complete kinds of `Host.World.observe`, `Host.World.observeTile`,
`Host.World.step`, `Host.wanderPopulation`, `Host.foodTrials`, `Host.spawnFood`,
`Host.selectSpawn`, and `Host.initializeDeer` share none of `Host.isPastLast`,
`Host.scaleAdmitsOctave`, `Host.scaleAdmitsRange`,
`Host.RawWorldConfig.admissible`, `Host.octaveScale`,
`Host.RawWorldConfig.admitLo`, or `Host.RawWorldConfig.admitHi`; their
specifications state the exact numeric quotient condition through
`Host.QuotientPastLast`, `Host.ScaleAdmitsRange`, and
`Host.RawWorldConfig.Admissible`, built directly from `Host.coordinateFloat`
(`coordinate_float`), `Binary32.div`, `Binary32.mul`, `Binary32.Finite`,
`Binary32.Negative`, and `Conversion.magnitudeUnits32`.

## What carries no separate contract

This inventory is not checked for completeness by any tool: a new definition
returning a Boolean, optional, error, or decidable result can arrive with no
contract and no entry here.

- Structure field projections, non-function default field values, and derived
  comparison instances (stored data or compiler-generated equality/ordering).
- Functions whose result type is `Decidable` carry both directions of their
  decision in their type and therefore carry no separate executable contract.
  Decision procedures with proved properties (such as
  `Binary32.positiveDecidable`, `Binary32.instDecidableFinite`, and
  `Host.instDecidableFoodDue`) are still explicitly registered in
  `Acorn.Decisions` via Regula's RegisteredDecision; derived comparison
  instances and unreferenced `Decidable` helpers carry neither a registration
  nor a contract.
- Definitions not named by any public theorem of the maintained libraries,
  together with internal private helpers (whose private proof lemmas support
  contracted entry points such as `Json.parse` and `Json.Numeral.scan`): the
  remaining parsers of `Host.Cli`, native drivers and `NativeApp`, private JSON
  helpers, viewer envelope and map decoders (`Host.Viewer.MapBytes.admit`,
  `Host.Viewer.decodeMapRuns`, `Json.decode`), and endurance summary helpers
  (`Host.Endurance.Rates.summary`, `Host.Endurance.ErrorStats.summary`,
  `Host.Endurance.Reduction.energySummary`).
- Definitions whose bodies directly delegate to a contracted or `Decidable`
  definition (`Prediction.admit`, `LogStepSize.admit`, `Lifetime.SumCount.admit`,
  and viewer line emitters that apply `Host.Viewer.wireText` and
  `Host.Viewer.sseLine`).
- Unverified certificate search and its CLI driver: `Host.CertificateSearch`
  helpers propose candidate paths and regions with no contract of their own;
  `Host.CertificateDriver.execute` admits a standard world via
  `Host.WorldConfig.standard` and `Host.World.initial`, checks that curriculum
  entries 3 and 7 are reach goals, calls `Host.CertificateSearch.explore`,
  validates every proposal through the contracted checkers
  `Host.ReplayCertificate.check`, `Host.BlockedCertificate.check`, and
  `Host.StanceCertificate.check`, and constructs a
  `Host.CertificateDriver.Report`.
- Viewer supervisor transitions and classifiers whose properties are proved by
  the supervisor's own anchored theorems (`Host.Viewer.Lifecycle.reserve`,
  `Host.Viewer.Lifecycle.beginArchive`, `Host.Viewer.Lifecycle.archived`,
  `Host.Viewer.Lifecycle.archiveIntent`, `Host.Viewer.Lifecycle.exhausted`,
  `Host.Viewer.Lifecycle.retryReady`, `Host.Viewer.PersistedState.launch`,
  `Host.Viewer.Pending.writes`, `Host.Viewer.Pending.clears`,
  `Host.Viewer.Pending.serves`; kinds are remaining work).
- Definitions in the proof library `AcornVerif`, which has no executable.
- Named definitions that decide nothing (`Host.Microduck.Phase.armed`,
  `Host.Microduck.Phase.last`, `Host.Microduck.Reading.age`,
  `Handcrafted.TemporalControl.takeoverValue`,
  `Handcrafted.DefaultConstruction.runPrefix`,
  `Handcrafted.TemporalControl.interrupt`,
  `Handcrafted.TemporalControl.refreshFree`, `Host.Viewer.goalTelemetry`) or
  whose verdict equals a contracted definition (`Host.Microduck.Idle.tick`,
  `Host.Microduck.Awaiting.tick`, `Host.Microduck.Stage.attend`).
- Effects in `IO` (covered through pure cores such as `Checkpoint.resume` and
  `Checkpoint.saveBytes` where present; OS/lock/filesystem effects rely on the
  verification guide's concurrency and OS assumptions), `Bootstrap`, and
  reviewed tooling under `lean/AcornTools`.

No kind says that a specification is the intended one, that every caller acts on
the verdict, or which value an accepting result carries. Exactness of the
accepted value is stated by the theorems beside each definition. No executable
and no other module imports `Acorn.Decisions`, so no native entry point links
its witness values or registration declarations.
