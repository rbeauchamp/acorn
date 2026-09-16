/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentPrefix
import AcornVerif.CurrentControl
import AcornVerif.CurrentRetirement
import AcornVerif.CurrentBackupBounds
import Mathlib.Tactic.FinCases

/-!
# Autonomous replacement: execution-linked obstructions

The domain is finite prefixes of the actual full-agent transition, with current
encoding, policy draws and binary32 arithmetic. A never-selected primitive row
vetoes every imprint slot, independently of the observation/reward sequence,
option selection, planning, refresh and hash aliases. This is an exposure
obstruction, not a claim that all streams retain a dormant row forever.

For the ordinary ranked discounted composition, there is also a distinct
short-invocation obstruction. Consider finite admitted callback executions from
cold construction (or a restore with cold models), in which every invoked option
ends before its second returned action, and its initiation encoding has at most
1900 active slots. Rewards at its endings must be finite with magnitude at most
2^32; every world-produced reward satisfies this premise. This condition refers
to exposure and inputs, not the retirement predicate.

The implementation argument follows the complete model write schedule:
* `dispatchMeta` calls `beginTemporal`; `first_option_model` identifies its
  immediate `stepTemporal` as a model no-op and gives age one.
* `Skill.goal_ends` supplies a non-circular sufficient ending condition. On the
  next option decision, goal feedback bypasses the continuing/model-step branch.
  Other ending reasons before a second action have the same model call order.
* `ending_option_model` identifies the terminal callback. The actual begin/terminal
  composition preserves initial reward-model beta (`one_action_model_beta`);
  `one_action_models_beta` closes arbitrary finite repetitions, while
  `model_begin_beta` covers the intermediate retirement check after initiation.
* Primitive actions, served exploration, prediction feedback and planning do not
  update model storage. Assignment identity retention keeps the same model;
  a changed identity or restore creates another cold reward model. A detached
  old owner's terminal result cannot write the replacement objective.
* Thus, before a putative first retirement, each stored model is cold, between
  such invocations, or just begun. `reward_model_veto` rules out that retirement.
  This scheduling composition is a source-linked structural argument; the
  omitted-primitive-row path theorem below is the separate full-agent Lean proof.

The exposure premise is inhabited at the admitted callback interface, without
choosing actions: arbitrary observations with both optional tile channels absent
have at most 1712 encoded features under the default tilings/bank bound, even if
all bank projections activate (`quiet_patch_sparse`). Goal feedback on every
active-option decision ensures the short invocation premise independently of the
policy draw. No claim says the endogenous world/curriculum produces every such
callback sequence, or that all learning executions have short invocations.
Weight credit and primitive-action coverage do not remove this obstruction;
longer invocations, other inputs and positive complete-ensemble reachability
remain separate questions. No utility criterion is inferred from beta alone.

A separate one-callback obstruction follows assignment replacement itself.
`TwoRefreshChanges` reads the pending flag and compares two existing complete
assignment identities with the actual Demon-0 ranking. At a discounted free
dispatch, both replacements start cold, and at most one can receive option
credit. The other model remains cold through common completion.
`act_two_refresh_changes` follows the actual `Agent.act` call and proves refusal
before retirement, then unchanged event history. Its free-boundary premise reads
the returned meta-decision; it assumes neither a chosen action nor eligibility.
The result has no sparsity or reward-magnitude premise. Occurrence of these
assignment changes along an initialized native path remains a separate obligation;
this conditional obstruction does not discharge complete-reader reachability.

The history quota is separate from eligibility. Neither structural checkpoint
admission nor the direct-write predicate-inhabitation theorem supplies a learning
trajectory. Compiler/native numeric primitives and host input production retain
their existing trusted boundaries. No learning-benefit claim is made here.
-/
namespace AcornVerif.CurrentReplacement
open Acorn Acorn.Features Acorn.Handcrafted

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

/-- Number of actual recorded replacements, read from the sole lifecycle owner. -/
def historyCount (state : Agent profile config criterion dimension planning) : Nat :=
  state.control.runtime.lifecycle.representation.progress.events.length

/-- One initialized reader blocks its slot under its actual receiver-derived predicate. -/
theorem cold_reader_veto {numeric : Acorn.Config} (learner : Managed numeric dimension)
    (cold : learner.state = NumericState.initial numeric dimension) (feature : FeatIdx dimension) :
    learner.state.unitIsNegligible feature = false := by
  rw [cold]
  apply CurrentRetirement.initial_beta_veto
  simp [NumericState.initial, Vector.get]

/-- Every freshly initialized model exposes a cold reward reader, in either
criterion. Its duplicate discounted reader position adds no separate state. -/
theorem initial_model_reader (criterion : Criterion) :
    (⟨criterion.config .demon, Managed.initial _ dimension⟩ : PackedLearner dimension) ∈
      (Model.initial dimension criterion).readers := by
  cases criterion <;> simp [Model.initial, Model.readers]

/-- A cold model in any skill vetoes the complete scan, even when all primary
weights and step sizes were restored at the floor. -/
theorem cold_model_veto {discounts : List Discount}
    (ensemble : Ensemble config criterion dimension discounts)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (cold : (ensemble.skills.get slot).model = Model.initial dimension criterion)
    (feature : FeatIdx dimension) : ensemble.negligible feature = false := by
  let reader : PackedLearner dimension := ⟨criterion.config .demon, Managed.initial _ _⟩
  have member : reader ∈ ensemble.readers := by
    simp only [Ensemble.readers, List.mem_append]
    apply Or.inl
    apply Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨ensemble.skills.get slot, by simp [Vector.get], ?_⟩
    apply List.mem_append.mpr
    right
    rw [cold]
    exact initial_model_reader criterion
  have veto := cold_reader_veto reader.2 rfl feature
  cases eligible : ensemble.negligible feature with
  | false => rfl
  | true =>
    have accepted := (ensemble.negligible_iff feature).mp eligible reader member
    change reader.2.state.unitIsNegligible feature = true at accepted
    simp [veto] at accepted

/-- Restoration restarts models cold, so structural primary admission alone
cannot enable immediate replacement. No claim of subsequent non-reachability. -/
theorem restored_veto {discounts : List Discount}
    (ensemble : Ensemble config criterion dimension discounts)
    (image : PrimaryImage dimension discounts)
    (assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (feature : FeatIdx dimension) :
    (ensemble.restore image assignments).negligible feature = false := by
  apply cold_model_veto _ ⟨0, by decide⟩
  simp [Ensemble.restore, Vector.get]

/-- Changing an assignment reinstates a model veto at the installation boundary.
Later learning must be considered separately before inferring refusal at `act`. -/
theorem installed_veto {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (changed : state.lifecycle.consumers.skills[slot.val].interest.sameAssignment target = false)
    (feature : FeatIdx dimension) :
    (state.install slot target).lifecycle.consumers.negligible feature = false := by
  apply cold_model_veto _ slot
  change ((state.install slot target).lifecycle.consumers.skills[slot.val]).model = _
  simp [FreeDispatch.install, changed, Skill.initial]

/-- The reward model's actual stored learner, used only as a proof-side
projection. The continuation state and discounted reader alias remain accounted. -/
def rewardModel (model : Model dimension .discounted) :
    Managed (Criterion.discounted.config .demon) dimension :=
  match model with | .discounted reward _ => reward

/-- Initial reward-model beta, without claiming its learned weights stay zero. -/
def ModelBetaInitial (model : Model dimension .discounted) : Prop :=
  ∀ idx, ((rewardModel model).state.beta.get idx).value =
    (rewardModel model).state.rails.initial.value

/-- Reward-model initialization establishes the beta invariant in real storage. -/
theorem initial_model_beta : ModelBetaInitial (Model.initial dimension .discounted) := by
  intro idx
  simp [rewardModel, Model.initial, Managed.initial,
    NumericState.initial, Vector.get]

/-- The model's actual begin/terminal callbacks preserve initial reward beta
through arbitrary weight learning. Raw reward is restricted to a finite envelope;
continuation can be arbitrary because it has a separate physical learner. -/
theorem one_action_model_beta (model : Model dimension .discounted)
    (features : SwiftTd.ActiveSet dimension) (reward terminal : Binary32)
    (cold : ModelBetaInitial model) (sparse : features.indices.length ≤ 1900)
    (finite : reward.Finite) (bound : |CurrentArithmetic.numerical32 reward| ≤ 4294967296) :
    ModelBetaInitial ((model.begin features).terminal reward terminal) := by
  cases model with
  | discounted rewardLearner continuation =>
    exact fun idx => (CurrentRetirement.one_action_trajectory_cold (.discounted .g99)
      rewardLearner.state features reward finite bound cold sparse idx).1

/-- Initiation itself already has the reward-model beta invariant, before any
terminal credit. This is the state the first returned option action observes. -/
theorem model_begin_beta (model : Model dimension .discounted)
    (features : SwiftTd.ActiveSet dimension) (cold : ModelBetaInitial model)
    (sparse : features.indices.length ≤ 1900) : ModelBetaInitial (model.begin features) := by
  cases model with
  | discounted reward continuation =>
    exact fun idx => (CurrentRetirement.short_begin_cold (.discounted .g99)
      reward.state features cold sparse idx).1

/-- An initial-beta reward model vetoes every slot in its complete ensemble,
including slots on which its weights have received nonzero terminal credit. -/
theorem reward_model_veto {discounts : List Discount}
    (ensemble : Ensemble config .discounted dimension discounts)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (cold : ModelBetaInitial (ensemble.skills.get slot).model)
    (feature : FeatIdx dimension) : ensemble.negligible feature = false := by
  let model := (ensemble.skills.get slot).model
  let reader : PackedLearner dimension := ⟨_, rewardModel model⟩
  have modelMember : reader ∈ model.readers := by
    dsimp only [reader]
    cases model
    simp [rewardModel, Model.readers]
  have member : reader ∈ ensemble.readers := by
    simp only [Ensemble.readers, List.mem_append]
    apply Or.inl
    apply Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨ensemble.skills.get slot, by simp [Vector.get], ?_⟩
    exact List.mem_append.mpr (Or.inr modelMember)
  have veto := CurrentRetirement.initial_beta_veto (rewardModel model).state feature (cold feature)
  cases eligible : ensemble.negligible feature with
  | false => rfl
  | true =>
    have accepted := (ensemble.negligible_iff feature).mp eligible reader member
    change (rewardModel model).state.unitIsNegligible feature = true at accepted
    simp only [veto, Bool.false_eq_true] at accepted

/-- A newly begun option's first returned action does not execute a model
step and records age one. Policy credit still executes, and the policy draw is unrestricted. -/
theorem first_option_model (skill : Skill config .discounted dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    let begun := skill.beginTemporal (modelOperations .discounted dimension)
      features potential true rate
    let result := begun.1.stepTemporal (modelOperations .discounted dimension)
      begun.2.1 begun.2.2 reward gain rng
    result.1.model = skill.model.begin features ∧ result.2.1.age.val = 1 := by
  simp only [Skill.beginTemporal, Skill.beginOption, Skill.stepTemporal, Skill.optionStep,
    OptionActivation.learning, modelOperations, if_true, Nat.lt_irrefl,
    decide_false, Bool.and_false, Bool.false_eq_true, if_false]
  exact ⟨trivial, rfl⟩

/-- Actual terminal dispatch supplies the reward and continuation to those
same model callbacks, while policy shaping remains a separate update. -/
theorem ending_option_model (skill : Skill config .discounted dimension)
    (ending : EndingPayload true) (reward terminal : Binary32) (gain : RewardRate) :
    (skill.endTemporal (modelOperations .discounted dimension) ending reward terminal gain).model =
      skill.model.terminal reward terminal := by
  simp only [Skill.endTemporal, Skill.terminateOption, OptionActivation.learning,
    modelOperations, if_true]

/-- Proof-side grouping of the actual model callbacks for one-action invocations.
The first action's no-model-write equation is `first_option_model`; this fold
is not an alternative learner or an input to the application. -/
def oneActionModels (model : Model dimension .discounted)
    (episodes : List (SwiftTd.ActiveSet dimension × Binary32 × Binary32)) :
    Model dimension .discounted :=
  episodes.foldl (fun current episode =>
    (current.begin episode.1).terminal episode.2.1 episode.2.2) model

/-- Every finite sequence of one-action invocations executes terminal weight
credit while retaining initial reward-model beta. Features and rewards are quantified,
not chosen by a diagnostic fixture or assumed to make the retirement guard false. -/
theorem one_action_models_beta (model : Model dimension .discounted)
    (episodes : List (SwiftTd.ActiveSet dimension × Binary32 × Binary32))
    (cold : ModelBetaInitial model)
    (inputs : ∀ episode ∈ episodes, episode.1.indices.length ≤ 1900 ∧
      episode.2.1.Finite ∧ |CurrentArithmetic.numerical32 episode.2.1| ≤ 4294967296) :
    ModelBetaInitial (oneActionModels model episodes) := by
  induction episodes generalizing model with
  | nil => exact cold
  | cons episode rest ih =>
    have input := inputs episode (by simp)
    exact ih _ (one_action_model_beta model episode.1 episode.2.1 episode.2.2
      cold input.1 input.2.1 input.2.2) (fun next member => inputs next (by simp [member]))

/-- World-produced reward satisfies the finite terminal premise for every
completion flag. The independent raw callback domain is strictly larger. -/
theorem world_reward_regular (result : Host.StepResult) :
    result.reward.Finite ∧ |CurrentArithmetic.numerical32 result.reward| ≤ 4294967296 := by
  cases done : result.done <;> simp only [Host.StepResult.reward, done, Bool.false_eq_true,
    if_false, if_true]
  · constructor
    · decide
    · change |(0 : ℚ)| ≤ 4294967296
      norm_num
  · constructor
    · decide
    · change |(1 : ℚ) * 8388608 * 2 ^ (-23 : Int)| ≤ 4294967296
      norm_num

private theorem flat_map_length_bound {α β : Type} (values : List α) (f : α → List β)
    (limit : Nat) (bounded : ∀ value ∈ values, (f value).length ≤ limit) :
    (values.flatMap f).length ≤ values.length * limit := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    have first := bounded value (by simp)
    have restBound := ih (fun next member => bounded next (by simp [member]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem task_words_bound (task : Host.TaskObservation) (mode : TaskFeatureMode) :
    (taskWords task mode).length ≤ 10 := by
  cases task <;> simp only [taskWords, List.length_cons, List.length_nil] <;>
    first | omega | (split <;> simp)

/-- A broad default-construction input class satisfies the short-trajectory
sparsity premise regardless of hash aliases, bank projections, kinds, inventory,
task coordinates, energy or cached predictions: only the two optional tile
channels are absent. No generated feature is assumed inactive. -/
theorem quiet_patch_sparse (bank : Bank Host.patchShape config) (observation : Host.Observation)
    (predictions : Predictions) (mode : TaskFeatureMode)
    (tilings : config.tilings.toNat ≤ 8) (units : config.units.count ≤ 512)
    (quiet : ∀ row col, ((observation.tiles.get row).get col).food = 0 ∧
      ((observation.tiles.get row).get col).deer = 0) :
    (encodeObservation dimension bank observation predictions mode).indices.length ≤ 1712 := by
  have tileBound : ∀ row col,
      (tileWords row col ((observation.tiles.get row).get col)).length ≤ 1 := by
    intro row col
    simp [tileWords, (quiet row col).1, (quiet row col).2]
  have rows : ∀ row, ((List.finRange Host.patchShape.side).flatMap fun col =>
      tileWords row col ((observation.tiles.get row).get col)).length ≤ 11 := by
    intro row
    simpa [Host.patchShape, Acorn.FeatureConstants.patchSide] using
      flat_map_length_bound (List.finRange Host.patchShape.side)
        (fun col => tileWords row col ((observation.tiles.get row).get col)) 1
        (fun col _ => tileBound row col)
  have cells := flat_map_length_bound (List.finRange Host.patchShape.side)
    (fun row => (List.finRange Host.patchShape.side).flatMap fun col =>
      tileWords row col ((observation.tiles.get row).get col)) 11 (fun row _ => rows row)
  have tasks := task_words_bound observation.task mode
  have channels : (predictionWords predictions).length ≤ 11 := by
    simpa [predictionWords, Acorn.FeatureConstants.demonCount] using predictions.bounded
  have words : (observationWords observation predictions mode).length ≤ 150 := by
    simp only [observationWords, List.length_append, List.length_cons, List.length_nil]
    change _ ≤ (121 : Nat) at cells
    omega
  have encoding := encode_length dimension bank
    (observationWords observation predictions mode) (observationPatch observation)
  have product := Nat.mul_le_mul tilings words
  change (encode dimension bank (observationWords observation predictions mode)
    (observationPatch observation)).indices.length ≤ 1712
  omega

/-- Independent Boolean signals at the admitted observation boundary. -/
def booleanObservation (bits : Vector Bool 11) : Host.Observation where
  tiles := ⟨#[(#v[
    ⟨if bits.get 1 then 4 else 2, 0, 0⟩,
    ⟨if bits.get 2 then 6 else 2, 0, 0⟩,
    ⟨if bits.get 3 then 7 else 2, 0, 0⟩,
    ⟨if bits.get 4 then 0 else 2, 0, 0⟩,
    ⟨2, if bits.get 5 then 1 else 0, 0⟩,
    ⟨2, 0, 0⟩, ⟨2, 0, 0⟩, ⟨2, 0, 0⟩,
    ⟨2, 0, 0⟩, ⟨2, 0, 0⟩, ⟨2, 0, 0⟩] : Vector Host.TileObservation 11)] ++
    Array.replicate 10 (Vector.replicate 11 (⟨2, 0, 0⟩ : Host.TileObservation)),
    by simp [Host.patchShape, Acorn.FeatureConstants.patchSide]⟩
  energy := if bits.get 6 then 3 else 4
  day := if bits.get 7 then 4 else 0
  task := .none
  inventory := ⟨if bits.get 8 then 1 else 0, if bits.get 9 then 1 else 0,
    0, 0, bits.get 10, false⟩

/-- Goal reward and done retain the host result coupling. -/
def booleanResult (bits : Vector Bool 11) : Host.RawStepResult :=
  Host.StepResult.raw { done := bits.get 0 }

theorem boolean_cumulants (bits : Vector Bool 11) (signal : Cumulant) :
    signal.eval (booleanObservation bits) (booleanResult bits).reward =
      indicator (bits.get signal) := by
  have choose_beq (b : Bool) (x y z : UInt8) :
      ((if b then x else y) == z) = (if b then x == z else y == z) := by
    cases b <;> rfl
  have food_nonzero (b : Bool) : ((if b then (1 : UInt8) else 0) != 0) = b := by
    cases b <;> rfl
  have low_energy (b : Bool) : decide ((if b then (3 : UInt8) else 4) ≤ 3) = b := by
    cases b <;> rfl
  fin_cases signal
  · change indicator (Binary32.zero.less (if bits.get 0 then .one else .zero)) =
      indicator (bits.get 0)
    cases bits.get 0 <;> rfl
  all_goals
    dsimp only [Cumulant.eval, booleanObservation, Host.TileKind.code,
      Host.patchShape, Acorn.FeatureConstants.patchSide, Acorn.FeatureConstants.demonCount]
    simp only [← Vector.any_toList]
    simp [Vector.toList, choose_beq, food_nonzero, low_energy,
      apply_ite, -Bool.if_false_right, -Array.any_toList]

private theorem index_map {α β : Type} {n : Nat} (values : Vector α n) (f : α → β) :
    (List.finRange n).map (fun i => f (values.get i)) = values.toList.map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [Vector.get]

private theorem indexed_tile_lengths (tiles : Vector Host.TileObservation Host.patchShape.side)
    (row : Fin Host.patchShape.side) :
    ((List.finRange Host.patchShape.side).flatMap
      (fun col => tileWords row col (tiles.get col))).length =
      (tiles.toList.map (fun tile => 1 + (if tile.food != 0 then 1 else 0) +
        (if tile.deer != 0 then 1 else 0))).sum := by
  simp only [List.length_flatMap, tileWords, List.length_append, List.length_cons,
    List.length_nil, apply_ite, Nat.zero_add]
  simpa only [apply_ite] using congrArg List.sum (index_map tiles
    (fun tile => 1 + (if tile.food != 0 then 1 else 0) +
      (if tile.deer != 0 then 1 else 0)))

theorem boolean_encoding_bound (bits : Vector Bool 11) (bank : Bank Host.patchShape config)
    (predictions : Predictions) (mode : TaskFeatureMode)
    (tilings : config.tilings.toNat ≤ 8) (units : config.units.count ≤ 512) :
    (encodeObservation dimension bank (booleanObservation bits) predictions mode).indices.length ≤
      1656 := by
  have cells : ((List.finRange Host.patchShape.side).flatMap (fun row =>
      (List.finRange Host.patchShape.side).flatMap (fun col =>
        tileWords row col (((booleanObservation bits).tiles.get row).get col)))).length ≤ 122 := by
    rw [List.length_flatMap]
    simp only [indexed_tile_lengths]
    rw [index_map (booleanObservation bits).tiles (fun row =>
      (row.toList.map (fun tile => 1 + (if tile.food != 0 then 1 else 0) +
        (if tile.deer != 0 then 1 else 0))).sum)]
    dsimp only [booleanObservation, Vector.toList, Host.patchShape,
      Acorn.FeatureConstants.patchSide]
    simp only [Vector.toArray_replicate,
      Array.toList_append, Array.toList_replicate,
      List.map_append, List.map_cons, List.map_nil, List.map_replicate,
      List.sum_append, List.sum_cons, List.sum_nil, List.sum_replicate]
    have foodWords : (if bits.get 5 then 2 else 1 : Nat) ≤ 2 := by
      cases bits.get 5 <;> decide
    have rowWords : 1 + (1 + (1 + (1 + ((if bits.get 5 then 2 else 1) + 6)))) ≤ 12 := by
      omega
    simpa [apply_ite, -Bool.if_false_right] using rowWords
  have channels : (predictionWords predictions).length ≤ 11 := by
    simpa [predictionWords, Acorn.FeatureConstants.demonCount] using predictions.bounded
  have words : (observationWords (booleanObservation bits) predictions mode).length ≤ 143 := by
    simp only [observationWords, List.length_append, List.length_cons, List.length_nil]
    have tasks : (taskWords (booleanObservation bits).task mode).length = 2 := rfl
    rw [tasks]
    omega
  have encoding := encode_length dimension bank
    (observationWords (booleanObservation bits) predictions mode)
    (observationPatch (booleanObservation bits))
  have product := Nat.mul_le_mul tilings words
  exact Nat.le_trans encoding (by omega)

theorem boolean_prefix_admitted (state : Agent profile config criterion dimension planning)
    (inputs : List (Vector Bool 11)) :
    ∃ finalState, state.runPrefix
      (inputs.map (fun bits => .act (booleanObservation bits) (booleanResult bits))) =
        .ok (finalState, false) ∧
      AgentPath state
        (inputs.map (fun bits => .act (booleanObservation bits) (booleanResult bits)))
        finalState false := by
  have total : ∀ (start : Agent profile config criterion dimension planning)
      (stream : List (Vector Bool 11)), ∃ finalState, start.runPrefix
        (stream.map (fun bits => .act (booleanObservation bits) (booleanResult bits))) =
          .ok (finalState, false) := by
    intro start stream
    induction stream generalizing start with
    | nil => exact ⟨start, rfl⟩
    | cons bits rest ih =>
      exact ih (start.act (booleanObservation bits)
        (booleanResult bits).reward (booleanResult bits).events.done).1
  obtain ⟨finalState, executed⟩ := total state inputs
  exact ⟨finalState, executed, state.prefix_path finalState _ false executed⟩

theorem neutral_interruption_iff (skill : Skill config .discounted dimension)
    {mode : Bool} (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (estimate : Binary32) (rate : ConsumerRate)
    (neutral : skill.interest = .learned .neutral)
    (room : activation.age.val < Acorn.FeatureConstants.optionMaxDuration)
    (finite : estimate.Finite)
    (bestFinite : (skill.policy.snapshot (count := primitiveCount) features
      (rate.resolve fun _ => skill.policy.exploreRate (count := primitiveCount))).best.Finite) :
    skill.decideOption activation features false false estimate rate = .ending .interrupted ↔
      CurrentArithmetic.numerical32 (skill.policy.snapshot (count := primitiveCount) features
        (rate.resolve fun _ => skill.policy.exploreRate (count := primitiveCount))).best <
          CurrentArithmetic.numerical32 estimate := by
  have bestZero := CurrentRetirement.add_zero_numeric _ bestFinite
  have estimateZero := CurrentRetirement.add_zero_numeric estimate finite
  simp only [Skill.decideOption, Bool.false_eq_true, ↓reduceIte, room, ↓reduceDIte,
    comparisonValue, Interest.stoppingValue, neutral, Assignment.stoppingValue,
    Assignment.bonus, Potential.value]
  change (if ((_ : Binary32).add .zero).less (estimate.add .zero) then
    OptionDecision.ending .interrupted else _) = .ending .interrupted ↔ _
  rw [CurrentOrder.numerical32_less _ _ bestZero.1 estimateZero.1,
    bestZero.2, estimateZero.2]
  split <;> simp_all

private theorem second_loop_weights {numeric : Acorn.Config}
    (state : NumericState numeric dimension) (features : SwiftTd.ActiveSet dimension)
    (acc : Binary32) :
    (state.learnSecondLoop numeric features acc).1.weights = state.weights := by
  have fold (indices : List (FeatIdx dimension)) (current : NumericState numeric dimension)
      (acc e t : Binary32) (overshoot : Bool) :
      (indices.foldl (fun (s, v) idx =>
        NumericState.secondLoopElement numeric overshoot e t s v idx)
          (current, acc)).1.weights = current.weights := by
    induction indices generalizing current acc with
    | nil => rfl
    | cons idx rest ih => exact ih _ _
  unfold NumericState.learnSecondLoop
  exact fold _ _ _ _ _ _

private theorem clear_row_state {numeric : Acorn.Config} {actions : Nat}
    (controller : Controller numeric dimension actions) (row : Action actions) :
    (controller.clear.learners.get row).state =
      (controller.learners.get row).state.clearTransient := by
  simp [Controller.clear, Vector.get, Fin.cast, Managed.apply, SwiftTd.Entry.apply]

private theorem credit_false_state {numeric : Acorn.Config}
    (learner : Managed numeric dimension) (delta vd decay : Binary32) :
    (learner.credit delta vd decay false).val.state =
      learner.state.learnFirstLoop numeric delta vd decay := rfl

private theorem clear_credit {numeric : Acorn.Config} {actions : Nat}
    (controller : Controller numeric dimension actions) (row : Action actions)
    (delta vd decay : Binary32) :
    ((controller.clear.learners.get row).credit delta vd decay false).val.state =
      (controller.learners.get row).state.clearTransient := by
  rw [credit_false_state, clear_row_state]
  exact CurrentControl.first_loop_empty _ rfl _ _ _

private theorem values_step_accumulator {numeric : Acorn.Config} {actions : Nat}
    (controller : Controller numeric dimension actions) (features : SwiftTd.ActiveSet dimension)
    (values : Vector Binary32 actions) (action : Action actions)
    (reward bootstrap decay : Binary32) :
    (controller.valuesStep features values action reward bootstrap decay).vDelta =
      (((controller.learners.get action).credit
        ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld)
        controller.vDelta decay controller.restartPending).val.state.learnSecondLoop
          numeric features .zero).2 := by
  simp [Controller.valuesStep, Vector.get, Fin.cast]

/-- The first policy action after the actual clear preserves every weight,
even for raw nonfinite credit inputs. Loop two changes adaptation registers,
but writes neither weights nor the cleared delta-weight accumulator. -/
theorem clear_values_step {numeric : Acorn.Config} {actions : Nat}
    (controller : Controller numeric dimension actions) (features : SwiftTd.ActiveSet dimension)
    (values : Vector Binary32 actions) (action : Action actions)
    (reward bootstrap decay : Binary32) :
    (∀ row,
      ((controller.clear.valuesStep features values action reward bootstrap decay).learners.get
        row).state.weights = (controller.learners.get row).state.weights) ∧
    (controller.clear.valuesStep features values action reward bootstrap decay).vDelta = .zero := by
  constructor
  · intro row
    by_cases selected : row = action
    · subst row
      rw [CurrentControl.selected_row, second_loop_weights]
      change ((controller.clear.learners.get action).credit _ _ _ false).val.state.weights = _
      rw [clear_credit]
      rfl
    · rw [CurrentControl.unselected_row _ _ _ _ _ selected]
      change ((controller.clear.learners.get row).credit _ _ _ false).val.state.weights = _
      rw [clear_credit]
      rfl
  · rw [values_step_accumulator]
    simp only [show controller.clear.restartPending = false from rfl]
    rw [clear_credit]
    exact CurrentRetirement.begin_accumulator_zero (controller.learners.get action).state features

/-- The executed begin/first-action composition retains every policy weight,
saves the drawn action's original machine prediction, and keeps a zero shared
accumulator. Model callbacks are confined to their separate storage. -/
theorem first_option_policy (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (rate : ConsumerRate) (reward : Binary32)
    (gain : RewardRate) (rng : Rng.Xoshiro256) :
    let begun := skill.beginTemporal models features potential true rate
    let result := begun.1.stepTemporal models begun.2.1 begun.2.2 reward gain rng
    (∀ row, (result.1.policy.learners.get row).state.weights =
      (skill.policy.learners.get row).state.weights) ∧
    result.1.policy.vOld = (skill.policy.predictAll features).get result.2.2.1.action ∧
    result.1.policy.vDelta = .zero := by
  simp only [Skill.beginTemporal, Skill.beginOption, Skill.stepTemporal,
    Skill.optionStep, OptionActivation.learning, if_true]
  simp only [Nat.lt_irrefl, decide_false, Bool.and_false, Bool.false_eq_true, if_false]
  dsimp only [Controller.policyStep]
  refine ⟨(clear_values_step _ _ _ _ _ _ _).1, ?_,
    (clear_values_step _ _ _ _ _ _ _).2⟩
  let drawn : PolicyDecision primitiveCount :=
    ((skill.policy.clear.snapshot (count := primitiveCount) features
      (rate.resolve fun _ =>
        skill.policy.clear.exploreRate (count := primitiveCount))).draw rng).1
  change
    (skill.policy.clear.predictAll features).get drawn.action =
      (skill.policy.predictAll features).get drawn.action
  simp [Controller.predictAll, Controller.clear, Vector.get, Fin.cast,
    Managed.apply, SwiftTd.Entry.apply, NumericState.linearPrediction,
    NumericState.clearTransient]

theorem neutral_terminal_error_nonnegative (estimate saved : Binary32)
    (finite : estimate.Finite) (savedFinite : saved.Finite)
    (ordered : CurrentArithmetic.numerical32 saved ≤ CurrentArithmetic.numerical32 estimate)
    (bound : |CurrentArithmetic.numerical32 estimate - CurrentArithmetic.numerical32 saved| ≤ 512) :
    0 ≤ CurrentArithmetic.numerical32
      (((Acorn.Features.terminalCumulant .zero
        ((Interest.learned (Assignment.neutral (config := config))).stoppingValue
          estimate false) false).sub saved).sub .zero) := by
  have stopping := CurrentRetirement.add_zero_numeric estimate finite
  have reward := CurrentRetirement.zero_add_numeric _ stopping.1
  have shaped := CurrentRetirement.sub_zero_numeric _ reward.1
  have difference := CurrentBackupBounds.binary32_rounded_sub _ saved shaped.1 savedFinite
    (by rw [shaped.2, reward.2, stopping.2]; exact bound)
  have error := CurrentRetirement.sub_zero_numeric _ difference.1
  simp only [Acorn.Features.terminalCumulant, Interest.stoppingValue,
    Assignment.stoppingValue, Assignment.bonus, Potential.value, Bool.false_eq_true,
    ↓reduceIte, show Binary32.zero.mul .zero = .zero from rfl]
  rw [error.2]
  exact CurrentBackupBounds.Rounded.mono CurrentBackupBounds.rounded_zero difference.2
    (by rw [shaped.2, reward.2, stopping.2]; exact sub_nonneg.mpr ordered)

/-- A primitive action row is always part of the complete receiving scan. -/
theorem control_reader_member (ensemble : Ensemble config criterion dimension demonLayout)
    (action : Action Acorn.FeatureConstants.primitiveCount) :
    (⟨criterion.config .control, ensemble.control.learners.get action⟩ : PackedLearner dimension) ∈
      ensemble.readers := by
  simp only [Ensemble.readers, List.mem_append]
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply List.mem_map.mpr
  exact ⟨_, by simp [Vector.get], rfl⟩

/-- One never-selected primitive row vetoes all units, including every alias of
their hashed slots; no assumption about the other readers is needed. -/
theorem cold_control_refuses
    (state : Lifecycle Host.patchShape config criterion dimension demonLayout)
    (action : Action Acorn.FeatureConstants.primitiveCount)
    (cold : (state.consumers.control.learners.get action).state =
      NumericState.initial (criterion.config .control) dimension) : state.tryRetire = none := by
  apply state.refusal_iff.mpr
  right
  apply List.find?_eq_none.mpr
  intro unit _
  have veto := cold_reader_veto _ cold (unitFeature dimension config unit)
  intro eligible
  have accepted := (state.consumers.negligible_iff _).mp eligible _
    (control_reader_member state.consumers action)
  change _ = true at accepted
  simp only [PackedLearner.negligible, veto, Bool.false_eq_true] at accepted

/-- The projection unaffected by selection: primitive storage and representation.
Common completion owns primitive learning; retirement owns bank replacement. -/
private def selectionStorage (state : TemporalControl profile config criterion dimension) :=
  (state.runtime.lifecycle.consumers.control, state.runtime.lifecycle.representation)

/-- Assignment installation never writes either part of the selection projection. -/
private theorem refresh_storage
    (state : FreeDispatch Host.patchShape config criterion dimension demonLayout.tail
      (EndingPayload (profile.mode != .frozen))) :
    (state.refreshRanked.lifecycle.consumers.control,
      state.refreshRanked.lifecycle.representation) =
      (state.lifecycle.consumers.control, state.lifecycle.representation) := by
  unfold FreeDispatch.refreshRanked
  dsimp only [Refresh.take]
  split
  · generalize rankAssignments dimension config
      state.lifecycle.consumers.demons.rankingWeights = targets
    have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
        (current : FreeDispatch Host.patchShape config criterion dimension demonLayout.tail
          (EndingPayload (profile.mode != .frozen))) :
        let result := slots.foldl (fun next slot => next.install slot targets[slot.val]) current
        (result.lifecycle.consumers.control, result.lifecycle.representation) =
          (current.lifecycle.consumers.control, current.lifecycle.representation) := by
      induction slots generalizing current with
      | nil => rfl
      | cons slot tail ih =>
        dsimp only [List.foldl_cons]
        rw [ih]
        rw [(current.install_preserves slot _).2.2, current.install_representation]
    exact fold _ _
  · rfl

/-- Gap, cache and meta-credit branches leave primitive storage and the bank alone. -/
private theorem skip_storage (state : TemporalControl profile config criterion dimension) :
    selectionStorage state.skipMeta = selectionStorage state := by
  unfold TemporalControl.skipMeta
  split <;> rfl

/-- Selection preparation changes no primitive learner or bank. -/
private theorem prepare_storage (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    selectionStorage (state.prepareSelection models features reward) = selectionStorage state := by
  unfold TemporalControl.prepareSelection
  dsimp only
  split <;> split <;> rfl

/-- Meta credit is isolated from primitive credit and representation. -/
private theorem meta_storage (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    selectionStorage (state.learnMeta features decision) = selectionStorage state := by
  unfold TemporalControl.learnMeta
  split <;> rfl

/-- Terminal option credit writes only the current option or a detached owner. -/
private theorem close_storage (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (closing : Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    selectionStorage (state.closeOption models closing reward terminal).1 =
      selectionStorage state := by
  unfold TemporalControl.closeOption
  dsimp only
  cases closing.oldOwner <;> rfl

/-- Refresh retains the projection even when all option assignments change. -/
private theorem free_storage (state : TemporalControl profile config criterion dimension)
    (closing : Option (Closing config criterion dimension
      (EndingPayload (profile.mode != .frozen)))) :
    selectionStorage (state.refreshFree closing).1 = selectionStorage state :=
  refresh_storage _

/-- A served exploratory run changes no primitive knowledge or representation. -/
private theorem serve_storage (state next : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision)
    (executed : state.serve features = some (next, decision)) :
    selectionStorage next = selectionStorage state := by
  unfold TemporalControl.serve at executed
  split at executed
  · rename_i run phase
    cases served : run.serve with
    | none => simp [served, bind, Option.bind] at executed
    | some pair =>
      simp only [served, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at executed
      rw [← executed.1]
      split <;> exact skip_storage _
  · contradiction
  · contradiction

/-- Dispatch learns meta and option state; common completion owns primitive credit. -/
private theorem dispatch_storage (state next : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (metaDecision : PolicyDecision metaCount)
    (ended : Option EndEvent) (decision : TemporalDecision)
    (executed : state.dispatchMeta models features declared reward metaDecision ended =
      some (next, decision)) :
    selectionStorage next = selectionStorage state := by
  unfold TemporalControl.dispatchMeta at executed
  dsimp only at executed
  split at executed
  · cases executed
    exact meta_storage state features metaDecision
  · rename_i slot selected
    cases potential :
        ((state.learnMeta features metaDecision).runtime.lifecycle.consumers.skills.get
          slot).interest.potential features declared with
    | none => simp [potential, bind, Option.bind] at executed
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at executed
      have nextEq := congrArg Prod.fst executed
      dsimp only at nextEq
      rw [← nextEq]
      exact meta_storage state features metaDecision

/-- Free dispatch preserves the projection across refresh, planning and terminal credit. -/
private theorem boundary_storage (state next : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (closing : Option (Closing config criterion dimension
      (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) (decision : TemporalDecision)
    (executed : state.atBoundary models plan features declared reward closing ended =
      some (next, decision)) :
    selectionStorage next = selectionStorage state := by
  unfold TemporalControl.atBoundary at executed
  dsimp only at executed
  split at executed
  · exact (dispatch_storage _ _ models features declared reward _ ended decision executed).trans
      (free_storage state closing)
  · rename_i owner closingEq
    exact (dispatch_storage _ _ models features declared reward _ _ decision executed).trans
      ((close_storage _ models owner reward _).trans (free_storage state closing))

/-- The actual selection dispatcher preserves primitive storage and representation
on every successful branch, for either criterion and any model/planning operations. -/
private theorem select_storage (state next : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (reward : Binary32) (goal : Bool) (decision : TemporalDecision)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision)) :
    selectionStorage next = selectionStorage state := by
  unfold TemporalControl.selectWithOperations at executed
  generalize preparedEq : state.prepareSelection models features reward = prepared at executed
  have preparedStorage : selectionStorage prepared = selectionStorage state := by
    rw [← preparedEq]
    exact prepare_storage state models features reward
  dsimp only at executed
  cases served : prepared.serve features with
  | some result =>
    simp only [served] at executed
    cases executed
    exact (serve_storage prepared next features decision served).trans preparedStorage
  | none =>
    simp only [served] at executed
    split at executed
    · cases executed
      exact preparedStorage
    · split at executed
      · exact (boundary_storage _ _ models plan features declared reward none none
          decision executed).trans preparedStorage
      · exact (boundary_storage _ _ models plan features declared reward none none
          decision executed).trans preparedStorage
      · rename_i slot activation phase
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential, bind, Option.bind] at executed
        | some value =>
          simp only [potential, bind, Option.bind] at executed
          split at executed
          · simp only [pure, Option.some.injEq, Prod.mk.injEq] at executed
            rw [← executed.1]
            exact (skip_storage _).trans preparedStorage
          · cases criterion with
            | discounted =>
              exact (boundary_storage _ _ models plan features declared reward none _
                decision executed).trans
                ((close_storage _ models _ reward _).trans preparedStorage)
            | differential =>
              exact (boundary_storage _ _ models plan features declared reward _ none
                decision executed).trans preparedStorage

/-- Each credit policy either skips primitive learning or uses the same Sarsa
row discipline. The theorem does not assume a fixed action-selection profile. -/
private theorem credit_cold (state : PrimitiveControl criterion dimension
      Acorn.FeatureConstants.primitiveCount)
    (features : SwiftTd.ActiveSet dimension)
    (action other : Action Acorn.FeatureConstants.primitiveCount) (own : Bool)
    (reward : Binary32) (different : other ≠ action)
    (cold : (state.controller.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension) :
    ((state.creditStep features action own reward).controller.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension := by
  cases credit : state.credit <;> cases own <;>
    simp only [PrimitiveControl.creditStep, credit, Bool.false_eq_true, ↓reduceIte,
      Controller.step, Controller.smdpStep]
  all_goals first | exact cold |
    exact CurrentControl.unselected_initial _ _ _ _ _ different cold _ _ _

/-- Common completion cannot expose a different action row. Frozen mode retains
it outright; learning modes use the same executed primitive action. -/
private theorem finish_cold (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observation : Host.Observation)
    (reward : Binary32) (decision : TemporalDecision)
    (other : Action Acorn.FeatureConstants.primitiveCount) (different : other ≠ decision.action)
    (cold : (state.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension) :
    let next := state.finish features observation reward decision
    (next.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension := by
  dsimp only
  rw [TemporalControl.finish_credit]
  unfold PredictionControl.advance
  split
  · exact cold
  · exact credit_cold state.predictionView.control features decision.action other decision.own
      reward different cold

/-- The concrete temporal step preserves a never-selected primitive row and
the representation; selection, credit and retirement are separate operations. -/
theorem step_cold (state next : TemporalControl profile config criterion dimension)
    (selection : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) (decision : TemporalDecision)
    (other : Action Acorn.FeatureConstants.primitiveCount) (different : other ≠ decision.action)
    (cold : (state.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension)
    (executed : state.step selection features observation reward goal = some (next, decision)) :
    (next.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension ∧
    next.runtime.lifecycle.representation = state.runtime.lifecycle.representation := by
  unfold TemporalControl.step at executed
  cases chosen : state.select selection features (spatialPotentials observation) reward goal with
  | none => simp [chosen, bind, Option.bind] at executed
  | some selected =>
    simp only [chosen, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at executed
    rcases executed with ⟨rfl, rfl⟩
    have kept := select_storage state selected.1 (modelOperations criterion dimension)
      (planningBoundary selection) features (spatialPotentials observation) reward goal
      selected.2 chosen
    have control := congrArg Prod.fst kept
    have representation := congrArg Prod.snd kept
    refine ⟨finish_cold selected.1 features observation reward selected.2 other different ?_,
      representation⟩
    change selected.1.runtime.lifecycle.consumers.control = _ at control
    rw [control]
    exact cold

/-- A cold row makes the full-agent retirement operation an identity. -/
theorem retire_cold (state : Agent profile config criterion dimension planning)
    (other : Action Acorn.FeatureConstants.primitiveCount)
    (cold : (state.control.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension) : state.retire = state := by
  have refused := cold_control_refuses state.control.runtime.lifecycle other cold
  unfold Agent.retire
  split
  · rfl
  · simp only [FeatureRuntime.retire, refused]

/-- A real full-agent action that omits a cold primitive row leaves that row
cold and records no replacement. The encoder and policy draw are the executed
ones; no feature set, internal learner state or chosen action is injected. -/
theorem act_cold (state : Agent profile config criterion dimension planning)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool)
    (other : Action Acorn.FeatureConstants.primitiveCount)
    (different : other ≠ (state.act observation reward goal).2.action)
    (cold : (state.control.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension) :
    let next := (state.act observation reward goal).1
    (next.control.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension ∧
    next.control.runtime.lifecycle.representation.progress.events =
      state.control.runtime.lifecycle.representation.progress.events := by
  obtain ⟨next, aligned, episodes, executed, actual⟩ := state.act_execution observation reward goal
  have kept := step_cold state.advanceClock.control next planning
    (state.advanceClock.frame observation).active observation reward goal _ other different cold
    executed
  dsimp only
  rw [actual, retire_cold _ other kept.1]
  exact ⟨kept.1, congrArg (fun representation => representation.progress.events) kept.2⟩

/-- A later unit sharing an earlier hashed slot can never be the first candidate,
for any receiver state. This is an identity obstruction, independent of learning. -/
theorem candidate_alias_minimal {shape : PatchShape} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts)
    (unit prior : Fin config.units.count) (selected : state.candidate = some unit)
    (sameSlot : unitFeature dimension config prior = unitFeature dimension config unit) :
    unit.val ≤ prior.val := by
  obtain ⟨eligible, i, valid, same, earlier⟩ := List.find?_eq_some_iff_getElem.mp selected
  have index : i = unit.val := by simpa using congrArg Fin.val same
  by_contra order
  have before : prior.val < i := by omega
  have veto := earlier prior.val before
  simp [List.getElem_finRange, sameSlot, eligible] at veto

/-- Proof-layer observation of an action prefix. Every transition calls `Agent.act`;
the action list is not stored by the agent and does not supply its policy choices. -/
def decisionPrefix (state : Agent profile config criterion dimension planning) :
    List (Host.Observation × Host.RawStepResult) →
      Agent profile config criterion dimension planning ×
        List (Action Acorn.FeatureConstants.primitiveCount)
  | [] => (state, [])
  | (observation, result) :: rest =>
    let next := state.act observation result.reward result.events.done
    let tail := decisionPrefix next.1 rest
    (tail.1, next.2.action :: tail.2)

/-- The observed fold is exactly the existing public prefix execution on action
inputs. This correspondence rules out a parallel assumed-equivalent learner. -/
theorem decisionPrefix_execution (state : Agent profile config criterion dimension planning)
    (inputs : List (Host.Observation × Host.RawStepResult)) :
    state.runPrefix (inputs.map fun input => AgentInput.act input.1 input.2) =
      .ok ((decisionPrefix state inputs).1, false) := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input rest ih =>
    change ((state.act input.1 input.2.reward input.2.events.done).1.runPrefix
      (rest.map fun input => AgentInput.act input.1 input.2)) = _
    exact ih _

/-- Exactly one primitive choice is observed for every actual action input. -/
theorem decisionPrefix_length (state : Agent profile config criterion dimension planning)
    (inputs : List (Host.Observation × Host.RawStepResult)) :
    (decisionPrefix state inputs).2.length = inputs.length := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input rest ih =>
    change (decisionPrefix (state.act input.1 input.2.reward input.2.events.done).1 rest).2.length +
      1 = rest.length + 1
    rw [ih]

/-- Over every actual finite action prefix, a row never selected since cold
initialization remains cold and prevents every recorded replacement. No reward,
feature-exposure, ranking, policy-fairness or arithmetic-sign assumption is used. -/
theorem prefix_cold (state : Agent profile config criterion dimension planning)
    (inputs : List (Host.Observation × Host.RawStepResult))
    (other : Action Acorn.FeatureConstants.primitiveCount)
    (omitted : other ∉ (decisionPrefix state inputs).2)
    (cold : (state.control.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension) :
    let next := (decisionPrefix state inputs).1
    (next.control.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension ∧
    next.control.runtime.lifecycle.representation.progress.events =
      state.control.runtime.lifecycle.representation.progress.events := by
  induction inputs generalizing state with
  | nil => exact ⟨cold, rfl⟩
  | cons input rest ih =>
    have different : other ≠ (state.act input.1 input.2.reward input.2.events.done).2.action :=
      fun same => omitted (List.mem_cons.mpr (Or.inl same))
    have tailOmitted : other ∉
        (decisionPrefix (state.act input.1 input.2.reward input.2.events.done).1 rest).2 :=
      fun member => omitted (List.mem_cons_of_mem _ member)
    have one := act_cold state input.1 input.2.reward input.2.events.done other different cold
    have tail := ih (state.act input.1 input.2.reward input.2.events.done).1 tailOmitted one.1
    exact ⟨tail.1, tail.2.trans one.2⟩

/-- An actual prefix's final history is empty whenever one primitive action
has not been selected. Cold initialization, not checkpoint admission, is the base. -/
theorem initialized_prefix_refuses (inputs : List (Host.Observation × Host.RawStepResult))
    (other : Action Acorn.FeatureConstants.primitiveCount)
    (omitted : other ∉ (decisionPrefix
      (Agent.initial profile config criterion dimension planning) inputs).2) :
    let finalState := (decisionPrefix
      (Agent.initial profile config criterion dimension planning) inputs).1
    finalState.control.runtime.lifecycle.representation.progress.events = [] := by
  exact (prefix_cold _ inputs other omitted (by
    simp [Agent.initial, TemporalControl.initial, Ensemble.initial, Controller.initial,
      Managed.initial, Vector.get])).2

/-- Non-vacuity is structural: fewer decisions than primitive actions cannot
expose every row, for every observation/result prefix and initial configuration.
This counts actual returned actions, not a simulated or chosen stream. -/
theorem short_prefix_omits (state : Agent profile config criterion dimension planning)
    (inputs : List (Host.Observation × Host.RawStepResult))
    (short : inputs.length < Acorn.FeatureConstants.primitiveCount) :
    ∃ other : Action Acorn.FeatureConstants.primitiveCount,
      other ∉ (decisionPrefix state inputs).2 := by
  by_contra! covered
  have subset : List.finRange Acorn.FeatureConstants.primitiveCount ⊆
      (decisionPrefix state inputs).2 := by
    intro action _
    exact covered action
  have bound :=
    (List.nodup_finRange Acorn.FeatureConstants.primitiveCount).length_le_of_subset subset
  rw [List.length_finRange, decisionPrefix_length] at bound
  omega

/-- Every cold action prefix shorter than the primitive-action count records
zero replacements. With nine primitive actions, this includes the first eight
decisions of every stream, regardless of any other learner's behavior. -/
theorem short_prefix_refuses (inputs : List (Host.Observation × Host.RawStepResult))
    (short : inputs.length < Acorn.FeatureConstants.primitiveCount) :
    let finalState := (decisionPrefix
      (Agent.initial profile config criterion dimension planning) inputs).1
    finalState.control.runtime.lifecycle.representation.progress.events = [] := by
  obtain ⟨other, omitted⟩ := short_prefix_omits
    (Agent.initial profile config criterion dimension planning) inputs short
  exact initialized_prefix_refuses inputs other omitted

/-- Existence of some complete-reader candidate is exactly non-refusal of the
bank-order search. It asserts existence, not fairness for a specified unit. -/
theorem candidate_exists {shape : PatchShape} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) :
    state.candidate ≠ none ↔ ∃ unit, state.consumers.negligible
      (unitFeature dimension config unit) = true := by
  constructor
  · intro present
    cases found : state.candidate with
    | none => exact False.elim (present found)
    | some unit => exact ⟨unit, (state.candidate_first unit found).1⟩
  · rintro ⟨unit, eligible⟩ absent
    have veto := List.find?_eq_none.mp absent unit (List.mem_finRange unit)
    exact veto eligible

/-- The complete local enabling condition combines receiver-bound eligibility
with capacity and strict clock order. No future-learning premise is hidden here. -/
theorem retirement_enabled_iff {shape : PatchShape} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) :
    state.tryRetire ≠ none ↔ state.representation.progress.CanRecord ∧
      ∃ unit, ∀ reader ∈ state.consumers.readers,
        reader.negligible (unitFeature dimension config unit) = true := by
  simp only [ne_eq, state.refusal_iff, not_or, not_not]
  have existsCandidate := candidate_exists state
  simp only [ne_eq] at existsCandidate
  rw [existsCandidate]
  simp only [Ensemble.negligible_iff]

/-- Receiver-owned retirement adds precisely one event on success and none on
refusal. The count is of events, so repeatedly replacing one unit spends quota. -/
theorem runtime_retirement_count {shape : PatchShape} {discounts : List Discount}
    {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts
      activation exploration decision) :
    state.retire.lifecycle.representation.progress.events.length =
      state.lifecycle.representation.progress.events.length +
        (if state.lifecycle.tryRetire.isSome then 1 else 0) := by
  unfold FeatureRuntime.retire
  cases attempted : state.lifecycle.tryRetire with
  | none => simp
  | some result =>
    rcases result with ⟨unit, next⟩
    obtain ⟨room, eligible, _, rfl⟩ := (state.lifecycle.success_iff unit next).mp attempted
    exact record_count _ unit room

/-- At the full-agent retirement boundary, a recorded event is equivalent to
learning mode and the complete local enabling condition. This is immediate
selection conditional on the current state, not eventual floor learning. -/
theorem agent_retirement_count (state : Agent profile config criterion dimension planning) :
    historyCount state.retire = historyCount state +
        (if profile.mode == .frozen then 0 else
          if state.control.runtime.lifecycle.tryRetire.isSome then 1 else 0) := by
  unfold Agent.retire
  split
  · simp
  · exact runtime_retirement_count _

/-- Temporal learning and observation never spend or replenish history. The
retirement transaction is the only event writer in an action call. -/
theorem step_representation (state next : TemporalControl profile config criterion dimension)
    (selection : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) (decision : TemporalDecision)
    (executed : state.step selection features observation reward goal = some (next, decision)) :
    next.runtime.lifecycle.representation = state.runtime.lifecycle.representation := by
  unfold TemporalControl.step at executed
  cases chosen : state.select selection features (spatialPotentials observation) reward goal with
  | none => simp [chosen, bind, Option.bind] at executed
  | some selected =>
    simp only [chosen, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at executed
    rcases executed with ⟨rfl, rfl⟩
    exact congrArg Prod.snd (select_storage state selected.1 (modelOperations criterion dimension)
      (planningBoundary selection) features (spatialPotentials observation) reward goal
      selected.2 chosen)

/-- One actual action has a zero-or-one increment, bounded by remaining lifetime
quota. A saturated clock may refuse even when this arithmetic bound has room. -/
theorem act_history_count (state : Agent profile config criterion dimension planning)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) :
    ∃ added : Nat, added ≤ 1 ∧
      historyCount (state.act observation reward goal).1 = historyCount state + added ∧
      added ≤ config.units.count - historyCount state := by
  obtain ⟨next, aligned, episodes, executed, actual⟩ := state.act_execution observation reward goal
  have kept := step_representation state.advanceClock.control next planning
    (state.advanceClock.frame observation).active observation reward goal _ executed
  let prepared : Agent profile config criterion dimension planning := ⟨next, aligned, episodes⟩
  have count := agent_retirement_count prepared
  have before : historyCount prepared = historyCount state :=
    congrArg (fun representation => representation.progress.events.length) kept
  rw [actual]
  let added := if profile.mode == .frozen then 0 else
    if next.runtime.lifecycle.tryRetire.isSome then 1 else 0
  have small : added ≤ 1 := by dsimp only [added]; split <;> (first | omega | (split <;> omega))
  have after := prepared.retire.control.runtime.lifecycle.representation.progress.legal.1
  refine ⟨added, small, ?_, ?_⟩
  · exact count.trans (congrArg (· + added) before)
  · change historyCount prepared.retire ≤ config.units.count at after
    rw [count, before] at after
    change historyCount state + added ≤ config.units.count at after
    omega

/-- A public input omits the designated primitive action. Environment/attempt
accounting and stop are allowed; clear and restore are excluded because they
start or admit knowledge with a different exposure history. -/
def inputOmits (state : Agent profile config criterion dimension planning)
    (event : AgentInput config criterion dimension)
    (other : Action Acorn.FeatureConstants.primitiveCount) : Prop :=
  match event with
  | .act observation result =>
    other ≠ (state.act observation result.reward result.events.done).2.action
  | .environment .. | .attempt .. | .stop => True
  | .clear | .restore .. => False

/-- The omission condition is imposed on every consumed edge of the existing
executed path. An ignored suffix after stop has no exposure requirement. -/
inductive PathOmits (other : Action Acorn.FeatureConstants.primitiveCount) :
    {before after : Agent profile config criterion dimension planning} →
    {events : List (AgentInput config criterion dimension)} → {stopped : Bool} →
    AgentPath before events after stopped → Prop where
  /-- No edge selects an action in an empty prefix. -/
  | nil (state : Agent profile config criterion dimension planning) : PathOmits other (.nil state)
  /-- Stop accounts only for its consumed input. -/
  | stopped (before after : Agent profile config criterion dimension planning)
      (event : AgentInput config criterion dimension)
      (rest : List (AgentInput config criterion dimension))
      (executed : before.input event = .ok (after, true))
      (omitted : inputOmits before event other) :
      PathOmits other (.stopped before after event rest executed)
  /-- A continuing edge and its actual suffix both omit this action. -/
  | continued (before next after : Agent profile config criterion dimension planning)
      (event : AgentInput config criterion dimension)
      (rest : List (AgentInput config criterion dimension)) (stopped : Bool)
      (executed : before.input event = .ok (next, false))
      (tail : AgentPath next rest after stopped) (omitted : inputOmits before event other)
      (remaining : PathOmits other tail) :
      PathOmits other (.continued before next after event rest stopped executed tail)

/-- Every consumed ordinary input preserves a cold omitted row and its history.
In particular, attempt-triggered ranking requests are allowed in this result. -/
theorem input_cold (before after : Agent profile config criterion dimension planning)
    (event : AgentInput config criterion dimension) (stopped : Bool)
    (executed : before.input event = .ok (after, stopped))
    (other : Action Acorn.FeatureConstants.primitiveCount) (omitted : inputOmits before event other)
    (cold : (before.control.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension) :
    (after.control.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension ∧
    after.control.runtime.lifecycle.representation.progress.events =
      before.control.runtime.lifecycle.representation.progress.events := by
  cases event with
  | act observation result =>
    cases executed
    exact act_cold before observation result.reward result.events.done other omitted cold
  | environment family reward => cases executed; exact ⟨cold, rfl⟩
  | attempt family cycle steps achieved => cases executed; exact ⟨cold, rfl⟩
  | stop => cases executed; exact ⟨cold, rfl⟩
  | clear => exact False.elim omitted
  | restore image => exact False.elim omitted

/-- Actual public finite paths, including arbitrary environment accounting,
attempt requests and stop, cannot replace while a cold primitive row is omitted.
The relation is `AgentPath`, already linked to `Agent.runPrefix` and native execution. -/
theorem path_cold {before after : Agent profile config criterion dimension planning}
    {events : List (AgentInput config criterion dimension)} {stopped : Bool}
    (path : AgentPath before events after stopped)
    (other : Action Acorn.FeatureConstants.primitiveCount) (omitted : PathOmits other path)
    (cold : (before.control.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension) :
    (after.control.runtime.lifecycle.consumers.control.learners.get other).state =
      NumericState.initial (criterion.config .control) dimension ∧
    after.control.runtime.lifecycle.representation.progress.events =
      before.control.runtime.lifecycle.representation.progress.events := by
  induction omitted with
  | nil state => exact ⟨cold, rfl⟩
  | stopped state next event rest executed omitted =>
    exact input_cold state next event true executed other omitted cold
  | continued state next finalState event rest stopped executed tail omitted remaining ih =>
    have one := input_cold state next event false executed other omitted cold
    have remaining := ih one.1
    exact ⟨remaining.1, remaining.2.trans one.2⟩

/-- The admitted input-path result starts from actual cold construction. This
includes attempt events that request assignment refresh, not just action lists. -/
theorem initialized_path_refuses {after : Agent profile config criterion dimension planning}
    {events : List (AgentInput config criterion dimension)} {stopped : Bool}
    (path : AgentPath (Agent.initial profile config criterion dimension planning)
      events after stopped)
    (other : Action Acorn.FeatureConstants.primitiveCount) (omitted : PathOmits other path) :
    after.control.runtime.lifecycle.representation.progress.events = [] := by
  exact (path_cold path other omitted (by
    simp [Agent.initial, TemporalControl.initial, Ensemble.initial, Controller.initial,
      Managed.initial, Vector.get])).2

/-- Pending ranking changes two distinct complete objective identities. The
comparison reads the actual receiving Demon-0 weights, including bonus bits. -/
def TwoRefreshChanges (state : TemporalControl profile config .discounted dimension) : Prop :=
  state.runtime.refresh.pending = true ∧
  ∃ left right : Fin Acorn.FeatureConstants.skillCount,
    left ≠ right ∧
    (state.runtime.lifecycle.consumers.skills.get left).interest.sameAssignment
      ((rankAssignments dimension config
        state.runtime.lifecycle.consumers.demons.rankingWeights).get left) = false ∧
    (state.runtime.lifecycle.consumers.skills.get right).interest.sameAssignment
      ((rankAssignments dimension config
        state.runtime.lifecycle.consumers.demons.rankingWeights).get right) = false

private theorem install_fold_other
    {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (other : Fin Acorn.FeatureConstants.skillCount) (absent : other ∉ slots) :
    ((slots.foldl (fun current slot => current.install slot (targets.get slot))
      state).lifecycle.consumers.skills.get other) =
      state.lifecycle.consumers.skills.get other := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot tail ih =>
    have different : other ≠ slot := fun same => absent (by simp [same])
    have missing : other ∉ tail := fun member => absent (List.mem_cons_of_mem _ member)
    dsimp only [List.foldl_cons]
    rw [ih _ missing]
    exact (state.install_other slot other (targets.get slot) different).1

private theorem install_fold_changed
    {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (unique : slots.Nodup) (member : slot ∈ slots)
    (changed : (state.lifecycle.consumers.skills.get slot).interest.sameAssignment
      (targets.get slot) = false) :
    ((slots.foldl (fun current index => current.install index (targets.get index))
      state).lifecycle.consumers.skills.get slot) =
      Skill.initial config criterion dimension (.learned (targets.get slot)) := by
  induction slots generalizing state with
  | nil => simp at member
  | cons head tail ih =>
    obtain ⟨missing, distinct⟩ := List.nodup_cons.mp unique
    dsimp only [List.foldl_cons]
    rcases List.mem_cons.mp member with same | member
    · subst head
      rw [install_fold_other _ tail targets slot missing]
      change state.lifecycle.consumers.skills[slot.val].interest.sameAssignment
        targets[slot.val] = false at changed
      change (state.install slot targets[slot.val]).lifecycle.consumers.skills[slot.val] = _
      simp only [FreeDispatch.install, changed, Bool.false_eq_true, ↓reduceIte,
        Vector.getElem_set_self]
      rfl
    · have different : slot ≠ head := fun same => missing (same ▸ member)
      apply ih _ distinct member
      have kept : (state.install head (targets.get head)).lifecycle.consumers.skills.get slot =
          state.lifecycle.consumers.skills.get slot :=
        (state.install_other head slot (targets.get head) different).1
      rw [kept]
      exact changed

private theorem refresh_changed_model
    {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (pending : state.refresh.pending = true)
    (changed : (state.lifecycle.consumers.skills.get slot).interest.sameAssignment
      ((rankAssignments dimension config
        state.lifecycle.consumers.demons.rankingWeights).get slot) = false) :
    (state.refreshRanked.lifecycle.consumers.skills.get slot).model =
      Model.initial dimension criterion := by
  unfold FreeDispatch.refreshRanked
  dsimp only [Refresh.take]
  rw [pending]
  have fresh := install_fold_changed
    { state with refresh := { state.refresh with pending := false } }
    (List.finRange Acorn.FeatureConstants.skillCount)
    (rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights)
    slot (List.nodup_finRange _) (List.mem_finRange slot) changed
  exact congrArg Skill.model fresh

private theorem refresh_closing_none
    {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (empty : state.closing = none) : state.refreshRanked.closing = none := by
  unfold FreeDispatch.refreshRanked
  dsimp only [Refresh.take]
  split
  · generalize rankAssignments dimension config
      state.lifecycle.consumers.demons.rankingWeights = targets
    have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
        (current : FreeDispatch shape config criterion dimension discounts payload)
        (empty : current.closing = none) :
        (slots.foldl (fun next slot => next.install slot targets[slot.val]) current).closing =
          none := by
      induction slots generalizing current with
      | nil => exact empty
      | cons slot tail ih =>
        dsimp only [List.foldl_cons]
        apply ih
        unfold FreeDispatch.install
        dsimp only
        split <;> simp [empty]
    exact fold _ _ empty
  · exact empty

private theorem withSkill_other_skill
    (state : TemporalControl profile config criterion dimension)
    (slot other : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill config criterion dimension) (different : other ≠ slot) :
    (state.withSkill slot skill).runtime.lifecycle.consumers.skills.get other =
      state.runtime.lifecycle.consumers.skills.get other := by
  have values : slot.val ≠ other.val := fun same => different (Fin.ext same.symm)
  change (state.runtime.lifecycle.consumers.skills.set slot.val skill slot.isLt)[other.val] = _
  rw [Vector.getElem_set]
  simp only [values, if_false]
  rfl

private theorem stepOption_other_skill
    (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation dimension activation) (reward : Binary32)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool)
    (ended : Option EndEvent) (other : Fin Acorn.FeatureConstants.skillCount)
    (different : other ≠ slot) :
    let result := state.stepOption models slot activation next reward metaValues metaDecision
      started ended
    result.1.runtime.lifecycle.consumers.skills.get other =
      state.runtime.lifecycle.consumers.skills.get other := by
  unfold TemporalControl.stepOption
  dsimp only
  exact withSkill_other_skill state slot other _ different

private theorem dispatch_other_skill
    (state next : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (reward : Binary32) (metaDecision : PolicyDecision metaCount)
    (ended : Option EndEvent) (decision : TemporalDecision)
    (other : Fin Acorn.FeatureConstants.skillCount)
    (omitted : skillOfMeta metaDecision.action ≠ some other)
    (executed : state.dispatchMeta models features declared reward metaDecision ended =
      some (next, decision)) :
    next.runtime.lifecycle.consumers.skills.get other =
      state.runtime.lifecycle.consumers.skills.get other := by
  have credited : (state.learnMeta features metaDecision).runtime.lifecycle.consumers.skills =
      state.runtime.lifecycle.consumers.skills := by
    unfold TemporalControl.learnMeta
    split <;> rfl
  unfold TemporalControl.dispatchMeta at executed
  dsimp only at executed
  cases selected : skillOfMeta metaDecision.action with
  | none =>
    simp only [selected, pure, Option.some.injEq] at executed
    have same := congrArg Prod.fst executed
    dsimp only at same
    rw [← same]
    exact congrArg (fun skills => skills.get other) credited
  | some slot =>
    have different : other ≠ slot := by
      intro same
      exact omitted (same ▸ selected)
    simp only [selected, bind, Option.bind] at executed
    cases potential : Interest.potential
        (Vector.get (state.learnMeta features metaDecision).runtime.lifecycle.consumers.skills
          slot).interest features declared with
    | none => simp [potential] at executed
    | some value =>
      simp only [potential, pure, Option.some.injEq] at executed
      have same := congrArg Prod.fst executed
      dsimp only at same
      rw [← same]
      rw [stepOption_other_skill (different := different),
        withSkill_other_skill (different := different)]
      exact congrArg (fun skills => skills.get other) credited

private theorem boundary_two_refresh_cold
    (state next : TemporalControl profile config .discounted dimension)
    (models : OptionModelOps .discounted dimension)
    (plan : PlanBoundary config .discounted dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (reward : Binary32) (ended : Option EndEvent) (decision : TemporalDecision)
    (changed : TwoRefreshChanges state)
    (executed : state.atBoundary models plan features declared reward none ended =
      some (next, decision)) :
    ∃ slot : Fin Acorn.FeatureConstants.skillCount,
      (next.runtime.lifecycle.consumers.skills.get slot).model =
        Model.initial dimension .discounted := by
  obtain ⟨pending, left, right, different, changedLeft, changedRight⟩ := changed
  let free : FreeDispatch Host.patchShape config .discounted dimension demonLayout.tail
      (EndingPayload (profile.mode != .frozen)) :=
    ⟨state.runtime.lifecycle, state.runtime.refresh,
      state.runtime.references.modelPredictions, none⟩
  have empty : (state.refreshFree none).2 = none := by
    change free.refreshRanked.closing = none
    exact refresh_closing_none (config := config) (criterion := .discounted)
      (dimension := dimension) (shape := Host.patchShape) (discounts := demonLayout.tail)
      (payload := EndingPayload (profile.mode != .frozen)) (state := free) rfl
  have freePending : free.refresh.pending = true := pending
  have freeLeft : (free.lifecycle.consumers.skills.get left).interest.sameAssignment
      ((rankAssignments dimension config free.lifecycle.consumers.demons.rankingWeights).get
        left) = false := changedLeft
  have freeRight : (free.lifecycle.consumers.skills.get right).interest.sameAssignment
      ((rankAssignments dimension config free.lifecycle.consumers.demons.rankingWeights).get
        right) = false := changedRight
  have leftCold := refresh_changed_model (config := config) (criterion := .discounted)
    (dimension := dimension) (shape := Host.patchShape) (discounts := demonLayout.tail)
    (payload := EndingPayload (profile.mode != .frozen)) (state := free)
    left freePending freeLeft
  have rightCold := refresh_changed_model (config := config) (criterion := .discounted)
    (dimension := dimension) (shape := Host.patchShape) (discounts := demonLayout.tail)
    (payload := EndingPayload (profile.mode != .frozen)) (state := free)
    right freePending freeRight
  let drawn := ((state.refreshFree none).1.planFree plan features).drawMeta features
  have skills : drawn.1.runtime.lifecycle.consumers.skills =
      free.refreshRanked.lifecycle.consumers.skills := rfl
  obtain ⟨slot, cold, omitted⟩ : ∃ slot : Fin Acorn.FeatureConstants.skillCount,
      (drawn.1.runtime.lifecycle.consumers.skills.get slot).model =
        Model.initial dimension .discounted ∧
      skillOfMeta drawn.2.action ≠ some slot := by
    by_cases chosen : skillOfMeta drawn.2.action = some left
    · refine ⟨right, ?_, ?_⟩
      · rw [skills]; exact rightCold
      · intro both
        exact different (Option.some.inj (chosen.symm.trans both))
    · refine ⟨left, ?_, chosen⟩
      rw [skills]; exact leftCold
  unfold TemporalControl.atBoundary at executed
  dsimp only at executed
  rw [empty] at executed
  have kept := dispatch_other_skill drawn.1 next models features declared reward drawn.2
    ended decision slot omitted executed
  exact ⟨slot, (congrArg Skill.model kept).trans cold⟩


private theorem prepare_two_changes
    (state : TemporalControl profile config .discounted dimension)
    (models : OptionModelOps .discounted dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (changed : TwoRefreshChanges state) :
    TwoRefreshChanges (state.prepareSelection models features reward) := by
  unfold TemporalControl.prepareSelection
  dsimp only
  split <;> split <;> exact changed

private theorem close_two_changes
    (state : TemporalControl profile config .discounted dimension)
    (models : OptionModelOps .discounted dimension)
    (closing : Closing config .discounted dimension (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) (changed : TwoRefreshChanges state) :
    TwoRefreshChanges (state.closeOption models closing reward terminal).1 := by
  have interests (slot : Fin Acorn.FeatureConstants.skillCount) :
      ((state.closeOption models closing reward terminal).1.runtime.lifecycle.consumers.skills.get
        slot).interest = (state.runtime.lifecycle.consumers.skills.get slot).interest := by
    unfold TemporalControl.closeOption
    dsimp only
    cases owner : closing.oldOwner with
    | some skill => rfl
    | none =>
      dsimp only [Option.getD]
      by_cases same : slot = closing.slot
      · subst slot
        change ((state.runtime.lifecycle.consumers.skills.set closing.slot.val _
          closing.slot.isLt)[closing.slot.val]).interest = _
        rw [Vector.getElem_set_self]
        unfold Skill.endTemporal
        split <;> exact (Skill.terminal_owners _ _ _ _ _ _).1
      · exact congrArg Skill.interest (withSkill_other_skill state closing.slot slot _ same)
  have pending : (state.closeOption models closing reward terminal).1.runtime.refresh =
      state.runtime.refresh := by
    unfold TemporalControl.closeOption
    dsimp only
    cases closing.oldOwner <;> rfl
  have demons :
      (state.closeOption models closing reward terminal).1.runtime.lifecycle.consumers.demons =
        state.runtime.lifecycle.consumers.demons := by
    unfold TemporalControl.closeOption
    dsimp only
    cases closing.oldOwner <;> rfl
  obtain ⟨requested, left, right, different, leftChanged, rightChanged⟩ := changed
  refine ⟨?_, left, right, different, ?_, ?_⟩
  · rw [pending]; exact requested
  · rw [interests, demons]; exact leftChanged
  · rw [interests, demons]; exact rightChanged

private theorem serve_no_meta (state next : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision)
    (executed : state.serve features = some (next, decision)) : decision.metaDecision = none := by
  unfold TemporalControl.serve at executed
  split at executed
  · rename_i run phase
    cases served : run.serve with
    | none => simp [served, bind, Option.bind] at executed
    | some pair =>
      simp only [served, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at executed
      rw [← executed.2]
  · contradiction
  · contradiction

private theorem select_two_refresh_cold
    (state next : TemporalControl profile config .discounted dimension)
    (models : OptionModelOps .discounted dimension)
    (plan : PlanBoundary config .discounted dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (reward : Binary32) (goal : Bool) (decision : TemporalDecision)
    (changed : TwoRefreshChanges state) (boundary : decision.metaDecision.isSome = true)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision)) :
    ∃ slot : Fin Acorn.FeatureConstants.skillCount,
      (next.runtime.lifecycle.consumers.skills.get slot).model =
        Model.initial dimension .discounted := by
  unfold TemporalControl.selectWithOperations at executed
  generalize preparedEq : state.prepareSelection models features reward = prepared at executed
  have preparedChanged : TwoRefreshChanges prepared := by
    rw [← preparedEq]
    exact prepare_two_changes state models features reward changed
  have idleChanged : TwoRefreshChanges (prepared.withPhase .idle) := preparedChanged
  dsimp only at executed
  cases served : prepared.serve features with
  | some result =>
    simp only [served] at executed
    cases executed
    rw [serve_no_meta prepared next features decision served] at boundary
    contradiction
  | none =>
    simp only [served] at executed
    split at executed
    · cases executed
      contradiction
    · split at executed
      · exact boundary_two_refresh_cold (prepared.withPhase .idle) next models plan features
          declared reward none decision idleChanged executed
      · exact boundary_two_refresh_cold (prepared.withPhase .idle) next models plan features
          declared reward none decision idleChanged executed
      · rename_i slot activation phase
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential, bind, Option.bind] at executed
        | some value =>
          simp only [potential, bind, Option.bind] at executed
          split at executed
          · simp only [pure, Option.some.injEq, Prod.mk.injEq] at executed
            rw [← executed.2] at boundary
            contradiction
          · refine boundary_two_refresh_cold _ next models plan features declared reward _
              decision ?_ executed
            exact close_two_changes (prepared.withPhase .idle) models _ reward _ idleChanged

/-- A free discounted dispatch that changes two assignments leaves at least one
fresh model untouched through common credit. Selection uses the actual policy draw. -/
theorem step_two_refresh_cold (state next : TemporalControl profile config .discounted dimension)
    (selection : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) (decision : TemporalDecision)
    (changed : TwoRefreshChanges state) (boundary : decision.metaDecision.isSome = true)
    (executed : state.step selection features observation reward goal = some (next, decision)) :
    (∃ slot : Fin Acorn.FeatureConstants.skillCount,
      (next.runtime.lifecycle.consumers.skills.get slot).model =
        Model.initial dimension .discounted) ∧
    next.runtime.lifecycle.representation = state.runtime.lifecycle.representation := by
  unfold TemporalControl.step at executed
  cases chosen : state.select selection features (spatialPotentials observation) reward goal with
  | none => simp [chosen, bind, Option.bind] at executed
  | some selected =>
    simp only [chosen, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at executed
    rcases executed with ⟨rfl, rfl⟩
    obtain ⟨slot, cold⟩ := select_two_refresh_cold state selected.1
      (modelOperations .discounted dimension) (planningBoundary selection) features
      (spatialPotentials observation) reward goal selected.2 changed boundary chosen
    have storage := select_storage state selected.1 (modelOperations .discounted dimension)
      (planningBoundary selection) features (spatialPotentials observation) reward goal
      selected.2 chosen
    refine ⟨⟨slot, ?_⟩, congrArg Prod.snd storage⟩
    rw [TemporalControl.finish_eq]
    exact cold

/-- A fresh stored skill model rejects every bank unit before the transaction,
including aliases. Capacity and clock admission cannot override this veto. -/
theorem cold_model_refuses
    (state : Lifecycle Host.patchShape config criterion dimension demonLayout)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (cold : (state.consumers.skills.get slot).model = Model.initial dimension criterion) :
    state.tryRetire = none := by
  apply state.refusal_iff.mpr
  right
  apply List.find?_eq_none.mpr
  intro unit _
  rw [cold_model_veto state.consumers slot cold]
  exact Bool.false_ne_true

/-- A pre-retirement cold model makes the full-agent retirement operation an identity. -/
theorem retire_cold_model (state : Agent profile config criterion dimension planning)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (cold : (state.control.runtime.lifecycle.consumers.skills.get slot).model =
      Model.initial dimension criterion) : state.retire = state := by
  have refused := cold_model_refuses state.control.runtime.lifecycle slot cold
  unfold Agent.retire
  split
  · rfl
  · simp only [FeatureRuntime.retire, refused]

/-- Two actual assignment changes at a discounted free boundary force refusal of
that callback's retirement scan. The cold reader is derived before retirement;
no feature encoding, action choice, or eligibility hypothesis is supplied. This
conditional obstruction does not establish that initialized executions meet its premise. -/
theorem act_two_refresh_changes (state : Agent profile config .discounted dimension planning)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool)
    (changed : TwoRefreshChanges state.control)
    (boundary : (state.act observation reward goal).2.metaDecision.isSome = true) :
    let next := (state.act observation reward goal).1
    (∀ feature, next.control.runtime.lifecycle.consumers.negligible feature = false) ∧
    next.control.runtime.lifecycle.representation.progress.events =
      state.control.runtime.lifecycle.representation.progress.events := by
  obtain ⟨next, aligned, episodes, executed, actual⟩ := state.act_execution observation reward goal
  have kept := step_two_refresh_cold state.advanceClock.control next planning
    (state.advanceClock.frame observation).active observation reward goal _ changed boundary
    executed
  obtain ⟨slot, cold⟩ := kept.1
  dsimp only
  rw [actual, retire_cold_model _ slot cold]
  exact ⟨cold_model_veto _ slot cold,
    congrArg (fun representation => representation.progress.events) kept.2⟩

open AcornVerif.CurrentRetirement

/-- Zero weight/update-lag sector of the actual discounted continuation learner.
The reward model, policy, beta and other transient registers are unrestricted. -/
def ZeroContinuation (model : Model dimension .discounted) : Prop :=
  match model with | .discounted _ continuation => ZeroKnowledge continuation.state

/-- The discounted model constructor initializes its continuation sector. -/
theorem zero_continuation_initial : ZeroContinuation (Model.initial dimension .discounted) :=
  zero_initial

/-- Starting actual model traces preserves the zero continuation sector. -/
theorem zero_continuation_begin (model : Model dimension .discounted)
    (hz : ZeroContinuation model) (features : SwiftTd.ActiveSet dimension) :
    ZeroContinuation (model.begin features) := by
  cases model with
  | discounted r c => exact zero_begin c.state hz _

/-- Continuing model credit uses zero continuation cumulant even when the
executed reward is positive or exceptional. -/
theorem zero_continuation_step (model : Model dimension .discounted)
    (hz : ZeroContinuation model) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (reward : Binary32) : ZeroContinuation (model.step features age reward) := by
  cases model with
  | discounted r c => exact zero_step c.state hz _ .zero (Or.inl rfl)

/-- A zero terminal meta value leaves continuation knowledge zero for every
reward word. Positive reward credit alone does not bootstrap this learner. -/
theorem zero_continuation_terminal (model : Model dimension .discounted)
    (hz : ZeroContinuation model) (reward terminal : Binary32) (ht : SignedZero terminal) :
    ZeroContinuation (model.terminal reward terminal) := by
  have target : SignedZero (Criterion.discounted.modelTerminal terminal) := by
    rcases ht with rfl | rfl <;> decide
  cases model with
  | discounted r c => exact zero_terminal c.state hz _ target

/-- Actual skill termination preserves zero continuation knowledge when its
terminal meta value is zero, including frozen activation and arbitrary interests. -/
theorem zero_continuation_end (skill : Skill config .discounted dimension)
    (hz : ZeroContinuation skill.model) {mode : Bool} (ending : EndingPayload mode)
    (reward terminal : Binary32) (gain : RewardRate) (ht : SignedZero terminal) :
    ZeroContinuation (skill.endTemporal (modelOperations .discounted dimension)
      ending reward terminal gain).model := by
  unfold Skill.endTemporal
  split
  · change ZeroContinuation
      (Model.terminal
        (skill.terminateOption ending.activation ending.potential reward terminal gain).model
        reward terminal)
    rw [(Skill.terminal_owners skill ending.activation ending.potential reward terminal gain).2]
    exact zero_continuation_terminal _ hz reward terminal ht
  · rw [(Skill.terminal_owners skill ending.activation ending.potential reward terminal gain).2]
    exact hz

/-- Every actual initialized discounted agent skill has zero continuation
knowledge, without a premise prescribing actions, targets or learned state. -/
theorem zero_continuation_agent_initial (profile : FeatureProfile)
    (config : Features.Config) (dimension : Dimension) (planning : PlanningSelection)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    let agent := Agent.initial profile config .discounted dimension planning
    ZeroContinuation (agent.control.runtime.lifecycle.consumers.skills.get slot).model := by
  simp only [Agent.initial, TemporalControl.initial, Ensemble.initial,
    CurrentLearner.vector_get, Vector.getElem_map,
    Skill.initial]
  exact zero_continuation_initial

/-- The executed skill-start owner preserves the continuation sector in both
learning and frozen modes. -/
theorem zero_continuation_skill_begin (skill : Skill config .discounted dimension)
    (hz : ZeroContinuation skill.model) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    ZeroContinuation (skill.beginTemporal (modelOperations .discounted dimension)
      features potential learning rate).1.model := by
  cases learning <;> simp only [Skill.beginTemporal, Skill.beginOption, Bool.false_eq_true,
    if_false, if_true, modelOperations]
  · exact hz
  · exact zero_continuation_begin _ hz features

/-- The executed option action preserves the continuation sector for every
actual draw and reward, including the age-zero model no-op. -/
theorem zero_continuation_skill_step (skill : Skill config .discounted dimension)
    (hz : ZeroContinuation skill.model) {mode : Bool} (activation : OptionActivation mode)
    (next : OptionContinuation dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    ZeroContinuation (skill.stepTemporal (modelOperations .discounted dimension)
      activation next reward gain rng).1.model := by
  have hm : (skill.optionStep activation next reward gain rng).1.model = skill.model := by
    unfold Skill.optionStep
    split <;> rfl
  unfold Skill.stepTemporal
  split
  · change ZeroContinuation ((skill.optionStep activation next reward gain rng).1.model.step
      next.features activation.age reward)
    rw [hm]
    exact zero_continuation_step _ hz _ _ reward
  · rw [hm]
    exact hz

/-- The actual close operation preserves all retained continuation learners
under zero terminal meta value. Detached old-owner results remain discarded.
This conditional endpoint does not derive the meta value from a native prefix. -/
theorem zero_continuation_close {profile : FeatureProfile}
    (state : TemporalControl profile config .discounted dimension)
    (hz : ∀ slot, ZeroContinuation (state.runtime.lifecycle.consumers.skills.get slot).model)
    (closing : Closing config .discounted dimension (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) (ht : SignedZero terminal) :
    ∀ slot, ZeroContinuation ((state.closeOption (modelOperations .discounted dimension)
      closing reward terminal).1.runtime.lifecycle.consumers.skills.get slot).model := by
  intro slot
  cases ho : closing.oldOwner with
  | some old => simpa only [TemporalControl.closeOption, ho] using hz slot
  | none =>
    simp only [TemporalControl.closeOption, ho, Option.getD, TemporalControl.withSkill,
      CurrentLearner.vector_get, Vector.getElem_set]
    split
    · have hs : closing.slot = slot := Fin.ext (by assumption)
      subst slot
      exact zero_continuation_end _ (hz closing.slot) closing.activation reward terminal
        state.average.rate ht
    · exact hz slot

/-- Zero weights exclude every actual bank candidate, including aliases, so
the complete current ranking consists of neutral assignments. -/
theorem zero_rank_assignments (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (hz : ∀ idx, SignedZero (weights.get idx).value) :
    rankAssignments dimension config weights = Vector.replicate _ .neutral := by
  have absent (unit : Fin config.units.count) :
      candidateOfWeight config weights unit = none := by
    have hn : ¬ 0 < (weights.get (unitFeature dimension config unit)).value.abs.key := by
      rcases hz (unitFeature dimension config unit) with h | h <;> rw [h] <;> decide
    simp [candidateOfWeight, hn]
  have empty : (List.finRange config.units.count).filterMap
      (candidateOfWeight config weights) = [] := by
    simp only [List.filterMap_eq_nil_iff]
    intro unit _; exact absent unit
  have rankedEmpty : ranked Acorn.FeatureConstants.skillCount
      ([] : List (Candidate config)) = [] := rfl
  simp only [rankAssignments, empty, rankedEmpty]
  apply Vector.ext
  intro idx hi
  simp

/-- Zero knowledge of the actual structurally selected Demon-0 learner.
Other prediction learners and feedback values are unrestricted. -/
def ZeroRanking {discounts : List Discount}
    (bank : DemonBank dimension (.g99 :: discounts)) : Prop :=
  match bank with | .cons learner _ => ZeroKnowledge learner.state

/-- The actual bank constructor establishes zero knowledge in its ranking head. -/
theorem zero_ranking_initial (discounts : List Discount) :
    ZeroRanking (DemonBank.initial dimension (.g99 :: discounts)) := zero_initial

/-- The sole ranking reader produces neutral targets from its zero knowledge. -/
theorem zero_ranking_assignments {discounts : List Discount}
    (bank : DemonBank dimension (.g99 :: discounts)) (hz : ZeroRanking bank)
    (config : Features.Config) :
    rankAssignments dimension config bank.rankingWeights = Vector.replicate _ .neutral := by
  cases bank with
  | cons learner rest => exact zero_rank_assignments config _ hz.weights

/-- Actual prediction/control completion preserves Demon-0 zero knowledge on
a zero-reward callback. Its cumulant is derived from the real reward indicator;
all other observation-dependent demons and frozen-mode behavior remain actual. -/
theorem zero_ranking_advance {profile : FeatureProfile} {criterion : Criterion}
    (state : PredictionControl profile criterion dimension) (hz : ZeroRanking state.demons)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (action : Action Acorn.FeatureConstants.primitiveCount) (own : Bool) (clock : UInt64)
    (hr : SignedZero reward) :
    ZeroRanking (state.advance features obs reward action own clock).demons := by
  have signal : Cumulant.eval ⟨0, by decide⟩ obs reward = .zero := by
    rcases hr with h | h <;> rw [h] <;> rfl
  unfold PredictionControl.advance
  split
  · exact hz
  · cases hb : state.demons with
    | cons learner rest =>
      have hn : ZeroKnowledge learner.state := by
        rw [hb] at hz
        exact hz
      change ZeroKnowledge (learner.state.step _ features
        (Cumulant.eval ⟨0, by decide⟩ obs reward)).1
      rw [signal]
      exact zero_step learner.state hn features .zero (Or.inl rfl)

/-- When the actual ranking head is zero and existing skills are neutral,
refresh only acknowledges its request. The real installation fold preserves
all consumers, transient state, caches, representation and closing ownership. -/
theorem zero_neutral_refresh {shape : PatchShape} {config : Features.Config}
    {criterion : Criterion}
    {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (hz : ZeroRanking state.lifecycle.consumers.demons)
    (hn : ∀ slot, (state.lifecycle.consumers.skills.get slot).interest = .learned .neutral) :
    state.refreshRanked = { state with refresh := state.refresh.take.2 } := by
  let taken := { state with refresh := state.refresh.take.2 }
  have installed (slot : Fin Acorn.FeatureConstants.skillCount) :
      taken.install slot .neutral = taken := by
    apply FreeDispatch.install_same
    apply (Interest.sameAssignment_iff _ _).mpr
    exact hn slot
  have fold (slots : List (Fin Acorn.FeatureConstants.skillCount)) :
      slots.foldl (fun current slot => current.install slot .neutral) taken = taken := by
    induction slots with
    | nil => rfl
    | cons slot rest ih => simpa only [List.foldl_cons, installed] using ih
  simp only [FreeDispatch.refreshRanked, zero_ranking_assignments _ hz config,
    Vector.getElem_replicate]
  split
  · exact fold _
  · rfl

open AcornVerif.CurrentControl

/-- Actual agent construction establishes zero meta-controller rows and lags. -/
theorem zero_meta_agent_initial (profile : FeatureProfile) (config : Features.Config)
    (dimension : Dimension) (planning : PlanningSelection) :
    let agent := Agent.initial profile config .discounted dimension planning
    ZeroController agent.control.runtime.lifecycle.consumers.metaController := by
  simp only [Agent.initial, TemporalControl.initial, Ensemble.initial]
  exact zero_controller_initial

/-- The executed old meta snapshot supplies the zero continuation target.
This removes the independent terminal-word premise at the close boundary, but
full native-prefix preservation of the incoming zero sectors remains separate. -/
theorem zero_continuation_close_snapshot
    (state : TemporalControl profile config .discounted dimension)
    (hz : ∀ slot, ZeroContinuation (state.runtime.lifecycle.consumers.skills.get slot).model)
    (hmeta : ZeroController state.runtime.lifecycle.consumers.metaController)
    (closing : Closing config .discounted dimension (EndingPayload (profile.mode != .frozen)))
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    let snapshot := state.runtime.lifecycle.consumers.metaController.snapshot
      (count := metaCount) features state.metaRate
    let result := state.closeOption (modelOperations .discounted dimension)
      closing reward (comparisonValue .discounted snapshot)
    ∀ slot, ZeroContinuation (result.1.runtime.lifecycle.consumers.skills.get slot).model := by
  exact zero_continuation_close state hz closing reward _
    (zero_snapshot_best (count := metaCount) _ hmeta features state.metaRate)

/-- Both actual discounted scalar model learners have zero knowledge. Other
raw registers, beta, caches and the current model age remain unrestricted. -/
def ZeroModel (model : Model dimension .discounted) : Prop :=
  match model with | .discounted r c => ZeroKnowledge r.state ∧ ZeroKnowledge c.state

/-- Actual discounted model construction establishes both zero sectors. -/
theorem zero_model_initial : ZeroModel (Model.initial dimension .discounted) :=
  ⟨zero_initial, zero_initial⟩

/-- Actual initiation primes both learners without changing zero knowledge. -/
theorem zero_model_begin (model : Model dimension .discounted) (hz : ZeroModel model)
    (features : SwiftTd.ActiveSet dimension) : ZeroModel (model.begin features) := by
  cases model with
  | discounted r c => exact ⟨zero_begin r.state hz.1 _, zero_begin c.state hz.2 _⟩

/-- Actual continuing zero reward preserves both scalar learners for every
age-augmented input, including arbitrary stored raw transients. -/
theorem zero_model_step (model : Model dimension .discounted) (hz : ZeroModel model)
    (features : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32)
    (hr : SignedZero reward) : ZeroModel (model.step features age reward) := by
  cases model with
  | discounted r c => exact ⟨zero_step r.state hz.1 _ reward hr,
      zero_continuation_step (.discounted r c) hz.2 features age reward⟩

/-- Actual terminal credit uses zero reward and the supplied zero meta
snapshot value; snapshot production is a separate controller obligation. -/
theorem zero_model_terminal (model : Model dimension .discounted) (hz : ZeroModel model)
    (reward terminal : Binary32) (hr : SignedZero reward) (ht : SignedZero terminal) :
    ZeroModel (model.terminal reward terminal) := by
  cases model with
  | discounted r c => exact ⟨zero_terminal r.state hz.1 reward hr,
      zero_continuation_terminal (.discounted r c) hz.2 reward terminal ht⟩

/-- The fresh planning target is produced as zero by the actual two stored
learners and projections. Cached predictions and gain do not enter this claim. -/
theorem zero_model_target (model : Model dimension .discounted) (hz : ZeroModel model)
    (features : SwiftTd.ActiveSet dimension) (age : ModelAge) (gain : RewardRate) :
    SignedZero ((model.predict features age).target gain) := by
  cases model with
  | discounted r c =>
    have hr := zero_prediction r.state hz.1 (modelInput .discounted features age)
    have hc := zero_prediction c.state hz.2 (modelInput .discounted features age)
    change SignedZero ((Prediction.project .g99
      ((Bounded32.project Criterion.discounted.modelRewardRange
        (r.state.predict (modelInput .discounted features age))).value.add
        (Criterion.discounted.modelContinuation
          (c.state.predict (modelInput .discounted features age))))).value)
    rcases hr with h | h <;> rcases hc with hc | hc <;> rw [h, hc] <;> decide

/-- A backup from actual zero models and zero controller rows preserves the
whole controller. Cache and error observations may be overwritten. -/
theorem zero_backup_controller (state : PlanningResult .discounted dimension)
    (hz : CurrentControl.ZeroController state.controller)
    (skills : Vector (Skill config .discounted dimension) Acorn.FeatureConstants.skillCount)
    (hm : ∀ slot, ZeroModel (skills.get slot).model)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (state.backup skills features gain slot).controller = state.controller := by
  exact congrArg Prod.fst (CurrentControl.zero_controller_plan state.controller hz
    (metaOfSkill slot) features _
    (zero_model_target _ (hm slot) features ⟨0, by decide⟩ gain))

/-- The actual ordered scalar-planning fold preserves the complete zero
controller. This holds for either configured planning selection and arbitrary
cache, error and clock words; those observation fields are not claimed equal. -/
theorem zero_planning_controller (selection : PlanningSelection)
    (state : PlanningResult .discounted dimension)
    (hz : CurrentControl.ZeroController state.controller)
    (skills : Vector (Skill config .discounted dimension) Acorn.FeatureConstants.skillCount)
    (hm : ∀ slot, ZeroModel (skills.get slot).model)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) :
    (planningBoundary selection state skills features gain).controller = state.controller := by
  have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
      (s : PlanningResult .discounted dimension)
      (hs : CurrentControl.ZeroController s.controller) :
      (slots.foldl (fun s slot => s.backup skills features gain slot) s).controller =
        s.controller := by
    induction slots generalizing s with
    | nil => rfl
    | cons slot rest ih =>
      have he := zero_backup_controller s hs skills hm features gain slot
      have hzNext : CurrentControl.ZeroController
          (s.backup skills features gain slot).controller := by rw [he]; exact hs
      exact (ih _ hzNext).trans he
  cases selection with
  | none => rfl
  | scalar => exact fold planningSlots state hz

/-- The actual neutral-interest producer returns false for every active set
and declared observation payload, including hash aliases. -/
theorem neutral_potential (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) :
    (Interest.learned (.neutral : Assignment config)).potential features declared =
      some false := rfl

/-- Neutral continuing and terminal cumulants are zero under zero reward and
zero old meta value, with the executed discounted operation order. -/
theorem zero_neutral_targets (reward terminal : Binary32) (gain : RewardRate)
    (hr : SignedZero reward) (ht : SignedZero terminal) :
    SignedZero (Features.shapedCumulant (Criterion.discounted.center reward 1 gain)
      Criterion.discounted.rule.gamma false false) ∧
    SignedZero (Features.terminalCumulant (Criterion.discounted.center reward 1 gain)
      ((Interest.learned (.neutral : Assignment config)).stoppingValue terminal false) false) := by
  change SignedZero (Features.shapedCumulant reward Criterion.discounted.rule.gamma false false) ∧
    SignedZero (Features.terminalCumulant reward
      ((Interest.learned (.neutral : Assignment config)).stoppingValue terminal false) false)
  simp only [Interest.stoppingValue, Assignment.stoppingValue, Assignment.bonus,
    Potential.value, Bool.false_eq_true, if_false]
  rcases hr with rfl | rfl <;> rcases ht with rfl | rfl <;> decide

/-- Neutral option termination consumes the actual old meta snapshot, whose
zero value follows from its stored controller. This includes frozen activation;
the incoming previous-potential invariant remains an explicit scheduling premise. -/
theorem zero_neutral_terminal_snapshot (skill : Skill config .discounted dimension)
    (hz : ZeroController skill.policy) (hn : skill.interest = .learned .neutral)
    {mode : Bool} (activation : OptionActivation mode) (hp : activation.previous = false)
    (metaController :
      Controller (Criterion.discounted.config .control) dimension metaCount.word.toNat)
    (hm : ZeroController metaController) (features : SwiftTd.ActiveSet dimension)
    (rate : SwiftTd.ExploreRate) (reward : Binary32) (hr : SignedZero reward) (gain : RewardRate) :
    let terminal := comparisonValue .discounted
      (metaController.snapshot (count := metaCount) features rate)
    ZeroController (skill.terminateOption activation false reward terminal gain).policy := by
  have ht := zero_snapshot_best (count := metaCount) metaController hm features rate
  have target := (zero_neutral_targets (config := config) reward _ gain hr ht).2
  dsimp only
  unfold Skill.terminateOption
  split
  · apply zero_controller_terminal _ hz
    simpa only [hn, hp, comparisonValue] using target
  · exact hz

/-- One neutral discounted objective and its actual policy/model zero sectors.
No constraint is placed on beta, other raw registers, rates or cached predictions. -/
structure ZeroNeutralSkill (skill : Skill config .discounted dimension) : Prop where
  /-- The actual interest produces the neutral coordinate. -/
  neutral : skill.interest = .learned .neutral
  /-- Every physical policy row and shared Sarsa lag is zero. -/
  policy : ZeroController skill.policy
  /-- Both physical discounted model learners are zero. -/
  model : ZeroModel skill.model

/-- Actual neutral skill construction establishes all three sector fields. -/
theorem zero_neutral_skill_initial :
    ZeroNeutralSkill (Skill.initial config .discounted dimension (.learned .neutral)) :=
  ⟨rfl, zero_controller_initial, zero_model_initial⟩

private theorem continuation_produced (skill : Skill config criterion dimension)
    {mode : Bool} (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential)
    (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (next : OptionContinuation dimension activation)
    (produced : skill.decideOption activation features potential goal estimate rate =
      .continuing next) :
    next.features = features ∧ next.potential = potential ∧
    next.policy = skill.policy.snapshot (count := primitiveCount) features
      (rate.resolve fun _ => skill.policy.exploreRate (count := primitiveCount)) := by
  unfold Skill.decideOption at produced
  split at produced
  · cases produced
  · split at produced
    · dsimp only at produced
      split at produced
      · cases produced
      · cases produced
        exact ⟨rfl, rfl, rfl⟩
    · cases produced

private theorem zero_neutral_skill_step (skill : Skill config .discounted dimension)
    (hz : ZeroNeutralSkill skill) {mode : Bool} (activation : OptionActivation mode)
    (next : OptionContinuation dimension activation) (hp : activation.previous = false)
    (hn : next.potential = false) (rate : SwiftTd.ExploreRate)
    (snapshot : next.policy = skill.policy.snapshot (count := primitiveCount) next.features rate)
    (reward : Binary32) (hr : SignedZero reward) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    let result := skill.stepTemporal (modelOperations .discounted dimension)
      activation next reward gain rng
    ZeroNeutralSkill result.1 ∧ result.2.1.previous = false := by
  have target : SignedZero (Features.shapedCumulant (Criterion.discounted.center reward 1 gain)
      Criterion.discounted.rule.gamma next.potential activation.previous) := by
    simpa only [hn, hp] using
      (zero_neutral_targets (config := config) reward .zero gain hr (Or.inl rfl)).1
  have credited : ZeroController (actions := Acorn.FeatureConstants.primitiveCount)
      (skill.policy.policyStep next.features (next.policy.draw rng).1
      (Features.shapedCumulant (Criterion.discounted.center reward 1 gain)
        Criterion.discounted.rule.gamma next.potential activation.previous) 1) := by
    rw [snapshot]
    exact zero_draw_policy_step (count := primitiveCount) skill.policy hz.policy
      next.features rate rng _ 1 target
  have policy : ZeroController (skill.optionStep activation next reward gain rng).1.policy := by
    by_cases learning : activation.learning = true
    · simpa only [Skill.optionStep, learning, if_true] using credited
    · simpa only [Skill.optionStep, learning, Bool.false_eq_true, if_false] using hz.policy
  have model : ZeroModel (skill.stepTemporal (modelOperations .discounted dimension)
      activation next reward gain rng).1.model := by
    by_cases learning : activation.learning = true
    · by_cases first : activation.age.val = 0
      · rw [CurrentModels.first_model_omitted _ _ _ _ _ _ first]
        exact hz.model
      · rw [CurrentModels.continuing_model_owner _ _ _ _ _ _ learning (by omega)]
        exact zero_model_step _ hz.model next.features activation.age reward hr
    · have frozen : activation.learning = false := by
        cases h : activation.learning <;> simp_all
      simp only [Skill.stepTemporal, frozen, Bool.false_and, Bool.false_eq_true, if_false]
      rw [Skill.step_frozen _ _ _ _ _ _ frozen]
      exact hz.model
  dsimp only
  constructor
  · constructor
    · rw [Skill.stepTemporal_interest]
      exact hz.neutral
    · rw [(skill.stepTemporal_policy (modelOperations .discounted dimension)
        activation next reward gain rng).1]
      exact policy
    · exact model
  · rw [(skill.stepTemporal_policy (modelOperations .discounted dimension)
      activation next reward gain rng).2]
    exact hn

private theorem zero_neutral_skill_begun (skill : Skill config .discounted dimension)
    (hz : ZeroNeutralSkill skill) (features : SwiftTd.ActiveSet dimension)
    (learning : Bool) (rate : ConsumerRate) :
    ZeroNeutralSkill (skill.beginTemporal (modelOperations .discounted dimension)
      features false learning rate).1 := by
  constructor
  · rw [Skill.beginTemporal_interest]
    exact hz.neutral
  · cases learning with
    | false => exact hz.policy
    | true => exact zero_controller_clear _ hz.policy
  · cases learning with
    | false => exact hz.model
    | true => exact zero_model_begin _ hz.model features

/-- The actual begin token freezes the cleared or frozen policy and immediately
returns its first action. Both model learners remain in their begun zero sector;
no age-zero model credit is manufactured. RNG and rate selection are unrestricted. -/
theorem zero_neutral_skill_begin (skill : Skill config .discounted dimension)
    (hz : ZeroNeutralSkill skill) (features : SwiftTd.ActiveSet dimension)
    (learning : Bool) (rate : ConsumerRate) (reward : Binary32) (hr : SignedZero reward)
    (gain : RewardRate) (rng : Rng.Xoshiro256) :
    let begun := skill.beginTemporal (modelOperations .discounted dimension)
      features false learning rate
    let result := begun.1.stepTemporal (modelOperations .discounted dimension)
      begun.2.1 begun.2.2 reward gain rng
    ZeroNeutralSkill result.1 ∧ result.2.1.previous = false ∧ result.2.1.age.val = 1 := by
  let begun := skill.beginTemporal (modelOperations .discounted dimension)
    features false learning rate
  have hb : ZeroNeutralSkill begun.1 := zero_neutral_skill_begun skill hz features learning rate
  let resolved := rate.resolve fun _ => begun.1.policy.exploreRate (count := primitiveCount)
  have snapshot : begun.2.2.policy = begun.1.policy.snapshot (count := primitiveCount)
      begun.2.2.features resolved := by
    cases learning <;> rfl
  have stepped := zero_neutral_skill_step begun.1 hb begun.2.1 begun.2.2
    (by rfl) (by rfl) resolved snapshot reward hr gain rng
  refine ⟨stepped.1, stepped.2, ?_⟩
  rw [(begun.1.stepTemporal_policy (modelOperations .discounted dimension)
    begun.2.1 begun.2.2 reward gain rng).2]
  simpa only [show begun.2.1.age.val = 0 from rfl, Nat.zero_add] using
    begun.1.step_age begun.2.1 begun.2.2 reward gain rng

/-- An actual continuing decision carries the incoming policy's snapshot and
neutral coordinate into the exact step. The branch equality identifies its
producer; it asserts neither eventual continuation nor action coverage. -/
theorem zero_neutral_skill_continuing (skill : Skill config .discounted dimension)
    (hz : ZeroNeutralSkill skill) {mode : Bool} (activation : OptionActivation mode)
    (hp : activation.previous = false) (features : SwiftTd.ActiveSet dimension)
    (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (next : OptionContinuation dimension activation)
    (produced : skill.decideOption activation features false goal estimate rate = .continuing next)
    (reward : Binary32) (hr : SignedZero reward) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    let result := skill.stepTemporal (modelOperations .discounted dimension)
      activation next reward gain rng
    ZeroNeutralSkill result.1 ∧ result.2.1.previous = false := by
  obtain ⟨hf, hn, hs⟩ := continuation_produced skill activation features false goal estimate rate
    next produced
  have snapshot : next.policy = skill.policy.snapshot (count := primitiveCount) next.features
      (rate.resolve fun _ => skill.policy.exploreRate (count := primitiveCount)) := by
    simpa only [hf] using hs
  exact zero_neutral_skill_step skill hz activation next hp hn _ snapshot reward hr gain rng

/-- Terminal policy and continuation use the same old meta snapshot; the reward
model consumes raw reward. Neutral coordinate premises belong to the incoming
activation and current interest producer, before later refresh or meta credit. -/
theorem zero_neutral_skill_end_snapshot (skill : Skill config .discounted dimension)
    (hz : ZeroNeutralSkill skill) {mode : Bool} (ending : EndingPayload mode)
    (hp : ending.activation.previous = false) (hn : ending.potential = false)
    (metaController :
      Controller (Criterion.discounted.config .control) dimension metaCount.word.toNat)
    (hm : ZeroController metaController) (features : SwiftTd.ActiveSet dimension)
    (rate : SwiftTd.ExploreRate) (reward : Binary32) (hr : SignedZero reward) (gain : RewardRate) :
    let terminal := comparisonValue .discounted
      (metaController.snapshot (count := metaCount) features rate)
    ZeroNeutralSkill (skill.endTemporal (modelOperations .discounted dimension)
      ending reward terminal gain) := by
  let terminal := comparisonValue .discounted
    (metaController.snapshot (count := metaCount) features rate)
  have ht : SignedZero terminal :=
    zero_snapshot_best (count := metaCount) metaController hm features rate
  have policy : ZeroController
      (skill.terminateOption ending.activation ending.potential reward terminal gain).policy := by
    rw [hn]
    exact zero_neutral_terminal_snapshot skill hz.policy hz.neutral ending.activation hp
      metaController hm features rate reward hr gain
  constructor
  · rw [Skill.endTemporal_interest]
    exact hz.neutral
  · dsimp only [Skill.endTemporal]
    split <;> exact policy
  · unfold Skill.endTemporal
    split
    · change ZeroModel (Model.terminal
        (skill.terminateOption ending.activation ending.potential reward terminal gain).model
        reward terminal)
      rw [(skill.terminal_owners ending.activation ending.potential reward terminal gain).2]
      exact zero_model_terminal _ hz.model reward terminal hr ht
    · rw [(skill.terminal_owners ending.activation ending.potential reward terminal gain).2]
      exact hz.model

/-- The actual retained skill table is neutral and zero; a stored active
option carries false previous potential. Other learners and references are
unrestricted, so this is not yet the complete callback zero-sector invariant. -/
structure ZeroSkillState (state : TemporalControl profile config .discounted dimension) : Prop where
  /-- All physical policies and both models at every retained slot. -/
  skills : ∀ slot, ZeroNeutralSkill (state.runtime.lifecycle.consumers.skills.get slot)
  /-- The actual stored activation, whenever an option occupies the phase. -/
  phase : ∀ slot activation, state.runtime.references.phase = .option slot activation →
    activation.previous = false

private theorem withSkill_selected_skill
    (state : TemporalControl profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (skill : Skill config criterion dimension) :
    (state.withSkill slot skill).runtime.lifecycle.consumers.skills.get slot = skill := by
  simp only [TemporalControl.withSkill, CurrentLearner.vector_get, Vector.getElem_set_self]

/-- A same-slot installation preserves every other actual skill and the
stored phase; its replacement already carries the complete neutral zero sector. -/
theorem zero_skill_state_with_skill (state : TemporalControl profile config .discounted dimension)
    (hz : ZeroSkillState state) (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill config .discounted dimension) (hs : ZeroNeutralSkill skill) :
    ZeroSkillState (state.withSkill slot skill) := by
  constructor
  · intro other
    by_cases same : other = slot
    · subst other
      rw [withSkill_selected_skill]
      exact hs
    · rw [withSkill_other_skill _ _ _ _ same]
      exact hz.skills other
  · exact hz.phase

/-- Neutral coordinate admission is derived from the actual retained table,
for arbitrary encoded features and declared observation payload. -/
theorem zero_skill_state_potential (state : TemporalControl profile config .discounted dimension)
    (hz : ZeroSkillState state) (slot : Fin Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    (state.runtime.lifecycle.consumers.skills.get slot).interest.potential features declared =
      some false := by
  rw [(hz.skills slot).neutral]
  exact neutral_potential features declared

private theorem zero_skill_state_idle (state : TemporalControl profile config .discounted dimension)
    (hz : ZeroSkillState state) : ZeroSkillState (state.withPhase .idle) := by
  refine ⟨hz.skills, ?_⟩
  intro slot activation phase
  cases phase

private theorem zero_skill_state_step_result
    (state : TemporalControl profile config .discounted dimension) (hz : ZeroSkillState state)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation dimension activation) (reward : Binary32)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool) (ended : Option EndEvent)
    (kept :
      let result := (state.runtime.lifecycle.consumers.skills.get slot).stepTemporal
        (modelOperations .discounted dimension) activation next reward state.average.rate
        state.runtime.references.rng
      ZeroNeutralSkill result.1 ∧ result.2.1.previous = false) :
    ZeroSkillState (state.stepOption (modelOperations .discounted dimension) slot activation next
      reward metaValues metaDecision started ended).1 := by
  have installed := zero_skill_state_with_skill state hz slot _ kept.1
  constructor
  · exact installed.skills
  · intro current active phase
    change Occupancy.option slot _ = Occupancy.option current active at phase
    cases phase
    exact kept.2

/-- Continuing selection reads the actual stored activation, then clears the
phase before installing the returned action. Its token is the actual decision's
output; metadata arguments cannot choose a different receiving skill. -/
theorem zero_skill_state_continuing
    (state : TemporalControl profile config .discounted dimension) (hz : ZeroSkillState state)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (phase : state.runtime.references.phase = .option slot activation)
    (features : SwiftTd.ActiveSet dimension) (goal : Bool) (estimate : Binary32)
    (next : OptionContinuation dimension activation)
    (produced : (state.runtime.lifecycle.consumers.skills.get slot).decideOption activation
      features false goal estimate state.skillRate = .continuing next)
    (reward : Binary32) (hr : SignedZero reward)
    (metaValues : Vector Binary32 metaCount.word.toNat) :
    ZeroSkillState (((state.withPhase .idle).withoutPlanning.stepOption
      (modelOperations .discounted dimension) slot activation next reward metaValues
      none false none).1.skipMeta) := by
  have hp := hz.phase slot activation phase
  have hs := zero_neutral_skill_continuing _ (hz.skills slot) activation hp features goal
    estimate state.skillRate next produced reward hr state.average.rate state.runtime.references.rng
  have idle := zero_skill_state_idle state hz
  have free : ZeroSkillState (state.withPhase .idle).withoutPlanning :=
    ⟨idle.skills, idle.phase⟩
  have result := zero_skill_state_step_result (state.withPhase .idle).withoutPlanning free
    slot activation next reward metaValues none false none hs
  unfold TemporalControl.skipMeta
  split
  · exact ⟨result.skills, result.phase⟩
  · exact result

private theorem zero_skill_state_meta_credit
    (state : TemporalControl profile config .discounted dimension) (hz : ZeroSkillState state)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    ZeroSkillState (state.learnMeta features decision) := by
  unfold TemporalControl.learnMeta
  split
  · exact hz
  · exact ⟨hz.skills, hz.phase⟩

private theorem zero_skill_state_primitive
    (state : TemporalControl profile config .discounted dimension) (hz : ZeroSkillState state)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 metaCount.word.toNat)
    (decision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    ZeroSkillState (state.choosePrimitive features values decision ended).1 := by
  constructor
  · exact hz.skills
  · intro slot activation phase
    dsimp only [TemporalControl.choosePrimitive, TemporalControl.withPhase] at phase
    split at phase
    · split at phase <;> cases phase
    · cases phase

/-- Actual meta dispatch derives neutral potential from the selected table
entry, then installs that exact begin/first-action result. Primitive selection
also preserves the table and leaves a non-option phase. This is a local dispatch
property, with no favorable action, owner or token independently prescribed. -/
theorem zero_skill_state_dispatch
    (state final : TemporalControl profile config .discounted dimension) (hz : ZeroSkillState state)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (reward : Binary32) (hr : SignedZero reward) (metaDecision : PolicyDecision metaCount)
    (ended : Option EndEvent) (decision : TemporalDecision)
    (executed : state.dispatchMeta (modelOperations .discounted dimension)
      features declared reward metaDecision ended = some (final, decision)) :
    ZeroSkillState final := by
  let credited := state.learnMeta features metaDecision
  have hc : ZeroSkillState credited := zero_skill_state_meta_credit state hz features metaDecision
  unfold TemporalControl.dispatchMeta at executed
  dsimp only at executed
  cases selected : skillOfMeta metaDecision.action with
  | none =>
    simp only [selected, pure, Option.some.injEq] at executed
    have same := congrArg Prod.fst executed
    dsimp only at same
    rw [← same]
    exact zero_skill_state_primitive credited hc features metaDecision.snapshot.values
      (some metaDecision) ended
  | some slot =>
    have potential := zero_skill_state_potential credited hc slot features declared
    dsimp only [credited] at potential
    simp only [selected, bind, Option.bind, potential, pure, Option.some.injEq] at executed
    have same := congrArg Prod.fst executed
    dsimp only at same
    rw [← same]
    let skill := credited.runtime.lifecycle.consumers.skills.get slot
    let begun := skill.beginTemporal (modelOperations .discounted dimension)
      features false (profile.mode != .frozen) credited.skillRate
    have hb : ZeroNeutralSkill begun.1 := zero_neutral_skill_begun skill (hc.skills slot)
      features (profile.mode != .frozen) credited.skillRate
    have hi := zero_skill_state_with_skill credited hc slot begun.1 hb
    have first := zero_neutral_skill_begin skill (hc.skills slot) features
      (profile.mode != .frozen) credited.skillRate reward hr credited.average.rate
      credited.runtime.references.rng
    apply zero_skill_state_step_result (credited.withSkill slot begun.1) hi slot
      begun.2.1 begun.2.2 reward metaDecision.snapshot.values (some metaDecision) true ended
    rw [withSkill_selected_skill]
    exact ⟨first.1, first.2.1⟩

/-- Close preserves the actual skill table/phase invariant using the current
pre-close meta snapshot. Only a retained owner needs neutral coordinate premises;
a detached owner's terminal result is discarded without any zero-sector premise. -/
theorem zero_skill_state_close_snapshot
    (state : TemporalControl profile config .discounted dimension) (hz : ZeroSkillState state)
    (hm : ZeroController state.runtime.lifecycle.consumers.metaController)
    (closing : Closing config .discounted dimension (EndingPayload (profile.mode != .frozen)))
    (coordinates : closing.oldOwner = none →
      closing.activation.activation.previous = false ∧ closing.activation.potential = false)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) (hr : SignedZero reward) :
    let terminal := comparisonValue .discounted
      (state.runtime.lifecycle.consumers.metaController.snapshot
        (count := metaCount) features state.metaRate)
    ZeroSkillState (state.closeOption (modelOperations .discounted dimension)
      closing reward terminal).1 := by
  cases owner : closing.oldOwner with
  | some old => simpa only [TemporalControl.closeOption, owner] using hz
  | none =>
    simp only [TemporalControl.closeOption, owner, Option.getD]
    apply zero_skill_state_with_skill state hz
    exact zero_neutral_skill_end_snapshot _ (hz.skills closing.slot) closing.activation
      (coordinates owner).1 (coordinates owner).2 _ hm features state.metaRate reward hr
      state.average.rate

/-- The actual stored active owner supplies the closing slot and previous
coordinate. Clear occupancy, then close that retained owner with the old meta
snapshot; every terminal reason obeys the same frame and leaves idle occupancy. -/
theorem zero_skill_state_close_active
    (state : TemporalControl profile config .discounted dimension) (hz : ZeroSkillState state)
    (hm : ZeroController state.runtime.lifecycle.consumers.metaController)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (phase : state.runtime.references.phase = .option slot activation)
    (reason : OptionEnd) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (hr : SignedZero reward) :
    let closing : Closing config .discounted dimension
        (EndingPayload (profile.mode != .frozen)) :=
      ⟨slot, ⟨activation, false, reason⟩, none⟩
    let terminal := comparisonValue .discounted
      (state.runtime.lifecycle.consumers.metaController.snapshot
        (count := metaCount) features state.metaRate)
    let result := (state.withPhase .idle).closeOption (modelOperations .discounted dimension)
      closing reward terminal
    ZeroSkillState result.1 ∧ result.1.runtime.references.phase = .idle := by
  have idle := zero_skill_state_idle state hz
  refine ⟨zero_skill_state_close_snapshot (state.withPhase .idle) idle hm _ ?_
    features reward hr, rfl⟩
  intro retained
  exact ⟨hz.phase slot activation phase, rfl⟩

/-- Joined zero sector for the actual ordinary ranked discounted control state.
The other ten prediction demons, other raw registers, beta, rates, caches and
representation are unrestricted. This predicate alone supplies neither callback
preservation nor complete-reader retirement eligibility. -/
structure ZeroRankedState
    (state : TemporalControl (researchProfile .ranked) config .discounted dimension) : Prop where
  /-- Neutral skills, their complete policy/model storage and stored option coordinate. -/
  skills : ZeroSkillState state
  /-- Every primitive row and its shared Sarsa lags. -/
  control : ZeroController state.runtime.lifecycle.consumers.control
  /-- Every meta row and its shared Sarsa lags. -/
  metaController : ZeroController state.runtime.lifecycle.consumers.metaController
  /-- The actual prediction learner used to rank replacement objectives. -/
  ranking : ZeroRanking state.runtime.lifecycle.consumers.demons
  /-- Deferred meta reward in the receiver's actual byte-bounded gap. -/
  gap : SignedZero state.gap.reward

/-- Cold construction of the current public ranked profile establishes the
joined predicate for every admitted feature configuration, dimension and planning
selection. This is the actual constructor base case, not a restored-state witness
or a proof that a subsequent callback preserves the predicate. -/
theorem zero_ranked_initial (config : Features.Config) (dimension : Dimension)
    (planning : PlanningSelection) :
    ZeroRankedState
      (Agent.initial (researchProfile .ranked) config .discounted dimension planning).control := by
  constructor
  · constructor
    · intro slot
      simp only [Agent.initial, TemporalControl.initial, Ensemble.initial,
        FeatureProfile.interests, researchProfile, CurrentLearner.vector_get,
        Vector.getElem_map, Vector.getElem_ofFn]
      exact zero_neutral_skill_initial
    · intro slot activation phase
      cases phase
  · exact zero_controller_initial
  · exact zero_meta_agent_initial _ _ _ _
  · exact zero_ranking_initial _
  · exact Or.inl rfl

/-- Preparing actual ranked selection changes rates and model observations,
while zero reward preserves the receiver's accumulated meta gap. Features and
all unconstrained cached/model observation values may vary on every call. -/
theorem zero_ranked_prepare
    (state : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (hr : SignedZero reward) :
    ZeroRankedState
      (state.prepareSelection (modelOperations .discounted dimension) features reward) := by
  refine ⟨⟨hz.skills.skills, hz.skills.phase⟩, hz.control, hz.metaController, hz.ranking, ?_⟩
  exact zero_gap_accumulate state.gap hz.gap reward hr (Criterion.rule .discounted)

/-- Consecutive actual meta draw and credit preserve the entire joined sector.
The decision retains this receiver's producing snapshot and the reward comes
from its own owed gap; neither is an independently supplied favorable input.
This endpoint does not assert that every boundary performs those calls without
intervening writes. -/
theorem zero_ranked_draw_credit
    (state : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state) (features : SwiftTd.ActiveSet dimension) :
    let drawn := state.drawMeta features
    ZeroRankedState (drawn.1.learnMeta features drawn.2) := by
  refine ⟨⟨hz.skills.skills, hz.skills.phase⟩, hz.control, ?_, hz.ranking, Or.inl rfl⟩
  exact zero_draw_policy_step (count := metaCount)
    state.runtime.lifecycle.consumers.metaController hz.metaController features state.metaRate
    state.runtime.references.rng state.gap.reward state.gap.close.2 hz.gap

/-- Actual neutral ranking acknowledges refresh without changing joined
storage. The optional closing owner is carried by the existing refresh fold. -/
theorem zero_ranked_refresh
    (state : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state)
    (closing : Option (Closing config .discounted dimension (EndingPayload true))) :
    ZeroRankedState (state.refreshFree closing).1 := by
  dsimp only [TemporalControl.refreshFree]
  rw [zero_neutral_refresh _ hz.ranking (fun slot => (hz.skills.skills slot).neutral)]
  exact ⟨⟨hz.skills.skills, hz.skills.phase⟩, hz.control, hz.metaController, hz.ranking, hz.gap⟩

/-- The configured concrete planning boundary preserves the joined sector.
Its fresh zero model targets preserve the whole meta controller; cache, error
and planning-clock observations retain their actual unconstrained updates. -/
theorem zero_ranked_plan
    (state : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state) (selection : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) :
    ZeroRankedState (state.planFree (planningBoundary selection) features) := by
  refine ⟨⟨hz.skills.skills, hz.skills.phase⟩, hz.control, ?_, hz.ranking, hz.gap⟩
  change ZeroController (planningBoundary selection _ _ features state.average.rate).controller
  rw [zero_planning_controller selection _ hz.metaController _
    (fun slot => (hz.skills.skills slot).model)]
  exact hz.metaController

/-- Actual dispatch after the receiver's own meta draw preserves the joined
sector for every successful selected branch. Skill installation uses the real
begin/first-action result; no meta decision is supplied independently. -/
theorem zero_ranked_dispatch
    (state final : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (hr : SignedZero reward)
    (ended : Option EndEvent) (decision : TemporalDecision)
    (executed : let drawn := state.drawMeta features
      drawn.1.dispatchMeta (modelOperations .discounted dimension)
        features declared reward drawn.2 ended = some (final, decision)) :
    ZeroRankedState final := by
  let drawn := state.drawMeta features
  change drawn.1.dispatchMeta _ features declared reward drawn.2 ended = _ at executed
  have hc := zero_ranked_draw_credit state hz features
  have hs := zero_skill_state_dispatch drawn.1 final ⟨hz.skills.skills, hz.skills.phase⟩
    features declared reward hr drawn.2 ended decision executed
  unfold TemporalControl.dispatchMeta at executed
  dsimp only at executed
  cases selected : skillOfMeta drawn.2.action with
  | none =>
    simp only [selected, pure, Option.some.injEq] at executed
    have same := congrArg Prod.fst executed
    dsimp only at same
    refine ⟨hs, ?_, ?_, ?_, ?_⟩ <;> rw [← same]
    · exact hc.control
    · exact hc.metaController
    · exact hc.ranking
    · exact hc.gap
  | some slot =>
    have potential := zero_skill_state_potential (drawn.1.learnMeta features drawn.2)
      hc.skills slot features declared
    simp only [selected, bind, Option.bind, potential, pure, Option.some.injEq] at executed
    have same := congrArg Prod.fst executed
    dsimp only at same
    refine ⟨hs, ?_, ?_, ?_, ?_⟩ <;> rw [← same]
    · exact hc.control
    · exact hc.metaController
    · exact hc.ranking
    · exact hc.gap

/-- The ordinary discounted free boundary with no pending close preserves the
joined sector, through actual refresh, configured planning, meta draw and selected
dispatch. An option ending must establish its pre-boundary sector separately. -/
theorem zero_ranked_boundary
    (state final : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state) (selection : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (reward : Binary32) (hr : SignedZero reward) (ended : Option EndEvent)
    (decision : TemporalDecision)
    (executed : state.atBoundary (modelOperations .discounted dimension)
      (planningBoundary selection) features declared reward none ended =
        some (final, decision)) :
    ZeroRankedState final := by
  let free : FreeDispatch Host.patchShape config .discounted dimension demonLayout.tail
      (EndingPayload true) :=
    ⟨state.runtime.lifecycle, state.runtime.refresh,
      state.runtime.references.modelPredictions, none⟩
  have empty : (state.refreshFree none).2 = none := by
    change free.refreshRanked.closing = none
    exact refresh_closing_none (config := config) (criterion := .discounted)
      (dimension := dimension) (shape := Host.patchShape) (discounts := demonLayout.tail)
      (payload := EndingPayload true) (state := free) rfl
  have refreshed := zero_ranked_refresh state hz none
  have planned := zero_ranked_plan (state.refreshFree none).1 refreshed selection features
  unfold TemporalControl.atBoundary at executed
  dsimp only at executed
  rw [empty] at executed
  exact zero_ranked_dispatch _ final planned features declared reward hr ended decision executed

/-- Served exploration retains priority and preserves the joined sector.
Its actual next exploratory phase, gap skip and diagnostic clearing are framed;
no assumption removes a served action from the selection schedule. -/
theorem zero_ranked_serve
    (state final : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state) (features : SwiftTd.ActiveSet dimension)
    (decision : TemporalDecision) (executed : state.serve features = some (final, decision)) :
    ZeroRankedState final := by
  unfold TemporalControl.serve at executed
  split at executed
  · rename_i run phase
    cases served : run.serve with
    | none => simp [served, bind, Option.bind] at executed
    | some pair =>
      simp only [served, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at executed
      rw [← executed.1]
      refine ⟨⟨hz.skills.skills, ?_⟩, hz.control, hz.metaController, hz.ranking, hz.gap⟩
      intro slot activation phase
      change Occupancy.exploring _ = Occupancy.option slot activation at phase
      cases phase
  · contradiction
  · contradiction

/-- An actual continuing token from the stored active option preserves the
join through phase clearing, step installation and skipped meta credit.
The comparison and reported values come from the same old meta snapshot. -/
theorem zero_ranked_continuing
    (state : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation true)
    (phase : state.runtime.references.phase = .option slot activation)
    (features : SwiftTd.ActiveSet dimension) (goal : Bool)
    (next : OptionContinuation dimension activation)
    (produced : (state.runtime.lifecycle.consumers.skills.get slot).decideOption activation
      features false goal (comparisonValue .discounted
        (state.runtime.lifecycle.consumers.metaController.snapshot
          (count := metaCount) features state.metaRate)) state.skillRate = .continuing next)
    (reward : Binary32) (hr : SignedZero reward) :
    let snapshot := state.runtime.lifecycle.consumers.metaController.snapshot
      (count := metaCount) features state.metaRate
    ZeroRankedState (((state.withPhase .idle).withoutPlanning.stepOption
      (modelOperations .discounted dimension) slot activation next reward snapshot.values
      none false none).1.skipMeta) := by
  refine ⟨?_, hz.control, hz.metaController, hz.ranking, hz.gap⟩
  exact zero_skill_state_continuing state hz.skills slot activation phase features goal _ next
    produced reward hr _

/-- Close the actual stored discounted option using its old pre-close meta
snapshot, then retain the joined sector at the now-idle boundary. The current
neutral coordinate is the value produced by the skill table. -/
theorem zero_ranked_close_active
    (state : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation true)
    (phase : state.runtime.references.phase = .option slot activation)
    (reason : OptionEnd) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (hr : SignedZero reward) :
    let closing : Closing config .discounted dimension (EndingPayload true) :=
      ⟨slot, ⟨activation, false, reason⟩, none⟩
    let terminal := comparisonValue .discounted
      (state.runtime.lifecycle.consumers.metaController.snapshot
        (count := metaCount) features state.metaRate)
    let result := (state.withPhase .idle).closeOption (modelOperations .discounted dimension)
      closing reward terminal
    ZeroRankedState result.1 ∧ result.1.runtime.references.phase = .idle := by
  have hs := zero_skill_state_close_active state hz.skills hz.metaController slot activation
    phase reason features reward hr
  exact ⟨⟨hs.1, hz.control, hz.metaController, hz.ranking, hz.gap⟩, hs.2⟩

/-- Successful actual ordinary selection preserves the joined sector across
served exploration, inactive boundaries, continuing options and discounted
endings. Features, goal and actual RNG remain arbitrary. Final primitive/demon
credit and retirement are later owners, outside this selection theorem. -/
theorem zero_ranked_selection
    (state final : TemporalControl (researchProfile .ranked) config .discounted dimension)
    (hz : ZeroRankedState state) (selection : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (reward : Binary32) (hr : SignedZero reward) (goal : Bool) (decision : TemporalDecision)
    (executed : state.selectWithOperations (modelOperations .discounted dimension)
      (planningBoundary selection) features declared reward goal = some (final, decision)) :
    ZeroRankedState final := by
  unfold TemporalControl.selectWithOperations at executed
  generalize preparedEq : state.prepareSelection (modelOperations .discounted dimension)
    features reward = prepared at executed
  have hp : ZeroRankedState prepared := by
    rw [← preparedEq]
    exact zero_ranked_prepare state hz features reward hr
  have idle : ZeroRankedState (prepared.withPhase .idle) :=
    ⟨zero_skill_state_idle prepared hp.skills, hp.control,
      hp.metaController, hp.ranking, hp.gap⟩
  dsimp only at executed
  cases served : prepared.serve features with
  | some result =>
    simp only [served] at executed
    cases executed
    exact zero_ranked_serve prepared final hp features decision served
  | none =>
    have hierarchy : (!(researchProfile .ranked).usesHierarchy) = false := rfl
    simp only [served, hierarchy, Bool.false_eq_true, if_false] at executed
    split at executed
    · exact zero_ranked_boundary _ final idle selection features declared reward hr
        none decision executed
    · exact zero_ranked_boundary _ final idle selection features declared reward hr
        none decision executed
    · rename_i slot activation phase
      have potential := zero_skill_state_potential (prepared.withPhase .idle)
        idle.skills slot features declared
      simp only [potential, bind, Option.bind] at executed
      split at executed
      · rename_i next produced
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at executed
        rw [← executed.1]
        exact zero_ranked_continuing prepared hp slot activation phase features goal next
          produced reward hr
      · rename_i reason produced
        have closed := zero_ranked_close_active prepared hp slot activation phase reason
          features reward hr
        exact zero_ranked_boundary _ final closed.1 selection features declared reward hr
          _ decision executed

end AcornVerif.CurrentReplacement
