/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentPrefix
import AcornVerif.CurrentControl
import AcornVerif.CurrentRetirement
import AcornVerif.CurrentBackupBounds

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

end AcornVerif.CurrentReplacement
