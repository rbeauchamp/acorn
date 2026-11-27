import Regula.Contract
import Regula.Decision
import Acorn.Agreement
import Acorn.FeatureRanking
import Acorn.Host.AgentArguments
import Acorn.Host.AgentPrefix
import Acorn.Host.Ansi
import Acorn.Host.Baseline
import Acorn.Host.Campaign
import Acorn.Host.Certificate
import Acorn.Host.Checkpoint.Snapshot
import Acorn.Host.Cli
import Acorn.Host.Endurance
import Acorn.Handcrafted.Microduck
import Acorn.Host.Microduck.Bridge
import Acorn.Host.Microduck.Session
import Acorn.Host.Microduck.Wire
import Acorn.Host.Viewer.Admission
import Acorn.Host.Viewer.BrowserStore
import Acorn.Host.Viewer.ControlRequest
import Acorn.Host.Viewer.GoalProtocol
import Acorn.Host.Viewer.Line
import Acorn.Host.Viewer.Options
import Acorn.Host.Viewer.WireNumber
import Acorn.Host.Viewer.WorldMemory

namespace Acorn.Decisions
open Features Handcrafted

private theorem decides.{u, v} {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
    {f : α → ρ} (iff : ∀ x, accepts (f x) ↔ spec x) (holds : ∃ x, spec x)
    (fails : ∃ x, ¬spec x) : Regula.Decides accepts spec f :=
  .of_iff iff (holds.elim fun x satisfied => ⟨x, (iff x).mpr satisfied⟩)
    (fails.elim fun x unsatisfied => ⟨x, fun accepted => unsatisfied ((iff x).mp accepted)⟩)

private theorem accepts_iff_not.{u} {α : Type u} {refusal : Prop} {result : Option α}
    (refuses : result = none ↔ refusal) : result.isSome = true ↔ ¬refusal := by
  rw [Option.isSome_iff_ne_none]
  exact not_congr refuses

private theorem dite_isSome.{u} {α : Type u} {condition : Prop} [Decidable condition]
    (accept : condition → α) :
    (if holds : condition then some (accept holds) else none).isSome = true ↔ condition := by
  split <;> simp_all

def wide : Host.WorldConfig :=
  ⟨⟨0, ⟨2 ^ 63 - 1, by decide⟩, 1, 0, 0, 0, 0, ⟨0x3f800000⟩⟩, by decide, by decide⟩

def last : Host.Position := ⟨⟨2 ^ 63 - 1, by decide⟩, ⟨0, by decide⟩⟩

private theorem ite_isSome.{u} {α : Type u} {condition : Prop} [Decidable condition]
    (value : α) : (if condition then some value else none).isSome = true ↔ condition := by
  split <;> simp_all

private theorem present.{u, v} {α : Sort u} {payload : α → Type v} {spec : α → Prop}
    {f : ∀ x, Option (payload x)} (iff : ∀ x, (f x).isSome = true ↔ spec x)
    (holds : ∃ x, spec x) (fails : ∃ x, ¬spec x) :
    Regula.Decides (· = true) spec (Regula.Dependent.isSome f) :=
  decides iff holds fails

private theorem succeeds.{u, v, w} {α : Sort u} {ε : α → Type v} {payload : α → Type w}
    {spec : α → Prop} {f : ∀ x, Except (ε x) (payload x)}
    (iff : ∀ x, (f x).isOk = true ↔ spec x) (holds : ∃ x, spec x) (fails : ∃ x, ¬spec x) :
    Regula.Decides (· = true) spec (Regula.Dependent.isOk f) :=
  decides iff holds fails

private theorem reads.{u, v, w} {α : Sort u} {payload : α → Type v} {β : α → Sort w}
    {write : ∀ x, β x → Prop} {f : ∀ x, Option (payload x)}
    (complete : ∀ x (value : β x), write x value → (f x).isSome = true)
    (refused : ∃ x, (f x).isSome = false) :
    Regula.DecidesCompletely (· = true) (fun x => ∃ value : β x, write x value)
      (Regula.Dependent.isSome f) :=
  { complete := fun x ⟨value, written⟩ => complete x value written
    refused := refused.elim fun x none => ⟨x, fun some => by
      have some : (f x).isSome = true := some
      rw [none] at some
      exact Bool.false_ne_true some⟩ }

private theorem accepts_iff.{u} {α : Type u} {condition : Prop} [Decidable condition]
    {result : Option α} (refuses : result = none ↔ ¬condition) :
    result.isSome = true ↔ condition :=
  (accepts_iff_not refuses).trans Decidable.not_not

private theorem written.{u, v} {σ : Sort u} {β : Type v} {write : β → σ} {parse : σ → Option β}
    (roundtrip : ∀ x, parse (write x) = some x)
    (canonical : ∀ s x, parse s = some x → s = write x) (s : σ) :
    (parse s).isSome = true ↔ ∃ x, s = write x :=
  ⟨fun accepted =>
      (Option.isSome_iff_exists.mp accepted).elim fun x admitted => ⟨x, canonical s x admitted⟩,
    fun ⟨x, same⟩ => by rw [same, roundtrip]; rfl⟩

private theorem product_positive (count envelope : Nat) :
    0 < count * envelope ^ 2 ↔ 0 < count ∧ 0 < envelope := by
  constructor
  · intro positive
    refine ⟨Nat.pos_of_ne_zero fun zero => ?_, Nat.pos_of_ne_zero fun zero => ?_⟩
    · rw [zero, Nat.zero_mul] at positive
      exact absurd positive (Nat.lt_irrefl 0)
    · rw [zero] at positive
      exact absurd positive (Nat.lt_irrefl 0)
  · intro ⟨count, envelope⟩
    exact Nat.mul_pos count (Nat.pow_pos envelope)

private theorem envelope_positive (discount : Discount) :
    0 < Agreement.envelopeUnits discount := by
  cases discount <;> decide

def point : Interval32 := ⟨.zero, .zero, by decide, by decide, by decide⟩

def narrow : Dimension := ⟨1, by decide, ⟨0, rfl⟩, by decide⟩

def bank : Features.Config :=
  ⟨0, 1, by decide, ⟨1, by decide, by decide⟩, ⟨1, by decide, by decide, 0, .zero, .zero⟩⟩

def spark : Bonus := ⟨⟨⟨0x3f800000⟩, by decide⟩, by decide⟩

def chosen : Assignment bank := .selected ⟨0, by decide⟩ spark

def plan : Host.CampaignPlan 1 := ⟨1, by decide, 1, by decide, 1, 0, by decide⟩

def writer : Host.WritableCheckpoint :=
  (Host.WritableCheckpoint.admit ⟨""⟩ 2 .missing).get (by decide)

def ranked : AgentConstruction :=
  AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .expectation .learnThenAct

def double : Dimension := ⟨2, by decide, ⟨1, rfl⟩, by decide⟩

def pair : Features.Config :=
  ⟨1, 1, by decide, ⟨2, by decide, by decide⟩, ⟨1, by decide, by decide, 0, .zero, .zero⟩⟩

def split : WeightArray (.discounted .g99) double :=
  #v[⟨⟨.zero, by decide⟩⟩, ⟨⟨⟨0x3f800000⟩, by decide⟩⟩]

def aged : Progress pair :=
  ⟨1, 0, #v[⟨0, 0, .zero⟩, ⟨0, 0, ⟨⟨0x3f800000⟩, by decide⟩⟩], ⟨0, by decide⟩, 0, none,
    by decide, trivial⟩

def lifecycle {config : Features.Config} (progress : Progress config)
    (interests : Vector (Interest config) Acorn.FeatureConstants.skillCount) :
    Features.Lifecycle Host.patchShape ⟨1, by decide⟩ config .discounted narrow [] :=
  ⟨.restore _ progress, .initial _ _ _ _ interests⟩

def fresh (cap : UInt64) : Host.Attempt wide Unit (.survive 0) cap :=
  ⟨⟨(Host.World.empty wide).setGoal (.survive 0), (), {}, 0⟩, rfl, 0, .zero, .wait⟩

def level : PolicySnapshot metaCount := ⟨Vector.replicate _ .zero, declaredRate⟩

def resumable : FeatureProfile := ⟨.final, .perStep, .declared, .learned⟩

def primitive : FeatureProfile := ⟨.primitiveOnly, .perStep, .declared, .learned⟩

def construction (profile : FeatureProfile) : AgentConstruction :=
  ⟨profile, .discounted, .none, .learnThenAct, bank, narrow⟩

def blank : Host.Observation :=
  ⟨.replicate _ (.replicate _ ⟨0, 0, 0⟩), 0, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩

theorem binary32_nan : Regula.ExecutableContract Binary32.isNaN
    (Regula.Decides (· = true) (fun word : Binary32 => word.magnitude > 0x7f800000)) :=
  ⟨decides
    (fun word => by
      show word.isNaN = true ↔ _
      rw [Binary32.isNaN_eq_magnitude]
      exact decide_eq_true_iff)
    ⟨⟨0x7fc00000⟩, by decide⟩ ⟨.zero, by decide⟩⟩

theorem Binary32_isNaN_registered : Regula.RegisteredDecision @Binary32.isNaN := ⟨⟩

private theorem ordered32 (word : Binary32) :
    word.isNaN = false ↔ word.magnitude ≤ 0x7f800000 := by
  rw [Binary32.isNaN_eq_magnitude, decide_eq_false_iff_not, Nat.not_lt]

theorem binary32_zero : Regula.ExecutableContract Binary32.isZero
    (Regula.Decides (· = true) (fun word : Binary32 => word.key = 0)) :=
  ⟨decides
    (fun word => by
      show word.isZero = true ↔ _
      rw [Binary32.isZero_eq_key]
      exact decide_eq_true_iff)
    ⟨.zero, by decide⟩ ⟨⟨0x3f800000⟩, by decide⟩⟩

theorem Binary32_isZero_registered : Regula.RegisteredDecision @Binary32.isZero := ⟨⟩

theorem binary32_less : Regula.ExecutableContract Binary32.less (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary32 × Binary32 =>
        words.1.magnitude ≤ 0x7f800000 ∧ words.2.magnitude ≤ 0x7f800000 ∧
          words.1.key < words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.less words.2 = true ↔ _
      rw [Binary32.less_eq_key, ← ordered32, ← ordered32]
      simp [and_assoc])
    ⟨(.zero, ⟨0x3f800000⟩), by decide⟩ ⟨(.zero, .zero), by decide⟩⟩

theorem Binary32_less_registered : Regula.RegisteredDecision @Binary32.less := ⟨⟩

theorem binary32_less_or_equal : Regula.ExecutableContract Binary32.lessOrEqual (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary32 × Binary32 =>
        words.1.magnitude ≤ 0x7f800000 ∧ words.2.magnitude ≤ 0x7f800000 ∧
          words.1.key ≤ words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.lessOrEqual words.2 = true ↔ _
      rw [Binary32.lessOrEqual_eq_key, ← ordered32, ← ordered32]
      simp [and_assoc])
    ⟨(.zero, .zero), by decide⟩ ⟨(⟨0x3f800000⟩, .zero), by decide⟩⟩

theorem Binary32_lessOrEqual_registered : Regula.RegisteredDecision @Binary32.lessOrEqual := ⟨⟩

theorem binary32_equal : Regula.ExecutableContract Binary32.numericallyEqual (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary32 × Binary32 =>
        words.1.magnitude ≤ 0x7f800000 ∧ words.2.magnitude ≤ 0x7f800000 ∧
          words.1.key = words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.numericallyEqual words.2 = true ↔ _
      rw [Binary32.numericallyEqual_eq_key, ← ordered32, ← ordered32]
      simp [and_assoc])
    ⟨(.zero, .zero), by decide⟩ ⟨(⟨0x3f800000⟩, .zero), by decide⟩⟩

theorem Binary32_numericallyEqual_registered :
    Regula.RegisteredDecision @Binary32.numericallyEqual := ⟨⟩

theorem binary32_magnitude : Regula.ExecutableContract Binary32.magnitudeEq (fun test =>
    Regula.Decides (· = true)
      (fun input : Binary32 × UInt32 => input.1.magnitude = input.2.toNat)
      (Function.uncurry test)) :=
  ⟨decides
    (fun input => by
      show input.1.magnitudeEq input.2 = true ↔ _
      rw [Binary32.magnitudeEq_exact]
      exact beq_iff_eq)
    ⟨(.zero, 0), by decide⟩ ⟨(.zero, 1), by decide⟩⟩

theorem Binary32_magnitudeEq_registered : Regula.RegisteredDecision @Binary32.magnitudeEq := ⟨⟩

theorem binary64_nan : Regula.ExecutableContract Binary64.isNaN
    (Regula.Decides (· = true) (fun word : Binary64 => word.magnitude > 0x7ff0000000000000)) :=
  ⟨decides (fun _ => decide_eq_true_iff)
    ⟨⟨0x7ff8000000000000⟩, by decide⟩ ⟨⟨0⟩, by decide⟩⟩

theorem Binary64_isNaN_registered : Regula.RegisteredDecision @Binary64.isNaN := ⟨⟩

private theorem ordered64 (word : Binary64) :
    word.isNaN = false ↔ word.magnitude ≤ 0x7ff0000000000000 := by
  have classified : word.isNaN = true ↔ word.magnitude > 0x7ff0000000000000 :=
    decide_eq_true_iff
  rw [← Bool.not_eq_true, classified, Nat.not_lt]

theorem binary64_less : Regula.ExecutableContract Binary64.less (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary64 × Binary64 =>
        words.1.magnitude ≤ 0x7ff0000000000000 ∧ words.2.magnitude ≤ 0x7ff0000000000000 ∧
          words.1.key < words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.less words.2 = true ↔ _
      rw [Binary64.less_eq_key, ← ordered64, ← ordered64]
      simp [and_assoc])
    ⟨(⟨0⟩, ⟨0x3ff0000000000000⟩), by decide⟩ ⟨(⟨0⟩, ⟨0⟩), by decide⟩⟩

theorem Binary64_less_registered : Regula.RegisteredDecision @Binary64.less := ⟨⟩

theorem binary32_negative : Regula.ExecutableContract Binary32.negative
    (Regula.Decides (· = true) (fun word : Binary32 => word.bits &&& 0x80000000 ≠ 0)) :=
  ⟨decides (fun word => by simp [Binary32.negative]) ⟨⟨0x80000000⟩, by decide⟩
    ⟨.zero, by decide⟩⟩

theorem Binary32_negative_registered : Regula.RegisteredDecision @Binary32.negative := ⟨⟩

theorem interval_admit : Regula.ExecutableContract Interval32.admit (fun admit =>
    Regula.Decides (·.isSome = true)
      (fun endpoints : Binary32 × Binary32 =>
        endpoints.1.Finite ∧ endpoints.2.Finite ∧ endpoints.1.key ≤ endpoints.2.key)
      (Function.uncurry admit)) :=
  ⟨decides
    (fun endpoints => (accepts_iff_not
      (Interval32.interval_admit_refuses endpoints.1 endpoints.2)).trans Classical.not_not)
    ⟨(.zero, .zero), by decide⟩ ⟨(⟨0x7fc00000⟩, .zero), by decide⟩⟩

theorem Interval32_admit_registered : Regula.RegisteredDecision @Interval32.admit := ⟨⟩

theorem reward_rate_admit : Regula.ExecutableContract RewardRate.admit
    (Regula.Decides (·.isSome = true) rewardRange.Contains) :=
  ⟨decides
    (fun raw => (accepts_iff_not (Bounded32.admit_refuses rewardRange raw)).trans
      Classical.not_not)
    ⟨.zero, by decide⟩ ⟨⟨0x7fc00000⟩, by decide⟩⟩

theorem RewardRate_admit_registered : Regula.RegisteredDecision @RewardRate.admit := ⟨⟩

theorem key_positive : Regula.ExecutableContract Binary32.keyPositive
    (Regula.Decides (· = true) (fun word : Binary32 => 0 < word.key)) :=
  ⟨decides Binary32.keyPositive_exact ⟨⟨0x3f800000⟩, by decide⟩ ⟨.zero, by decide⟩⟩

theorem Binary32_keyPositive_registered : Regula.RegisteredDecision @Binary32.keyPositive := ⟨⟩

theorem bonus_admit : Regula.ExecutableContract Bonus.admit
    (Regula.Decides (·.isSome = true)
      (fun raw : Binary32 => Discount.g99.predictionRange.Contains raw ∧ 0 < raw.key)) :=
  ⟨decides
    (fun raw => by
      show (Bonus.admit raw).isSome = true ↔ _
      unfold Bonus.admit Prediction.admit Bounded32.admit
      by_cases legal : Discount.g99.predictionRange.Contains raw
      · by_cases positive : 0 < raw.key <;> simp [legal, positive, Bonus.ofWeight]
      · simp [legal])
    ⟨⟨0x3f800000⟩, by decide⟩ ⟨.zero, by decide⟩⟩

theorem Bonus_admit_registered : Regula.RegisteredDecision @Bonus.admit := ⟨⟩

theorem bonus_of_weight : Regula.ExecutableContract Bonus.ofWeight
    (Regula.Decides (·.isSome = true)
      (fun weight : Prediction .g99 => 0 < weight.value.key)) :=
  ⟨decides
    (fun weight => by
      show (Bonus.ofWeight weight).isSome = true ↔ _
      unfold Bonus.ofWeight
      split <;> simp_all)
    ⟨⟨⟨0x3f800000⟩, by decide⟩, by decide⟩ ⟨⟨.zero, by decide⟩, by decide⟩⟩

theorem Bonus_ofWeight_registered : Regula.RegisteredDecision @Bonus.ofWeight := ⟨⟩

theorem predictions_admit : Regula.ExecutableContract Predictions.admit
    (Regula.Decides (·.isSome = true)
      (fun values : List Binary32 => values.length ≤ Acorn.FeatureConstants.demonCount)) :=
  ⟨decides (fun _ => dite_isSome _) ⟨[], Nat.zero_le _⟩
    ⟨List.replicate (Acorn.FeatureConstants.demonCount + 1) .zero, by simp⟩⟩

theorem predictions_admit_value : Regula.ExecutableContract Predictions.admit
    (fun admit => ∀ values predictions, admit values = some predictions ↔
      predictions.values = values) :=
  ⟨fun values predictions => by
    constructor
    · intro accepted
      unfold Predictions.admit at accepted
      split at accepted
      · cases accepted
        rfl
      · cases accepted
    · rintro rfl
      unfold Predictions.admit
      exact dite_eq_left predictions.bounded⟩

theorem Predictions_admit_registered : Regula.RegisteredDecision @Predictions.admit := ⟨⟩

theorem unit_state_admit : Regula.ExecutableContract UnitState.admit
    (Regula.Decides (·.isSome = true)
      (fun raw : UnitWords => utilityRange.Contains raw.2.2)) :=
  ⟨decides
    (fun raw => by
      show (UnitState.admit raw).isSome = true ↔ _
      rw [UnitState.admit, Option.isSome_map]
      exact (accepts_iff_not (Bounded32.admit_refuses utilityRange raw.2.2)).trans
        Classical.not_not)
    ⟨(0, 0, .zero), by decide⟩ ⟨(0, 0, ⟨0x7fc00000⟩), by decide⟩⟩

theorem UnitState_admit_registered : Regula.RegisteredDecision @UnitState.admit := ⟨⟩

theorem clock_advance : Regula.ExecutableContract Word.advanceClock (fun advance =>
    Regula.Decides (·.isSome = true)
      (fun words : UInt64 × UInt64 => words.1.toNat + words.2.toNat < 2 ^ 64)
      (Function.uncurry advance)) :=
  ⟨decides
    (fun words => (accepts_iff_not (Word.clock_advance_refuses words.1 words.2)).trans
      Nat.not_le)
    ⟨(0, 0), by decide⟩ ⟨(0xffffffffffffffff, 1), by decide⟩⟩

theorem Word_advanceClock_registered : Regula.RegisteredDecision @Word.advanceClock := ⟨⟩

theorem ratio_admit : Regula.ExecutableContract Agreement.Ratio.admit (fun admit =>
    Regula.Decides (·.isSome = true)
      (fun parts : Nat × Nat => 0 < parts.2 ∧ parts.1 ≤ parts.2) (Function.uncurry admit)) :=
  ⟨decides
    (fun parts => by
      show (Agreement.Ratio.admit parts.1 parts.2).isSome = true ↔ _
      unfold Agreement.Ratio.admit
      by_cases positive : 0 < parts.2 <;> by_cases bounded : parts.1 ≤ parts.2 <;>
        simp [positive, bounded])
    ⟨(0, 1), by decide⟩ ⟨(0, 0), by decide⟩⟩

theorem Agreement_Ratio_admit_registered : Regula.RegisteredDecision @Agreement.Ratio.admit := ⟨⟩

open Handcrafted.FeatureProfile (Resumable)

private theorem resumable_iff (profile : FeatureProfile) :
    profile.checkpointSupported = true ↔ Resumable profile :=
  FeatureProfile.checkpoint_iff profile

theorem agent_construction_admit :
    Regula.ExecutableContract AgentConstruction.admit (fun admit =>
      Regula.Decides (·.isSome = true)
        (fun input : ((((((FeatureProfile × Criterion) × PlanningSelection) × StepOrder) ×
            UInt64) × UInt64) × Nat) × Nat =>
          0 < input.1.1.2.toNat ∧ 0 < input.1.2 ∧ input.1.2 ≤ 65535 ∧ input.2 < 32)
        (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry
          (Function.uncurry (Function.uncurry (Function.uncurry admit)))))))) :=
  ⟨decides
    (fun input => AgentConstruction.admit_iff input.1.1.1.1.1.1.1 input.1.1.1.1.1.1.2
      input.1.1.1.1.1.2 input.1.1.1.1.2 input.1.1.1.2 input.1.1.2 input.1.2 input.2)
    ⟨(((((((⟨.final, .perStep, .declared, .learned⟩, .discounted), .expectation),
        .learnThenAct), 0), 1), 1), 0),
      by decide⟩
    ⟨(((((((⟨.final, .perStep, .declared, .learned⟩, .discounted), .expectation),
        .learnThenAct), 0), 0), 1), 0),
      by decide⟩⟩

theorem AgentConstruction_admit_registered :
    Regula.RegisteredDecision @AgentConstruction.admit := ⟨⟩

theorem checkpoint_supported : Regula.ExecutableContract FeatureProfile.checkpointSupported
    (Regula.Decides (· = true) (fun profile : FeatureProfile =>
      profile.mode = .final ∧ profile.credit = .perStep ∧ profile.rate = .declared ∧
        profile.subtasks = .learned)) :=
  ⟨decides FeatureProfile.checkpoint_iff ⟨⟨.final, .perStep, .declared, .learned⟩, by decide⟩
    ⟨⟨.frozen, .perStep, .declared, .learned⟩, by decide⟩⟩

theorem FeatureProfile_checkpointSupported_registered :
    Regula.RegisteredDecision @FeatureProfile.checkpointSupported := ⟨⟩

theorem goal_admit : Regula.ExecutableContract Checkpoint.admitGoal
    (Regula.Decides (·.isSome = true) (fun words : Checkpoint.GoalWords =>
      words.2.1.toNat ≤ words.1.toNat ∧ (words.1 = 0 → words.2.2 = 0))) :=
  ⟨decides (fun _ => dite_isSome _) ⟨(0, 0, 0), by decide⟩ ⟨(0, 1, 0), by decide⟩⟩

theorem Checkpoint_admitGoal_registered : Regula.RegisteredDecision @Checkpoint.admitGoal := ⟨⟩

def HeaderMatches (input : AgentConstruction × Checkpoint.Header) : Prop :=
  ∃ gain : RewardRate, Checkpoint.HeaderAdmitted input.1 input.2 gain

private theorem admitHeader_isOk (construction : AgentConstruction) (header : Checkpoint.Header) :
    (Checkpoint.admitHeader construction header).isOk = true ↔
      HeaderMatches (construction, header) := by
  unfold HeaderMatches
  constructor
  · intro accepted
    cases admitted : Checkpoint.admitHeader construction header with
    | error refusal =>
      rw [admitted] at accepted
      exact absurd accepted Bool.false_ne_true
    | ok gain => exact ⟨gain, (Checkpoint.admitHeader_iff construction header gain).mp admitted⟩
  · rintro ⟨gain, specified⟩
    rw [(Checkpoint.admitHeader_iff construction header gain).mpr specified]
    rfl

theorem header_admit : Regula.ExecutableContract Checkpoint.admitHeader (fun admit =>
    Regula.Decides (·.isOk = true) HeaderMatches (Function.uncurry admit)) :=
  ⟨decides (fun input => admitHeader_isOk input.1 input.2)
    ⟨(AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .expectation .learnThenAct,
        ⟨Checkpoint.formatVersion, Acorn.FeatureConstants.defaultWeightSpace.toUInt32,
          Checkpoint.primaryCount.toUInt32, 0, 0, 0, .zero,
          Acorn.FeatureConstants.defaultTilings.toUInt64,
          Acorn.FeatureConstants.defaultImprintUnits.toUInt32, 1, 0⟩),
      (admitHeader_isOk _ _).mp (by decide)⟩
    ⟨(AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .expectation .learnThenAct,
        ⟨19, Acorn.FeatureConstants.defaultWeightSpace.toUInt32,
          Checkpoint.primaryCount.toUInt32, 0, 0, 0, .zero,
          Acorn.FeatureConstants.defaultTilings.toUInt64,
          Acorn.FeatureConstants.defaultImprintUnits.toUInt32, 1, 0⟩),
      fun ⟨_, specified⟩ => absurd specified.version (by decide)⟩⟩

theorem Checkpoint_admitHeader_registered : Regula.RegisteredDecision @Checkpoint.admitHeader := ⟨⟩

theorem nat_decode : Regula.ExecutableContract Checkpoint.decodeNat (fun decode =>
    Regula.Decides (·.isSome = true)
      (fun input : Nat × List UInt8 => ∃ value suffix, value < 256 ^ input.1 ∧
        input.2 = Checkpoint.encodeNat input.1 value ++ suffix)
      (Function.uncurry decode)) :=
  ⟨{ sound := fun input accepted => by
       obtain ⟨⟨value, rest⟩, decoded⟩ := Option.isSome_iff_exists.mp accepted
       exact ⟨value, rest, Checkpoint.decodeNat_bound _ _ _ _ decoded,
         Checkpoint.decodeNat_written _ _ _ _ decoded⟩
     accepted := ⟨(0, []), rfl⟩
     complete := fun input ⟨value, suffix, bound, written⟩ => by
       show (Checkpoint.decodeNat input.1 input.2).isSome = true
       rw [written, Checkpoint.nat_roundtrip _ _ bound]
       rfl
     refused := ⟨(1, []), by decide⟩ }⟩

theorem Checkpoint_decodeNat_registered : Regula.RegisteredDecision @Checkpoint.decodeNat := ⟨⟩

theorem writable_checkpoint_admit :
    Regula.ExecutableContract Host.WritableCheckpoint.admit (fun admit =>
      Regula.Decides (·.isSome = true)
        (fun input : (System.FilePath × UInt32) × Host.CheckpointAdmission =>
          input.2 ≠ .refused ∧ 0 < input.1.2.toNat)
        (Function.uncurry (Function.uncurry admit))) :=
  ⟨decides
    (fun ⟨⟨path, interval⟩, status⟩ => by
      show (Host.WritableCheckpoint.admit path interval status).isSome = true ↔
        status ≠ .refused ∧ 0 < interval.toNat
      cases status <;> by_cases positive : 0 < interval.toNat <;>
        simp [Host.WritableCheckpoint.admit, positive])
    ⟨((⟨""⟩, 1), .loaded), by decide⟩ ⟨((⟨""⟩, 1), .refused), by decide⟩⟩

theorem Host_WritableCheckpoint_admit_registered :
    Regula.RegisteredDecision @Host.WritableCheckpoint.admit := ⟨⟩

theorem profile_resumable : Regula.ExecutableContract Host.ResearchProfile.resumable
    (Regula.Decides (· = true) (fun profile : Host.ResearchProfile => profile = .ranked)) :=
  ⟨decides (fun profile => by cases profile <;> simp [Host.ResearchProfile.resumable])
    ⟨.ranked, rfl⟩ ⟨.primitive, by decide⟩⟩

theorem Host_ResearchProfile_resumable_registered :
    Regula.RegisteredDecision @Host.ResearchProfile.resumable := ⟨⟩

theorem coordinate_checked : Regula.ExecutableContract Host.Coordinate.checked
    (Regula.Decides (·.isSome = true)
      (fun value : Int => -(2 ^ 63) ≤ value ∧ value < 2 ^ 63)) :=
  ⟨decides
    (fun value => (accepts_iff_not (Host.Coordinate.checked_none value)).trans
      Classical.not_not)
    ⟨0, by decide⟩ ⟨2 ^ 63, by decide⟩⟩

theorem Host_Coordinate_checked_registered :
    Regula.RegisteredDecision @Host.Coordinate.checked := ⟨⟩

theorem is_past_last : Regula.ExecutableContract Host.isPastLast
    (Regula.Decides (· = true) Host.QuotientPastLast) :=
  ⟨decides
    Host.isPastLast_iff_units
    ⟨⟨0x5f000000⟩, (Host.isPastLast_iff_units _).mp (by decide)⟩
    ⟨⟨0⟩, fun h => absurd ((Host.isPastLast_iff_units _).mpr h) (by decide)⟩⟩

theorem Host_isPastLast_registered : Regula.RegisteredDecision @Host.isPastLast := ⟨⟩

theorem scale_admits_octave : Regula.ExecutableContract Host.scaleAdmitsOctave (fun admits =>
    Regula.Decides (· = true)
      (fun input : Host.Coordinate × Host.Coordinate × Binary32 =>
        ¬Host.QuotientPastLast ((Host.coordinateFloat input.1).div input.2.2) ∧
          ¬Host.QuotientPastLast ((Host.coordinateFloat input.2.1).div input.2.2))
      (fun input => admits input.1 input.2.1 input.2.2)) :=
  ⟨decides
    (fun input => Host.scaleAdmitsOctave_spec_iff input.1 input.2.1 input.2.2)
    ⟨(⟨-5, by decide⟩, ⟨5, by decide⟩, ⟨0x3f800000⟩),
      (Host.scaleAdmitsOctave_spec_iff _ _ _).mp (by decide)⟩
    ⟨(⟨-5, by decide⟩, ⟨5, by decide⟩, ⟨0⟩),
      fun h => absurd ((Host.scaleAdmitsOctave_spec_iff _ _ _).mpr h) (by decide)⟩⟩

theorem Host_scaleAdmitsOctave_registered :
    Regula.RegisteredDecision @Host.scaleAdmitsOctave := ⟨⟩

theorem scale_admits_range : Regula.ExecutableContract Host.scaleAdmitsRange (fun admits =>
    Regula.Decides (· = true)
      (fun input : Host.Coordinate × Host.Coordinate × Binary32 =>
        Host.ScaleAdmitsRange input.1 input.2.1 input.2.2)
      (fun input => admits input.1 input.2.1 input.2.2)) :=
  ⟨decides
    (fun input => Host.scaleAdmitsRange_spec_iff input.1 input.2.1 input.2.2)
    ⟨(⟨-5, by decide⟩, ⟨5, by decide⟩, ⟨0x3f800000⟩),
      (Host.scaleAdmitsRange_spec_iff _ _ _).mp (by decide)⟩
    ⟨(⟨-5, by decide⟩, ⟨5, by decide⟩, ⟨0⟩),
      fun h => absurd ((Host.scaleAdmitsRange_spec_iff _ _ _).mpr h) (by decide)⟩⟩

theorem Host_scaleAdmitsRange_registered :
    Regula.RegisteredDecision @Host.scaleAdmitsRange := ⟨⟩

theorem raw_world_config_admissible :
    Regula.ExecutableContract Host.RawWorldConfig.admissible
      (Regula.Decides (· = true) Host.RawWorldConfig.Admissible) :=
  ⟨decides
    Host.RawWorldConfig.admissible_spec_iff
    ⟨⟨0, ⟨1, by decide⟩, 8, 0, 0, 0, 0, ⟨0x42800000⟩⟩,
      (Host.RawWorldConfig.admissible_spec_iff _).mp (by decide)⟩
    ⟨⟨0, ⟨0, by decide⟩, 8, 0, 0, 0, 0, ⟨0x42800000⟩⟩,
      fun h => absurd ((Host.RawWorldConfig.admissible_spec_iff _).mpr h) (by decide)⟩⟩

theorem Host_RawWorldConfig_admissible_registered :
    Regula.RegisteredDecision @Host.RawWorldConfig.admissible := ⟨⟩

theorem world_config_admit : Regula.ExecutableContract Host.WorldConfig.admit
    (Regula.Decides (·.isOk = true) Host.RawWorldConfig.Admissible) :=
  ⟨decides
    (fun raw => (Host.WorldConfig.admit_isOk_iff raw).trans
      (Host.RawWorldConfig.admissible_spec_iff raw))
    ⟨⟨0, ⟨1, by decide⟩, 8, 0, 0, 0, 0, ⟨0x42800000⟩⟩,
      (Host.RawWorldConfig.admissible_spec_iff _).mp (by decide)⟩
    ⟨⟨0, ⟨0, by decide⟩, 8, 0, 0, 0, 0, ⟨0x42800000⟩⟩,
      fun h => absurd ((Host.RawWorldConfig.admissible_spec_iff _).mpr h) (by decide)⟩⟩

theorem Host_WorldConfig_admit_registered : Regula.RegisteredDecision @Host.WorldConfig.admit := ⟨⟩

theorem world_config_standard :
    Regula.ExecutableContract Host.WorldConfig.standard (fun standard =>
      Regula.Decides (·.isOk = true)
        (fun input : UInt64 × Host.Coordinate =>
          (Acorn.FeatureConstants.worldMinSide : Int) ≤ input.2.val ∧
            input.2.val ≤ (Acorn.FeatureConstants.worldMaxSide : Int))
        (Function.uncurry standard)) :=
  ⟨decides
    (fun input => by
      show (Host.WorldConfig.standard input.1 input.2).isOk = true ↔ _
      unfold Host.WorldConfig.standard
      by_cases low : input.2.val < Acorn.FeatureConstants.worldMinSide
      · simp [low, Except.isOk, Except.toBool] <;> omega
      · by_cases high : input.2.val > Acorn.FeatureConstants.worldMaxSide
        · simp [low, high, Except.isOk, Except.toBool] <;> omega
        · simp [low, high, Except.isOk, Except.toBool] <;> omega)
    ⟨(0, ⟨64, by decide⟩), by decide⟩ ⟨(0, ⟨63, by decide⟩), by decide⟩⟩

theorem Host_WorldConfig_standard_registered :
    Regula.RegisteredDecision @Host.WorldConfig.standard := ⟨⟩

theorem world_area : Regula.ExecutableContract Host.RawWorldConfig.area
    (Regula.Decides (·.isSome = true) (fun raw : Host.RawWorldConfig =>
      -(2 ^ 63) ≤ raw.side.val * raw.side.val ∧ raw.side.val * raw.side.val < 2 ^ 63)) :=
  ⟨decides (fun raw => coordinate_checked.evidence.iff (raw.side.val * raw.side.val))
    ⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide⟩
    ⟨⟨0, ⟨2 ^ 62, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide⟩⟩

theorem Host_RawWorldConfig_area_registered :
    Regula.RegisteredDecision @Host.RawWorldConfig.area := ⟨⟩

theorem energy_spend : Regula.ExecutableContract Host.Energy.spend (fun spend =>
    Regula.Decides (·.isSome = true)
      (fun input : Host.Energy × Nat => input.2 ≤ input.1.val) (Function.uncurry spend)) :=
  ⟨decides
    (fun input => by
      show (Host.Energy.spend input.1 input.2).isSome = true ↔ _
      unfold Host.Energy.spend
      split <;> simp_all)
    ⟨(Host.Energy.new 0, 0), Nat.zero_le _⟩ ⟨(Host.Energy.new 0, 1), by decide⟩⟩

theorem Host_Energy_spend_registered : Regula.RegisteredDecision @Host.Energy.spend := ⟨⟩

private theorem harvest_beq (action : Host.Action) :
    (action == .harvest) = true ↔ action = .harvest := by
  cases action <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun same => absurd same (by decide), fun same => nomatch same⟩

theorem raw_energy_cost : Regula.ExecutableContract Host.Action.rawEnergyCost (fun cost =>
    Regula.Decides (·.isSome = true)
      (fun input : Host.Action × UInt32 =>
        (input.1 = .harvest → Acorn.FeatureConstants.harvestCost * input.2.toNat < 2 ^ 32) ∧
          (input.1 ≠ .harvest → input.2.toNat < 2 ^ 32))
      (Function.uncurry cost)) :=
  ⟨decides
    (fun ⟨action, multiplier⟩ => by
      show (Host.Action.rawEnergyCost action multiplier).isSome = true ↔ _
      unfold Host.Action.rawEnergyCost
      dsimp only
      rw [ite_isSome]
      by_cases harvest : action = .harvest
      · rw [ite_eq_left ((harvest_beq action).mpr harvest)]
        exact ⟨fun fits => ⟨fun _ => fits, fun differs => absurd harvest differs⟩,
          fun both => both.1 harvest⟩
      · have test : ¬(action == .harvest) = true := fun same =>
          harvest ((harvest_beq action).mp same)
        rw [ite_eq_right test, Nat.one_mul]
        exact ⟨fun fits => ⟨fun same => absurd same harvest, fun _ => fits⟩,
          fun both => both.2 harvest⟩)
    ⟨(.wait, 0), by decide⟩ ⟨(.harvest, 0xffffffff), by decide⟩⟩

theorem Host_Action_rawEnergyCost_registered :
    Regula.RegisteredDecision @Host.Action.rawEnergyCost := ⟨⟩

theorem inventory_craft : Regula.ExecutableContract Host.Inventory.craft (fun craft =>
    Regula.Decides (·.isOk = true)
      (fun input : Host.Inventory × Host.Craftable =>
        ¬input.1.Owns input.2 ∧ input.2.recipe.1 ≤ input.1.wood.toNat ∧
          input.2.recipe.2 ≤ input.1.stone.toNat)
      (Function.uncurry craft)) :=
  ⟨decides
    (fun ⟨inventory, tool⟩ => by
      show (inventory.craft tool).isOk = true ↔ ¬inventory.Owns tool ∧
        tool.recipe.1 ≤ inventory.wood.toNat ∧ tool.recipe.2 ≤ inventory.stone.toNat
      rcases recipe : tool.recipe with ⟨wood, stone⟩
      by_cases owned : inventory.Owns tool
      · simp [Host.Inventory.craft, owned, Except.isOk, Except.toBool]
      · by_cases short : inventory.wood.toNat < wood
        · simp [Host.Inventory.craft, recipe, owned, short, Except.isOk, Except.toBool] <;>
            omega
        · by_cases shortStone : inventory.stone.toNat < stone
          · simp [Host.Inventory.craft, recipe, owned, short, shortStone, Except.isOk,
              Except.toBool] <;> omega
          · simp [Host.Inventory.craft, recipe, owned, short, shortStone, Except.isOk,
              Except.toBool] <;> omega)
    ⟨(⟨100, 100, 0, 0, false, false⟩, .axe), by decide⟩
    ⟨(⟨0, 0, 0, 0, true, false⟩, .axe), by decide⟩⟩

theorem Host_Inventory_craft_registered : Regula.RegisteredDecision @Host.Inventory.craft := ⟨⟩

theorem outcome_steps : Regula.ExecutableContract Host.addOutcomeSteps (fun add =>
    Regula.Decides (·.isOk = true)
      (fun input : UInt64 × Host.GoalOutcome => input.1.toNat + input.2.steps.toNat < 2 ^ 64)
      (Function.uncurry add)) :=
  ⟨decides
    (fun input => by
      show (Host.addOutcomeSteps input.1 input.2).isOk = true ↔ _
      have advance := clock_advance.evidence.iff (input.1, input.2.steps)
      unfold Host.addOutcomeSteps
      cases next : Word.advanceClock input.1 input.2.steps <;>
        simp_all [Function.uncurry, Except.isOk, Except.toBool])
    ⟨(0, ⟨0, 0, 0, 0, false, .zero, ⟨.zero, .zero, .zero⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩),
      by decide⟩
    ⟨(0xffffffffffffffff,
        ⟨0, 0, 0, 1, false, .zero, ⟨.zero, .zero, .zero⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩),
      by decide⟩⟩

theorem Host_addOutcomeSteps_registered : Regula.RegisteredDecision @Host.addOutcomeSteps := ⟨⟩

theorem tile_walkable : Regula.ExecutableContract Host.TileKind.walkable
    (Regula.Decides (· = true)
      (fun kind : Host.TileKind => kind ≠ .water ∧ kind ≠ .mountain)) :=
  ⟨decides (fun kind => by cases kind <;> simp [Host.TileKind.walkable])
    ⟨.grass, by decide⟩ ⟨.water, by decide⟩⟩

theorem Host_TileKind_walkable_registered : Regula.RegisteredDecision @Host.TileKind.walkable := ⟨⟩

theorem planning_parse : Regula.ExecutableContract PlanningSelection.parse
    (Regula.Decides (·.isSome = true)
      (fun text => ∃ selection, text = PlanningSelection.name selection)) :=
  ⟨.of_roundtrip (fun selection => (PlanningSelection.parse_accepted _ selection).mpr rfl)
    (fun text selection parsed =>
      ((PlanningSelection.parse_accepted text selection).mp parsed).symm)
    .expectation (unwritten := "") rfl⟩

theorem PlanningSelection_parse_registered :
    Regula.RegisteredDecision @PlanningSelection.parse := ⟨⟩

private theorem planningValue_isOk (text : String) :
    (Host.Cli.planningValue text).isOk = (PlanningSelection.parse text).isSome := by
  unfold Host.Cli.planningValue
  cases PlanningSelection.parse text <;> rfl

theorem planning_value : Regula.ExecutableContract Host.Cli.planningValue
    (Regula.Decides (·.isOk = true)
      (fun text => ∃ selection, text = PlanningSelection.name selection)) :=
  ⟨decides
    (fun text => by
      show (Host.Cli.planningValue text).isOk = true ↔ _
      rw [planningValue_isOk]
      exact planning_parse.evidence.iff text)
    planning_parse.evidence.toDecidesSoundly.satisfiable
    planning_parse.evidence.toDecidesCompletely.refutable⟩

theorem Host_Cli_planningValue_registered : Regula.RegisteredDecision @Host.Cli.planningValue := ⟨⟩

private theorem cliProfile_isOk (text : String) :
    (Host.Cli.profile text).isOk = true ↔ ∃ selected, Host.Cli.ProfileSpelled text selected := by
  cases parsed : Host.Cli.profile text with
  | ok selected =>
    exact ⟨fun _ => ⟨selected, (Host.Cli.profile_spelled text selected).mp parsed⟩, fun _ => rfl⟩
  | error refusal =>
    refine ⟨fun accepted => absurd accepted Bool.false_ne_true, fun ⟨selected, spelled⟩ => ?_⟩
    rw [(Host.Cli.profile_spelled text selected).mpr spelled] at parsed
    cases parsed

theorem cli_profile : Regula.ExecutableContract Host.Cli.profile
    (Regula.Decides (·.isOk = true)
      (fun text => ∃ selected, Host.Cli.ProfileSpelled text selected)) :=
  ⟨decides cliProfile_isOk ⟨"ranked", .ranked, .inl ⟨rfl, rfl⟩⟩
    ⟨"", fun ⟨_, spelled⟩ => by simp [Host.Cli.ProfileSpelled] at spelled⟩⟩

theorem Host_Cli_profile_registered : Regula.RegisteredDecision @Host.Cli.profile := ⟨⟩

private theorem value_accepts (arguments : List String) (wanted : String) :
    (Host.Cli.value arguments wanted).isOk = true ↔ ¬Host.Cli.Ends arguments wanted := by
  cases found : Host.Cli.value arguments wanted with
  | error refusal =>
    have ends := ((Host.Cli.value_missing arguments wanted refusal).mp found).1
    exact ⟨fun accepted => absurd accepted Bool.false_ne_true, fun follows => absurd ends follows⟩
  | ok result =>
    refine ⟨fun _ ends => ?_, fun _ => rfl⟩
    have refused := (Host.Cli.value_missing arguments wanted (.missing wanted)).mpr ⟨ends, rfl⟩
    rw [found] at refused
    cases refused

theorem planning_selection : Regula.ExecutableContract Host.Cli.planningSelection
    (Regula.Decides (·.isOk = true) (fun arguments : List String =>
      "--planning" ∉ arguments ∨
        ∃ selection,
          Host.Cli.Follows arguments "--planning" (PlanningSelection.name selection))) :=
  ⟨.of_iff
    (fun arguments => by
      show (Host.Cli.planningSelection arguments).isOk = true ↔ _
      have present := Host.Cli.value_follows arguments "--planning"
      rw [← Host.Cli.value_absent arguments "--planning"]
      cases found : Host.Cli.value arguments "--planning" with
      | error refusal =>
        have refused : (Host.Cli.planningSelection arguments).isOk = false := by
          simp [Host.Cli.planningSelection, found, Except.isOk, Except.toBool, bind, Except.bind]
        rw [refused]
        constructor
        · intro accepted
          cases accepted
        · rintro (absurd | ⟨selection, first⟩)
          · cases absurd
          · have provided := (present _).mpr first
            rw [found] at provided
            cases provided
      | ok text =>
        cases text with
        | none =>
          simp [Host.Cli.planningSelection_absent arguments found, Except.isOk, Except.toBool]
        | some text =>
          rw [Host.Cli.planningSelection_provided arguments text found, planningValue_isOk]
          constructor
          · intro accepted
            obtain ⟨selection, written⟩ := (planning_parse.evidence.iff text).mp accepted
            have first := (present text).mp found
            exact .inr ⟨selection, written ▸ first⟩
          · rintro (absurd | ⟨selection, first⟩)
            · cases absurd
            · have provided := (present _).mpr first
              rw [found] at provided
              have written : text = PlanningSelection.name selection := by simpa using provided
              exact (planning_parse.evidence.iff text).mpr ⟨selection, written⟩)
    ⟨[], by decide⟩ ⟨["--planning"], by decide⟩⟩

theorem Host_Cli_planningSelection_registered :
    Regula.RegisteredDecision @Host.Cli.planningSelection := ⟨⟩

private theorem stepOrderParse_isSome (text : String) :
    (StepOrder.parse text).isSome = true ↔ ∃ order, StepOrder.Spelled text order := by
  constructor
  · intro accepted
    cases parsed : StepOrder.parse text with
    | none =>
      rw [parsed] at accepted
      exact absurd accepted Bool.false_ne_true
    | some order => exact ⟨order, (StepOrder.parse_spelled text order).mp parsed⟩
  · rintro ⟨order, spelled⟩
    rw [(StepOrder.parse_spelled text order).mpr spelled]
    rfl

theorem step_order_parse : Regula.ExecutableContract StepOrder.parse
    (Regula.Decides (·.isSome = true) (fun text => ∃ order, StepOrder.Spelled text order)) :=
  ⟨decides stepOrderParse_isSome ⟨"act-then-learn", .actThenLearn, .inr (.inr ⟨rfl, rfl⟩)⟩
    ⟨"", fun specified => absurd ((stepOrderParse_isSome "").mpr specified) (by decide)⟩⟩

theorem StepOrder_parse_registered : Regula.RegisteredDecision @StepOrder.parse := ⟨⟩

private theorem stepOrderValue_isOk (text : String) :
    (Host.Cli.stepOrderValue text).isOk = (StepOrder.parse text).isSome := by
  unfold Host.Cli.stepOrderValue
  cases StepOrder.parse text <;> rfl

theorem step_order_value : Regula.ExecutableContract Host.Cli.stepOrderValue
    (Regula.Decides (·.isOk = true) (fun text => ∃ order, StepOrder.Spelled text order)) :=
  ⟨decides
    (fun text => by
      show (Host.Cli.stepOrderValue text).isOk = true ↔ _
      rw [stepOrderValue_isOk]
      exact step_order_parse.evidence.iff text)
    step_order_parse.evidence.toDecidesSoundly.satisfiable
    step_order_parse.evidence.toDecidesCompletely.refutable⟩

theorem Host_Cli_stepOrderValue_registered :
    Regula.RegisteredDecision @Host.Cli.stepOrderValue := ⟨⟩

private theorem stepOrder_isOk (arguments : List String) :
    (Host.Cli.stepOrder arguments).isOk = true ↔
      "--step-order" ∉ arguments ∨
        ∃ text order, Host.Cli.Follows arguments "--step-order" text ∧
          StepOrder.Spelled text order := by
  constructor
  · intro accepted
    cases admitted : Host.Cli.stepOrder arguments with
    | error refusal =>
      rw [admitted] at accepted
      exact absurd accepted Bool.false_ne_true
    | ok order =>
      rcases (Host.Cli.stepOrder_iff arguments order).mp admitted with ⟨absent, _⟩ |
        ⟨text, follows, spelled⟩
      · exact .inl absent
      · exact .inr ⟨text, order, follows, spelled⟩
  · rintro (absent | ⟨text, order, follows, spelled⟩)
    · rw [(Host.Cli.stepOrder_iff arguments .learnThenAct).mpr (.inl ⟨absent, rfl⟩)]
      rfl
    · rw [(Host.Cli.stepOrder_iff arguments order).mpr (.inr ⟨text, follows, spelled⟩)]
      rfl

theorem step_order : Regula.ExecutableContract Host.Cli.stepOrder
    (Regula.Decides (·.isOk = true) (fun arguments : List String =>
      "--step-order" ∉ arguments ∨
        ∃ text order, Host.Cli.Follows arguments "--step-order" text ∧
          StepOrder.Spelled text order)) :=
  ⟨decides stepOrder_isOk ⟨[], .inl (by decide)⟩
    ⟨["--step-order"], fun specified =>
      absurd ((stepOrder_isOk ["--step-order"]).mpr specified) (by decide)⟩⟩

theorem Host_Cli_stepOrder_registered : Regula.RegisteredDecision @Host.Cli.stepOrder := ⟨⟩

theorem pace_meets : Regula.ExecutableContract Pace.meets (fun meets =>
    Regula.Decides (· = true)
      (fun input : ((Pace × Instant) × Nat) × Instant =>
        input.1.1.1.index input.1.1.2 input.2 < input.1.2 + input.1.1.1.latency)
      (Function.uncurry (Function.uncurry (Function.uncurry meets)))) :=
  ⟨decides (fun input => Pace.meets_index input.1.1.1 input.1.1.2 input.1.2 input.2)
    ⟨(((⟨1, 1, by decide, by decide⟩, ⟨0⟩), 0), ⟨0⟩), by decide⟩
    ⟨(((⟨1, 1, by decide, by decide⟩, ⟨0⟩), 0), ⟨1⟩), by decide⟩⟩

theorem Pace_meets_registered : Regula.RegisteredDecision @Pace.meets := ⟨⟩

theorem microduck_outcome :
    Regula.ExecutableContract Host.Microduck.Action.outcome (fun outcome =>
      Regula.Decides
        (fun result : Host.Microduck.Outcome => result ≠ .refused ∧ result ≠ .unanswered)
        (fun input : ((Host.Microduck.Action × Bool) × Host.Microduck.Reply) × Bool =>
          input.1.2 = .accepted)
        (Function.uncurry (Function.uncurry (Function.uncurry outcome)))) :=
  ⟨decides
    (fun input =>
      Host.Microduck.Action.outcome_accepted input.1.1.1 input.1.1.2 input.1.2 input.2)
    ⟨(((.still, false), .accepted), true), by decide⟩
    ⟨(((.still, false), .pending), true), by decide⟩⟩

theorem Host_Microduck_Action_outcome_registered :
    Regula.RegisteredDecision @Host.Microduck.Action.outcome := ⟨⟩

theorem microduck_outcome_judged :
    Regula.ExecutableContract Host.Microduck.Action.outcome (fun outcome =>
      ∀ (action : Host.Microduck.Action) (sitting : Bool) (reply : Host.Microduck.Reply)
        (shown : Bool) (result : Host.Microduck.Outcome),
        outcome action sitting reply shown = result ↔
          action.Judged sitting reply shown result) :=
  ⟨Host.Microduck.Action.outcome_judged⟩

theorem microduck_upright :
    Regula.ExecutableContract Handcrafted.Microduck.upright (fun upright =>
      Regula.Decides (· = true)
        (fun state : Host.Microduck.State => (state.gravity.get 2).val < -967)
        upright) :=
  ⟨decides Handcrafted.Microduck.upright_iff
    ⟨⟨⟨0⟩, Vector.replicate 15 ⟨0, by decide⟩, none,
        #v[⟨0, by decide⟩, ⟨0, by decide⟩, ⟨-1000, by decide⟩],
        Vector.replicate 3 ⟨0, by decide⟩, ⟨0, by decide⟩, .stand, false, false, none,
        ⟨false, false, false, false⟩⟩, by decide⟩
    ⟨⟨⟨0⟩, Vector.replicate 15 ⟨0, by decide⟩, none, Vector.replicate 3 ⟨0, by decide⟩,
        Vector.replicate 3 ⟨0, by decide⟩, ⟨0, by decide⟩, .stand, false, false, none,
        ⟨false, false, false, false⟩⟩, by decide⟩⟩

theorem Handcrafted_Microduck_upright_registered :
    Regula.RegisteredDecision @Handcrafted.Microduck.upright := ⟨⟩

def standing : Host.Microduck.State :=
  ⟨⟨0⟩, Vector.replicate 15 ⟨0, by decide⟩, none,
    #v[⟨0, by decide⟩, ⟨0, by decide⟩, ⟨-1000, by decide⟩],
    Vector.replicate 3 ⟨0, by decide⟩, ⟨0, by decide⟩, .stand, false, false, none,
    ⟨false, false, false, false⟩⟩

def obstructed : Host.Microduck.Reading :=
  ⟨standing, some ⟨⟨0⟩, Vector.replicate 64 ⟨⟨100, by decide⟩, 5⟩⟩⟩

def unobstructed : Host.Microduck.Reading :=
  ⟨standing, some ⟨⟨0⟩, Vector.replicate 64 ⟨⟨0, by decide⟩, 255⟩⟩⟩

def unsighted : Host.Microduck.Reading := ⟨standing, none⟩

private theorem age_stamps (reading : Host.Microduck.Reading) (holds : Nat → Prop) :
    (∃ age, reading.age = some age ∧ holds age) ↔
      ∃ depth, reading.depth = some depth ∧
        holds (reading.state.taken.nanoseconds - depth.taken.nanoseconds) := by
  unfold Host.Microduck.Reading.age
  cases reading.depth with
  | none =>
    exact ⟨fun ⟨_, absent, _⟩ => (nomatch absent), fun ⟨_, absent, _⟩ => (nomatch absent)⟩
  | some depth => simp

theorem microduck_fresh :
    Regula.ExecutableContract Handcrafted.Microduck.fresh (fun fresh =>
      Regula.Decides (· = true)
        (fun reading : Host.Microduck.Reading =>
          ∃ depth, reading.depth = some depth ∧
            min ((reading.state.taken.nanoseconds - depth.taken.nanoseconds) /
                  Handcrafted.Microduck.Declared.stale)
                Handcrafted.Microduck.Declared.oldest <
              Handcrafted.Microduck.Declared.oldest)
        fresh) :=
  ⟨decides (fun reading => (Handcrafted.Microduck.fresh_level reading).trans
      (age_stamps reading fun age =>
        min (age / Handcrafted.Microduck.Declared.stale) Handcrafted.Microduck.Declared.oldest <
          Handcrafted.Microduck.Declared.oldest))
    ⟨unobstructed, _, rfl, by decide⟩
    ⟨unsighted, fun ⟨_, absent, _⟩ => nomatch absent⟩⟩

theorem Handcrafted_Microduck_fresh_registered :
    Regula.RegisteredDecision @Handcrafted.Microduck.fresh := ⟨⟩

def MicroduckNear (reading : Host.Microduck.Reading) : Prop :=
  (reading.state.gravity.get 2).val < -967 ∧
    (∃ depth, reading.depth = some depth ∧
      reading.state.taken.nanoseconds - depth.taken.nanoseconds <
        Handcrafted.Microduck.Declared.fresh) ∧
      ∃ position : Fin Handcrafted.Microduck.shape.inputs, position.val < 16 ∧
        ((Handcrafted.Microduck.symbols reading.depth).get position).toNat ≤ 3

def MicroduckClear (reading : Host.Microduck.Reading) : Prop :=
  (reading.state.gravity.get 2).val < -967 ∧
    (∃ depth, reading.depth = some depth ∧
      reading.state.taken.nanoseconds - depth.taken.nanoseconds <
        Handcrafted.Microduck.Declared.fresh) ∧
      ∀ position : Fin Handcrafted.Microduck.shape.inputs, position.val < 16 →
        (5 ≤ ((Handcrafted.Microduck.symbols reading.depth).get position).toNat ∧
            ((Handcrafted.Microduck.symbols reading.depth).get position).toNat < 0x1000) ∨
          ((Handcrafted.Microduck.symbols reading.depth).get position).toNat = 0x10FF

private theorem near_spec (reading : Host.Microduck.Reading) :
    Handcrafted.Microduck.near reading = true ↔ MicroduckNear reading :=
  (Handcrafted.Microduck.near_symbols reading).trans
    (and_congr Iff.rfl (and_congr (age_stamps reading (· < Handcrafted.Microduck.Declared.fresh))
      Iff.rfl))

private theorem clear_spec (reading : Host.Microduck.Reading) :
    Handcrafted.Microduck.clear reading = true ↔ MicroduckClear reading :=
  (Handcrafted.Microduck.clear_symbols reading).trans
    (and_congr Iff.rfl (and_congr (age_stamps reading (· < Handcrafted.Microduck.Declared.fresh))
      Iff.rfl))

private theorem obstructed_near : MicroduckNear obstructed :=
  (near_spec _).mp (by decide)

private theorem unobstructed_clear : MicroduckClear unobstructed :=
  (clear_spec _).mp (by decide)

theorem microduck_near :
    Regula.ExecutableContract Handcrafted.Microduck.near (fun near =>
      Regula.Decides (· = true) MicroduckNear near) :=
  ⟨decides near_spec
    ⟨obstructed, obstructed_near⟩
    ⟨unsighted, fun ⟨_, ⟨_, absent, _⟩, _⟩ => nomatch absent⟩⟩

theorem Handcrafted_Microduck_near_registered :
    Regula.RegisteredDecision @Handcrafted.Microduck.near := ⟨⟩

theorem microduck_clear :
    Regula.ExecutableContract Handcrafted.Microduck.clear (fun clear =>
      Regula.Decides (· = true) MicroduckClear clear) :=
  ⟨decides clear_spec
    ⟨unobstructed, unobstructed_clear⟩
    ⟨unsighted, fun ⟨_, ⟨_, absent, _⟩, _⟩ => nomatch absent⟩⟩

theorem Handcrafted_Microduck_clear_registered :
    Regula.RegisteredDecision @Handcrafted.Microduck.clear := ⟨⟩

private theorem unobstructed_far : ¬MicroduckNear unobstructed := fun close => by
  have wide := (clear_spec _).mpr unobstructed_clear
  rw [Handcrafted.Microduck.near_clear _ ((near_spec _).mpr close)]
    at wide
  exact Bool.false_ne_true wide

theorem microduck_achieved :
    Regula.ExecutableContract Handcrafted.Microduck.achieved (fun achieved =>
      Regula.Decides (· = true)
        (fun input : Bool × Host.Microduck.Reading => input.1 = true ∧ MicroduckNear input.2)
        (Function.uncurry achieved)) :=
  ⟨decides
    (fun input => (Handcrafted.Microduck.achieved_iff input.1 input.2).trans
      (and_congr Iff.rfl (near_spec input.2)))
    ⟨(true, obstructed), rfl, obstructed_near⟩
    ⟨(false, obstructed), fun ⟨armed, _⟩ => nomatch armed⟩⟩

theorem Handcrafted_Microduck_achieved_registered :
    Regula.RegisteredDecision @Handcrafted.Microduck.achieved := ⟨⟩

theorem microduck_arm :
    Regula.ExecutableContract Handcrafted.Microduck.arm (fun arm =>
      Regula.Decides (· = true)
        (fun input : Bool × Host.Microduck.Reading =>
          ¬MicroduckNear input.2 ∧ (input.1 = true ∨ MicroduckClear input.2))
        (Function.uncurry arm)) :=
  ⟨decides
    (fun input => by
      rcases input with ⟨armed, reading⟩
      change Handcrafted.Microduck.arm armed reading = true ↔
        ¬MicroduckNear reading ∧ (armed = true ∨ MicroduckClear reading)
      rw [show MicroduckNear reading ↔ Handcrafted.Microduck.near reading = true from
          (near_spec reading).symm,
        show MicroduckClear reading ↔ Handcrafted.Microduck.clear reading = true from
          (clear_spec reading).symm]
      unfold Handcrafted.Microduck.arm
      cases Handcrafted.Microduck.near reading <;>
        cases Handcrafted.Microduck.clear reading <;> cases armed <;> simp)
    ⟨(false, unobstructed), unobstructed_far, .inr unobstructed_clear⟩
    ⟨(true, obstructed), fun ⟨far, _⟩ => far obstructed_near⟩⟩

theorem Handcrafted_Microduck_arm_registered :
    Regula.RegisteredDecision @Handcrafted.Microduck.arm := ⟨⟩

theorem microduck_fitting :
    Regula.ExecutableContract Host.Microduck.fitting (fun fitting =>
      Regula.Decides (·.isSome = true)
        (fun input : Host.Microduck.State × Option Host.Microduck.Depth => ∃ frame,
          input.2 = some frame ∧ frame.taken.nanoseconds ≤ input.1.taken.nanoseconds)
        (Function.uncurry fitting)) :=
  ⟨decides
    (fun input => by
      rcases input with ⟨state, candidate⟩
      change (Host.Microduck.fitting state candidate).isSome = true ↔ _
      unfold Host.Microduck.fitting
      cases candidate with
      | none => simp
      | some frame =>
        by_cases early : frame.taken.nanoseconds ≤ state.taken.nanoseconds <;>
          simp [Option.filter, early])
    ⟨(standing, obstructed.depth), _, rfl, Nat.le_refl 0⟩
    ⟨(standing, none), fun ⟨_, absent, _⟩ => nomatch absent⟩⟩

theorem Host_Microduck_fitting_registered : Regula.RegisteredDecision @Host.Microduck.fitting := ⟨⟩

theorem microduck_state_frame :
    Regula.ExecutableContract Host.Microduck.Line.stateFrame (fun stateFrame =>
      Regula.Decides (·.isSome = true)
        (fun line : Host.Microduck.Line => ∃ frame, line = .state frame) stateFrame) :=
  ⟨decides (fun line => by cases line <;> simp [Host.Microduck.Line.stateFrame])
    ⟨.state standing, _, rfl⟩ ⟨.notice, fun ⟨_, same⟩ => nomatch same⟩⟩

theorem Host_Microduck_Line_stateFrame_registered :
    Regula.RegisteredDecision @Host.Microduck.Line.stateFrame := ⟨⟩

theorem microduck_depth_frame :
    Regula.ExecutableContract Host.Microduck.Line.depthFrame (fun depthFrame =>
      Regula.Decides (·.isSome = true)
        (fun line : Host.Microduck.Line => ∃ frame, line = .depth frame) depthFrame) :=
  ⟨decides (fun line => by cases line <;> simp [Host.Microduck.Line.depthFrame])
    ⟨.depth ⟨⟨0⟩, Vector.replicate 64 ⟨⟨100, by decide⟩, 5⟩⟩, _, rfl⟩
    ⟨.notice, fun ⟨_, same⟩ => nomatch same⟩⟩

theorem Host_Microduck_Line_depthFrame_registered :
    Regula.RegisteredDecision @Host.Microduck.Line.depthFrame := ⟨⟩

theorem json_scan :
    Regula.ExecutableContract Json.Numeral.scan (fun scan =>
      Regula.DecidesSoundly (fun found => found.isSome = true)
        (fun text : List Char => ∃ (parts : Json.Numeral) (rest : List Char),
          parts.Formed ∧ text = parts.chars ++ rest)
        scan) :=
  ⟨{ sound := fun text accepted => by
       obtain ⟨⟨parts, rest⟩, same⟩ := Option.isSome_iff_exists.mp accepted
       exact ⟨parts, rest, Json.Numeral.scan_formed same⟩
     accepted := ⟨['0'], by decide⟩ }⟩

theorem Json_Numeral_scan_registered : Regula.RegisteredDecision @Json.Numeral.scan := ⟨⟩

theorem json_numeral :
    Regula.ExecutableContract Json.Value.numeral
      (Regula.Decides (fun found => found.isSome = true) Json.Value.Numeric) :=
  ⟨decides
    (fun value => by
      constructor
      · intro found
        obtain ⟨parts, same⟩ := Option.isSome_iff_exists.mp found
        exact ⟨parts, (Json.Value.numeral_iff value parts).mp same⟩
      · rintro ⟨parts, formed⟩
        rw [(Json.Value.numeral_iff value parts).mpr formed]
        rfl)
    ⟨.number (String.ofList ['0']), ⟨false, ['0'], none, none⟩,
      ⟨Or.inl rfl, fun _ wrong => (nomatch wrong), fun _ wrong => (nomatch wrong)⟩, rfl⟩
    ⟨.null, fun ⟨_, _, wrong⟩ => nomatch wrong⟩⟩

theorem Json_Value_numeral_registered : Regula.RegisteredDecision @Json.Value.numeral := ⟨⟩

theorem microduck_decimal :
    Regula.ExecutableContract Host.Microduck.Decimal.read
      (Regula.Decides (fun found => found.isSome = true) Json.Value.Numeric) :=
  ⟨decides
    (fun value => by
      constructor
      · intro found
        obtain ⟨decimal, same⟩ := Option.isSome_iff_exists.mp found
        obtain ⟨parts, formed, spelling, _⟩ :=
          (Host.Microduck.Decimal.read_iff value decimal).mp same
        exact ⟨parts, formed, spelling⟩
      · rintro ⟨parts, formed, spelling⟩
        rw [(Host.Microduck.Decimal.read_iff value _).mpr ⟨parts, formed, spelling, rfl⟩]
        rfl)
    ⟨.number (String.ofList ['0']), ⟨false, ['0'], none, none⟩,
      ⟨Or.inl rfl, fun _ wrong => (nomatch wrong), fun _ wrong => (nomatch wrong)⟩, rfl⟩
    ⟨.null, fun ⟨_, _, wrong⟩ => nomatch wrong⟩⟩

theorem Host_Microduck_Decimal_read_registered :
    Regula.RegisteredDecision @Host.Microduck.Decimal.read := ⟨⟩

theorem json_member :
    Regula.ExecutableContract Json.Value.member (fun member =>
      Regula.Decides (fun found => found.isSome = true)
        (fun input : String × Json.Value =>
          ∃ inner : Json.Value, Json.Value.Member input.1 input.2 inner)
        (Function.uncurry member)) :=
  ⟨decides
    (fun input => by
      show (input.2.member input.1).isSome = true ↔ _
      constructor
      · intro found
        obtain ⟨inner, same⟩ := Option.isSome_iff_exists.mp found
        exact ⟨inner, (Json.Value.member_iff input.1 input.2 inner).mp same⟩
      · rintro ⟨inner, member⟩
        rw [(Json.Value.member_iff input.1 input.2 inner).mpr member]
        rfl)
    ⟨("a", .object [("a", .null)]), .null, [], [], rfl, fun _ wrong => (nomatch wrong)⟩
    ⟨("a", .null), fun ⟨_, _, _, wrong, _⟩ => nomatch wrong⟩⟩

theorem Json_Value_member_registered : Regula.RegisteredDecision @Json.Value.member := ⟨⟩

theorem microduck_state :
    Regula.ExecutableContract Host.Microduck.State.read
      (Regula.Decides (fun found => found.isSome = true)
        (fun json : Json.Value => ∃ state, Host.Microduck.State.Written json state)) :=
  ⟨decides
    (fun json => by
      constructor
      · intro found
        obtain ⟨state, same⟩ := Option.isSome_iff_exists.mp found
        exact ⟨state, (Host.Microduck.State.read_iff json state).mp same⟩
      · rintro ⟨state, written⟩
        rw [(Host.Microduck.State.read_iff json state).mpr written]
        rfl)
    ⟨.object [("t_ns", .number "0"), ("joints", .array (List.replicate 15 (.number "0"))),
        ("safety", .object [("gravity", .array (List.replicate 3 (.number "0"))),
          ("fallen", .bool false), ("limp", .bool false)]),
        ("imu", .object [("gyro", .array (List.replicate 3 (.number "0")))]),
        ("odom", .object [("position", .array (List.replicate 3 (.number "0")))]),
        ("policy", .string "stand"), ("move", .object [])], by
      have written : ∀ json : Json.Value, (Host.Microduck.State.read json).isSome = true →
          ∃ state, Host.Microduck.State.Written json state := fun json found =>
        (Option.isSome_iff_exists.mp found).imp fun state same =>
          (Host.Microduck.State.read_iff json state).mp same
      exact written _ (by decide)⟩
    ⟨.null, fun ⟨_, written⟩ => by
      obtain ⟨_, ⟨_, _, wrong, _⟩, _⟩ := written.taken
      exact nomatch wrong⟩⟩

theorem Host_Microduck_State_read_registered :
    Regula.RegisteredDecision @Host.Microduck.State.read := ⟨⟩

theorem microduck_depth :
    Regula.ExecutableContract Host.Microduck.Depth.read
      (Regula.Decides (fun found => found.isSome = true)
        (fun json : Json.Value => ∃ depth, Host.Microduck.Depth.Written json depth)) :=
  ⟨decides
    (fun json => by
      constructor
      · intro found
        obtain ⟨depth, same⟩ := Option.isSome_iff_exists.mp found
        exact ⟨depth, (Host.Microduck.Depth.read_iff json depth).mp same⟩
      · rintro ⟨depth, written⟩
        rw [(Host.Microduck.Depth.read_iff json depth).mpr written]
        rfl)
    ⟨.object [("rows", .number "8"), ("cols", .number "8"), ("t_ns", .number "0"),
        ("distance_mm", .array (List.replicate 64 (.number "0"))),
        ("status", .array (List.replicate 64 (.number "255")))], by
      have written : ∀ json : Json.Value, (Host.Microduck.Depth.read json).isSome = true →
          ∃ depth, Host.Microduck.Depth.Written json depth := fun json found =>
        (Option.isSome_iff_exists.mp found).imp fun depth same =>
          (Host.Microduck.Depth.read_iff json depth).mp same
      exact written _ (by decide)⟩
    ⟨.null, fun ⟨_, written⟩ => by
      obtain ⟨_, ⟨_, _, wrong, _⟩, _⟩ := written.taken
      exact nomatch wrong⟩⟩

theorem Host_Microduck_Depth_read_registered :
    Regula.RegisteredDecision @Host.Microduck.Depth.read := ⟨⟩

theorem microduck_line :
    Regula.ExecutableContract Host.Microduck.Line.read
      (Regula.Decides (fun line => line ≠ Host.Microduck.Line.invalid)
        (fun json : Json.Value =>
          (∃ method, Host.Microduck.Notified json method) ∨
            (∃ id accepted, Host.Microduck.Resulted json id accepted) ∨
            ∃ id, Host.Microduck.Faulted json id)) :=
  ⟨decides
    (fun json => by
      constructor
      · intro valid
        cases line : Host.Microduck.Line.read json with
        | state frame =>
          exact .inl ⟨_, ((Host.Microduck.Line.read_state json frame).mp line).1⟩
        | depth frame =>
          exact .inl ⟨_, ((Host.Microduck.Line.read_depth json frame).mp line).1⟩
        | unread stream =>
          exact .inl ⟨_, ((Host.Microduck.Line.read_unread json stream).mp line).1⟩
        | notice =>
          obtain ⟨method, noted, _⟩ := (Host.Microduck.Line.read_notice json).mp line
          exact .inl ⟨method, noted⟩
        | result id accepted =>
          exact .inr (.inl ⟨id, accepted,
            (Host.Microduck.Line.read_result json id accepted).mp line⟩)
        | fault id => exact .inr (.inr ⟨id, (Host.Microduck.Line.read_fault json id).mp line⟩)
        | invalid => exact absurd line valid
      · intro valid invalid
        obtain ⟨unnoted, unresulted, unfaulted⟩ :=
          (Host.Microduck.Line.read_invalid json).mp invalid
        rcases valid with ⟨method, noted⟩ | ⟨id, accepted, resulted⟩ | ⟨id, faulted⟩
        · exact unnoted method noted
        · exact unresulted id accepted resulted
        · exact unfaulted id faulted)
    ⟨.object [("jsonrpc", .string "2.0"), ("id", .number "0"),
        ("result", .object [("accepted", .bool true)])],
      .inr (.inl ⟨0, some true, (Host.Microduck.Line.read_result _ 0 (some true)).mp rfl⟩)⟩
    ⟨.null, by
      rintro (⟨_, ⟨_, ⟨_, _, wrong, _⟩, _⟩, _⟩ | ⟨_, _, ⟨_, ⟨_, _, wrong, _⟩, _⟩, _⟩ |
        ⟨_, ⟨_, ⟨_, _, wrong, _⟩, _⟩, _⟩) <;> exact nomatch wrong⟩⟩

theorem Host_Microduck_Line_read_registered :
    Regula.RegisteredDecision @Host.Microduck.Line.read := ⟨⟩

theorem microduck_line_read :
    Regula.ExecutableContract Host.Microduck.Line.read (fun read =>
      ∀ json : Json.Value,
        (∀ frame, read json = .state frame ↔
            Host.Microduck.Notified json "robot.state" ∧
              Host.Microduck.Within "params" Host.Microduck.State.Written json frame) ∧
          (∀ frame, read json = .depth frame ↔
            Host.Microduck.Notified json "tof.frame" ∧
              Host.Microduck.Within "params" Host.Microduck.Depth.Written json frame) ∧
          (∀ stream, read json = .unread stream ↔
            Host.Microduck.Notified json stream.method ∧ stream.Unwritten json) ∧
          (read json = .notice ↔
            ∃ method, Host.Microduck.Notified json method ∧ method ≠ "robot.state" ∧
              method ≠ "tof.frame") ∧
          (∀ id accepted, read json = .result id accepted ↔
            Host.Microduck.Resulted json id accepted) ∧
          (∀ id, read json = .fault id ↔ Host.Microduck.Faulted json id) ∧
          (read json = .invalid ↔
            (∀ method, ¬Host.Microduck.Notified json method) ∧
              (∀ id accepted, ¬Host.Microduck.Resulted json id accepted) ∧
                ∀ id, ¬Host.Microduck.Faulted json id)) :=
  ⟨fun json => ⟨Host.Microduck.Line.read_state json, Host.Microduck.Line.read_depth json,
    Host.Microduck.Line.read_unread json, Host.Microduck.Line.read_notice json,
    Host.Microduck.Line.read_result json, Host.Microduck.Line.read_fault json,
    Host.Microduck.Line.read_invalid json⟩⟩

theorem json_parse :
    Regula.ExecutableContract Json.parse
      (Regula.DecidesCompletely (fun result => result.isOk = true)
        (fun text : String => ∃ request : Json.Request,
          request.Simple ∧ text = String.ofList request.chars)) :=
  ⟨{ complete := fun text ⟨request, simple, same⟩ => by
       rw [same, Json.parse_request request simple]
       rfl
     refused := ⟨"", by decide +kernel⟩ }⟩

theorem Json_parse_registered : Regula.RegisteredDecision @Json.parse := ⟨⟩

theorem json_parse_value :
    Regula.ExecutableContract Json.parse (fun parse =>
      ∀ request : Json.Request, request.Simple →
        parse (String.ofList request.chars) = .ok request.value) :=
  ⟨Json.parse_request⟩

theorem json_parse_text :
    Regula.ExecutableContract Json.parse
      (Regula.DecidesSoundly (fun result => result.isOk = true)
        (fun text : String => ∃ v, Json.Grammar.Text text.toList v)) :=
  ⟨{ sound := fun text accepted => by
       cases parsed : Json.parse text with
       | ok v => exact ⟨v, Json.parse_sound text v parsed⟩
       | error refusal => rw [parsed] at accepted; exact absurd accepted Bool.false_ne_true
     accepted := ⟨"{}", by decide +kernel⟩ }⟩

theorem json_parse_text_value :
    Regula.ExecutableContract Json.parse (fun parse =>
      ∀ text v, parse text = .ok v → Json.Grammar.Text text.toList v) :=
  ⟨Json.parse_sound⟩

theorem microduck_shows :
    Regula.ExecutableContract Host.Microduck.Action.shows (fun shows =>
      Regula.Decides (· = true)
        (fun input : Host.Microduck.Action × Host.Microduck.Policy => input.1.Shown input.2)
        (Function.uncurry shows)) :=
  ⟨decides (fun input => Host.Microduck.Action.shows_iff input.1 input.2)
    ⟨(.still, .stand), .still⟩
    ⟨(.still, .walk), fun shown => nomatch shown⟩⟩

theorem Host_Microduck_Action_shows_registered :
    Regula.RegisteredDecision @Host.Microduck.Action.shows := ⟨⟩

theorem microduck_sense :
    Regula.ExecutableContract Host.Microduck.Idle.sense (fun sense =>
      ∀ (now : Instant) (idle : Host.Microduck.Idle),
        (sense now idle).isSome = true ↔
          (∃ frame, idle.calm.state = some frame) ∧
            idle.calm.cycle ≤ idle.calm.pace.index idle.calm.origin now) :=
  ⟨Host.Microduck.Idle.sense_admitted⟩

theorem microduck_release :
    Regula.ExecutableContract Host.Microduck.Awaiting.release (fun release =>
      ∀ (index : Nat) (now : Instant) (action : Host.Microduck.Action)
        (awaiting : Host.Microduck.Awaiting),
        (release index now action awaiting).isSome = true ↔
          index = awaiting.poised.index ∧
            (awaiting.poised.pace.boundary awaiting.poised.origin index).nanoseconds ≤
              now.nanoseconds) :=
  ⟨Host.Microduck.Awaiting.release_admitted⟩

structure BridgeTick where
  pace : Pace
  keep : Host.Microduck.Keep
  origin : Instant
  bridge : Host.Microduck.Bridge
  now : Instant

theorem bridge_tick : Regula.ExecutableContract Host.Microduck.Bridge.tick (fun tick =>
    Regula.DecidesSoundly
      (fun result : Host.Microduck.Bridge × Option Host.Microduck.Command =>
        result.2.isSome = true)
      (fun input : BridgeTick => input.bridge.action = .forward ∨
        input.bridge.action = .turnLeft ∨ input.bridge.action = .turnRight)
      (fun input : BridgeTick => tick input.pace input.keep input.origin input.bridge input.now)) :=
  ⟨{ sound := fun input sent => by
       obtain ⟨command, same⟩ := Option.isSome_iff_exists.mp sent
       have moving := (Host.Microduck.Bridge.tick_command _ _ _ _ _ command same).2.1
       revert moving
       cases input.bridge.action <;>
         simp [Host.Microduck.Action.velocity, Host.Microduck.Action.intent]
     accepted := ⟨⟨Host.Microduck.Declared.pace, Host.Microduck.Declared.keep, ⟨0⟩,
       ⟨.forward, false, 0, ⟨0⟩, ⟨0⟩⟩, ⟨100000000⟩⟩, by decide⟩ }⟩

theorem Host_Microduck_Bridge_tick_registered :
    Regula.RegisteredDecision @Host.Microduck.Bridge.tick := ⟨⟩

theorem bridge_tick_value : Regula.ExecutableContract Host.Microduck.Bridge.tick (fun tick =>
    (∀ (pace : Pace) (keep : Host.Microduck.Keep) (origin : Instant)
        (bridge : Host.Microduck.Bridge) (now : Instant),
      (∀ command, (tick pace keep origin bridge now).2 = some command →
        command = .move bridge.action.velocity ∧ bridge.action.velocity ≠ .zero ∧
          now.nanoseconds < (bridge.ends pace keep origin).nanoseconds ∧
          bridge.sent.nanoseconds + keep.resend ≤ now.nanoseconds) ∧
        ((bridge.ends pace keep origin).nanoseconds ≤ now.nanoseconds →
          tick pace keep origin bridge now = (bridge, none)) ∧
        (bridge.action.velocity ≠ .zero →
          now.nanoseconds < (bridge.ends pace keep origin).nanoseconds →
          bridge.sent.nanoseconds + keep.resend ≤ now.nanoseconds →
          tick pace keep origin bridge now =
            ({ bridge with sent := now }, some (.move bridge.action.velocity))) ∧
        (bridge.action.velocity ≠ .zero →
          now.nanoseconds < (bridge.ends pace keep origin).nanoseconds →
          (tick pace keep origin bridge now).1.Fresh keep now) ∧
        (tick pace keep origin bridge now).1.action = bridge.action ∧
        (tick pace keep origin bridge now).1.sitting = bridge.sitting ∧
        (tick pace keep origin bridge now).1.next pace keep origin =
          bridge.next pace keep origin ∧
        (tick pace keep origin bridge now).1.ends pace keep origin =
          bridge.ends pace keep origin) ∧
      (tick Host.Microduck.Declared.pace Host.Microduck.Declared.keep ⟨0⟩
        ⟨.forward, false, 0, ⟨0⟩, ⟨0⟩⟩ ⟨100000000⟩).2.isSome = true) :=
  ⟨⟨fun pace keep origin bridge now =>
      ⟨fun command sent =>
          have stated := Host.Microduck.Bridge.tick_command pace keep origin bridge now command sent
          ⟨stated.1, stated.2.1, stated.2.2, by
            unfold Host.Microduck.Bridge.tick at sent
            split at sent
            · rename_i due
              exact due.2.2
            · cases sent⟩,
        Host.Microduck.Bridge.tick_ended pace keep origin bridge now,
        fun moving inside due => ite_eq_left ⟨moving, inside, due⟩,
        Host.Microduck.Bridge.tick_fresh pace keep origin bridge now,
        Host.Microduck.Bridge.tick_keeps pace keep origin bridge now⟩,
    by decide⟩⟩

theorem cli_value : Regula.ExecutableContract Host.Cli.value (fun value =>
    Regula.Decides (·.isOk = true)
      (fun input : List String × String => ¬Host.Cli.Ends input.1 input.2)
      (Function.uncurry value)) :=
  ⟨.of_iff (fun input => value_accepts input.1 input.2) ⟨([], ""), by decide⟩
    ⟨([""], ""), by decide⟩⟩

theorem Host_Cli_value_registered : Regula.RegisteredDecision @Host.Cli.value := ⟨⟩

theorem cli_value_found : Regula.ExecutableContract Host.Cli.value (fun value =>
    ∀ (arguments : List String) (wanted : String),
      (value arguments wanted = .ok none ↔ wanted ∉ arguments) ∧
        ∀ text, value arguments wanted = .ok (some text) ↔
          Host.Cli.Follows arguments wanted text) :=
  ⟨fun arguments wanted =>
    ⟨Host.Cli.value_absent arguments wanted, Host.Cli.value_follows arguments wanted⟩⟩

theorem checkpoint_status_parse : Regula.ExecutableContract Host.CheckpointStatus.parse
    (Regula.Decides (·.isSome = true)
      (fun line => ∃ status : Host.CheckpointStatus, line = status.line)) :=
  ⟨.of_roundtrip Host.CheckpointStatus.roundtrip
    (fun line status parsed => by
      unfold Host.CheckpointStatus.parse at parsed
      split at parsed <;> cases parsed <;> rfl)
    .saved (unwritten := "") rfl⟩

theorem Host_CheckpointStatus_parse_registered :
    Regula.RegisteredDecision @Host.CheckpointStatus.parse := ⟨⟩

private theorem positional_cons (c : Char) (digits : List Char) :
    ((c :: digits).reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum =
      (c.toNat - 48) * 10 ^ digits.length +
        (digits.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum := by
  simp [List.zipIdx_append, Nat.add_comm]

private theorem digit_test (c : Char) :
    ('0' ≤ c && c ≤ '9') = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp [Char.le_def, UInt32.le_iff_toNat_le]

private theorem digits_fold (total : Nat) (digits : List Char) (n : Nat) :
    digits.foldlM (fun total c =>
        if '0' ≤ c && c ≤ '9' then some (10 * total + (c.toNat - 48)) else none) total =
        some n ↔
      (∀ c ∈ digits, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧
        n = total * 10 ^ digits.length +
          (digits.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum := by
  induction digits generalizing total with
  | nil =>
    simp only [List.foldlM_nil, List.length_nil, Nat.pow_zero, Nat.mul_one, List.reverse_nil,
      List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero, List.not_mem_nil,
      false_implies, implies_true, true_and, Option.pure_def, Option.some.injEq]
    exact ⟨Eq.symm, Eq.symm⟩
  | cons c more hold =>
    rw [List.foldlM_cons, positional_cons, List.forall_mem_cons]
    by_cases digit : ('0' ≤ c && c ≤ '9') = true
    · simp only [digit, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
      rw [hold, ← digit_test]
      have arith : (10 * total + (c.toNat - 48)) * 10 ^ more.length +
          (more.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum =
          total * 10 ^ (more.length + 1) + ((c.toNat - 48) * 10 ^ more.length +
            (more.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum) := by
        rw [Nat.add_mul, Nat.add_assoc, Nat.pow_succ, Nat.mul_comm 10 total, Nat.mul_assoc,
          Nat.mul_comm 10]
      simp [digit, arith, List.length_cons]
    · have refused : ('0' ≤ c && c ≤ '9') = false := by simpa using digit
      rw [← digit_test]
      simp [refused]

private theorem read_iff (text : String) (n : Nat) :
    Digits.read text = some n ↔ Digits.Spelled text n := by
  unfold Digits.read Digits.Spelled
  split
  · rename_i empty
    simp [empty]
  · rename_i head tail split
    rw [digits_fold, split]
    simp

private theorem natural_iff (text : String) (n : Nat) :
    Digits.natural text = some n ↔ Digits.Natural text n := by
  have notDigit : ¬ (48 ≤ ('+' : Char).toNat ∧ ('+' : Char).toNat ≤ 57) := by decide
  unfold Digits.natural
  split
  · rename_i digits plus
    rw [read_iff]
    unfold Digits.Spelled Digits.Natural
    rw [String.toList_ofList, plus]
    constructor
    · rintro ⟨nonempty, each, value⟩
      exact ⟨['+'], digits, .inr rfl, nonempty, each, rfl, value⟩
    · rintro ⟨sign, others, unsigned | signed, nonempty, each, spelled, value⟩
      · subst unsigned
        cases others with
        | nil => exact absurd rfl nonempty
        | cons c more =>
          simp only [List.nil_append, List.cons.injEq] at spelled
          exact absurd (spelled.1 ▸ each c (by simp)) notDigit
      · subst signed
        simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at spelled
        exact ⟨spelled ▸ nonempty, spelled ▸ each, spelled ▸ value⟩
  · rename_i unsigned
    rw [read_iff]
    unfold Digits.Spelled Digits.Natural
    constructor
    · rintro ⟨nonempty, each, value⟩
      exact ⟨[], text.toList, .inl rfl, nonempty, each, rfl, value⟩
    · rintro ⟨sign, digits, unsigned' | signed, nonempty, each, spelled, value⟩
      · subst unsigned'
        simp only [List.nil_append] at spelled
        exact ⟨spelled ▸ nonempty, spelled ▸ each, spelled ▸ value⟩
      · subst signed
        exact absurd spelled (unsigned digits)

theorem digits_read : Regula.ExecutableContract Digits.read
    (Regula.Decides (·.isSome = true) (fun text => ∃ n, Digits.Spelled text n)) :=
  ⟨decides
    (fun text => Option.isSome_iff_exists.trans (exists_congr fun n => read_iff text n))
    ⟨"0", 0, by simp, by simp, by simp⟩
    ⟨"", fun ⟨_, nonempty, _⟩ => nonempty (by simp)⟩⟩

theorem Digits_read_registered : Regula.RegisteredDecision @Digits.read := ⟨⟩

theorem digits_read_value : Regula.ExecutableContract Digits.read (fun read =>
    ∀ text n, read text = some n ↔ Digits.Spelled text n) :=
  ⟨read_iff⟩

theorem digits_natural : Regula.ExecutableContract Digits.natural
    (Regula.Decides (·.isSome = true) (fun text => ∃ n, Digits.Natural text n)) :=
  ⟨decides
    (fun text => Option.isSome_iff_exists.trans (exists_congr fun n => natural_iff text n))
    ⟨"0", 0, [], ['0'], .inl rfl, by simp, by simp, by simp, by simp⟩
    ⟨"", fun ⟨_, sign, digits, _, nonempty, _, spelled, _⟩ => nonempty (by simp_all)⟩⟩

theorem Digits_natural_registered : Regula.RegisteredDecision @Digits.natural := ⟨⟩

theorem digits_natural_value : Regula.ExecutableContract Digits.natural (fun natural =>
    ∀ text n, natural text = some n ↔ Digits.Natural text n) :=
  ⟨natural_iff⟩

private theorem integer_iff (text : String) (z : Int) :
    Digits.integer text = some z ↔ Digits.Integer text z := by
  have notDigit : ∀ c : Char, c = '+' ∨ c = '-' → ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57) := by
    rintro c (rfl | rfl) <;> decide
  unfold Digits.integer Digits.Integer
  split
  · rename_i digits minus
    simp only [Option.map_eq_some_iff, read_iff, Digits.Spelled, String.toList_ofList, minus]
    constructor
    · rintro ⟨n, ⟨nonempty, each, value⟩, rfl⟩
      exact ⟨['-'], digits, .inr (.inr rfl), nonempty, each, rfl, by subst value; simp⟩
    · rintro ⟨sign, others, unsigned | plus | signed, nonempty, each, spelled, value⟩
      · subst unsigned
        cases others with
        | nil => exact absurd rfl nonempty
        | cons c more =>
          simp only [List.nil_append, List.cons.injEq] at spelled
          exact absurd (spelled.1 ▸ each c (by simp)) (notDigit '-' (.inr rfl))
      · subst plus
        simp at spelled
      · subst signed
        simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at spelled
        subst spelled
        exact ⟨_, ⟨nonempty, each, rfl⟩, by subst value; simp⟩
  · rename_i digits plus
    simp only [Option.map_eq_some_iff, read_iff, Digits.Spelled, String.toList_ofList, plus]
    constructor
    · rintro ⟨n, ⟨nonempty, each, value⟩, rfl⟩
      exact ⟨['+'], digits, .inr (.inl rfl), nonempty, each, rfl, by subst value; simp⟩
    · rintro ⟨sign, others, unsigned | plus | signed, nonempty, each, spelled, value⟩
      · subst unsigned
        cases others with
        | nil => exact absurd rfl nonempty
        | cons c more =>
          simp only [List.nil_append, List.cons.injEq] at spelled
          exact absurd (spelled.1 ▸ each c (by simp)) (notDigit '+' (.inl rfl))
      · subst plus
        simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at spelled
        subst spelled
        exact ⟨_, ⟨nonempty, each, rfl⟩, by subst value; simp⟩
      · subst signed
        simp at spelled
  · rename_i minus plus
    simp only [Option.map_eq_some_iff, read_iff, Digits.Spelled]
    constructor
    · rintro ⟨n, ⟨nonempty, each, value⟩, rfl⟩
      exact ⟨[], text.toList, .inl rfl, nonempty, each, rfl, by subst value; simp⟩
    · rintro ⟨sign, digits, unsigned | signed | negated, nonempty, each, spelled, value⟩
      · subst unsigned
        simp only [List.nil_append] at spelled
        subst spelled
        exact ⟨_, ⟨nonempty, each, rfl⟩, by subst value; simp⟩
      · subst signed
        exact absurd spelled (plus digits)
      · subst negated
        exact absurd spelled (minus digits)

theorem digits_integer : Regula.ExecutableContract Digits.integer
    (Regula.Decides (·.isSome = true) (fun text => ∃ z, Digits.Integer text z)) :=
  ⟨decides
    (fun text => Option.isSome_iff_exists.trans (exists_congr fun z => integer_iff text z))
    ⟨"-0", 0, ['-'], ['0'], .inr (.inr rfl), by simp, by simp, by simp, by simp⟩
    ⟨"-", fun ⟨_, sign, digits, signs, nonempty, each, spelled, _⟩ => by
      rcases signs with rfl | rfl | rfl <;> cases digits <;> simp at nonempty spelled
      obtain ⟨rfl, rfl⟩ := spelled
      exact absurd (each '-' (by simp)) (by decide)⟩⟩

theorem Digits_integer_registered : Regula.RegisteredDecision @Digits.integer := ⟨⟩

theorem digits_integer_value : Regula.ExecutableContract Digits.integer (fun integer =>
    ∀ text z, integer text = some z ↔ Digits.Integer text z) :=
  ⟨integer_iff⟩

private theorem word_iff (text : String) (w : UInt64) :
    Host.AgentArguments.word text = some w ↔ Digits.Natural text w.toNat := by
  rw [← natural_iff]
  unfold Host.AgentArguments.word
  constructor
  · intro read
    obtain ⟨value, parsed, bounded⟩ := Option.bind_eq_some_iff.mp read
    by_cases below : value < 2 ^ 64
    · rw [ite_eq_left_iff.mpr (fun h => absurd below h), Option.some.injEq] at bounded
      rw [← bounded, parsed]
      simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' below]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h below)] at bounded
      cases bounded
  · intro parsed
    simp [parsed, w.toNat_lt]

private theorem word_isSome (text : String) :
    (Host.AgentArguments.word text).isSome = true ↔
      ∃ n, Digits.Natural text n ∧ n < 2 ^ 64 := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨w, read⟩
    exact ⟨w.toNat, (word_iff text w).mp read, w.toNat_lt⟩
  · rintro ⟨n, spelled, below⟩
    refine ⟨n.toUInt64, (word_iff text _).mpr ?_⟩
    simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' below] using spelled

private theorem words_iff (texts : List String) (words : List UInt64) :
    texts.mapM Host.AgentArguments.word = some words ↔
      words.length = texts.length ∧
        ∀ pair ∈ texts.zip words, Digits.Natural pair.1 pair.2.toNat := by
  induction texts generalizing words with
  | nil =>
    cases words <;> simp
  | cons text more hold =>
    cases words with
    | nil =>
      simp only [List.mapM_cons, List.length_nil, List.length_cons, Nat.right_eq_add,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, false_and, iff_false]
      intro read
      obtain ⟨w, -, rest⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨ws, -, done⟩ := Option.bind_eq_some_iff.mp rest
      cases done
    | cons w ws =>
      simp only [List.mapM_cons, List.length_cons, Nat.add_right_cancel_iff, List.zip_cons_cons,
        List.forall_mem_cons]
      constructor
      · intro read
        obtain ⟨w', first, rest⟩ := Option.bind_eq_some_iff.mp read
        obtain ⟨ws', others, done⟩ := Option.bind_eq_some_iff.mp rest
        cases done
        obtain ⟨length, each⟩ := (hold ws).mp others
        exact ⟨length, (word_iff text w).mp first, each⟩
      · rintro ⟨length, first, each⟩
        simp [(word_iff text w).mpr first, (hold ws).mpr ⟨length, each⟩]

private theorem profile_iff (mode credit rate subtasks : String) (profile : FeatureProfile) :
    Host.AgentArguments.profile mode credit rate subtasks = some profile ↔
      Host.AgentArguments.ProfileSpelled mode credit rate subtasks profile := by
  unfold Host.AgentArguments.profile Host.AgentArguments.ProfileSpelled
    Host.AgentArguments.ModeSpelled Host.AgentArguments.CreditSpelled
    Host.AgentArguments.RateSpelled Host.AgentArguments.SubtasksSpelled
  simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.pure_def]
  obtain ⟨m, c, r, t⟩ := profile
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all [eq_comm]

open Host.AgentArguments in
private theorem admit_spelled (arguments : List String) (admitted : DefaultConstruction)
    (words : List UInt64) (accepted : admit arguments = some (admitted, words)) :
    ∃ (seed exponent tilings units mode credit rate subtasks criterion planning : String)
      (texts : List String) (profile : FeatureProfile) (selected : Criterion)
      (selection : PlanningSelection) (s t : UInt64) (u e : Nat),
      arguments = [seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion,
        planning] ++ texts ∧
      ProfileSpelled mode credit rate subtasks profile ∧ CriterionSpelled criterion selected ∧
      planning = PlanningSelection.name selection ∧ Digits.Natural seed s.toNat ∧
      Digits.Natural tilings t.toNat ∧ Digits.Natural units u ∧ Digits.Natural exponent e ∧
      AgentConstruction.admit profile selected selection .learnThenAct s t u e =
        some admitted.construction ∧
      words.length = texts.length ∧
        ∀ pair ∈ texts.zip words, Digits.Natural pair.1 pair.2.toNat := by
  unfold admit at accepted
  split at accepted
  · rename_i seed exponent tilings units mode credit rate subtasks criterion planning texts
    obtain ⟨profile, profiled, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    split at accepted <;>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at accepted
    all_goals
      obtain ⟨selection, planned, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨s, seeded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨t, tiled, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨u, banked, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨e, sized, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      split at accepted
      · cases accepted
      · rename_i construction made
        obtain ⟨ws, read, done⟩ := Option.bind_eq_some_iff.mp accepted
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at done
        obtain ⟨rfl, rfl⟩ := done
        exact ⟨_, _, _, _, _, _, _, _, _, _, texts, profile, _, selection, s, t, u, e, rfl,
          (profile_iff _ _ _ _ _).mp profiled, by simp [CriterionSpelled],
          (PlanningSelection.parse_accepted _ _).mp planned, (word_iff _ _).mp seeded,
          (word_iff _ _).mp tiled, (natural_iff _ _).mp banked,
          (natural_iff _ _).mp sized, made, (words_iff _ _).mp read⟩
  · cases accepted

private theorem words_isSome (texts : List String) :
    (texts.mapM Host.AgentArguments.word).isSome = true ↔
      ∀ text ∈ texts, ∃ n, Digits.Natural text n ∧ n < 2 ^ 64 := by
  have each : ∀ texts : List String, (texts.mapM Host.AgentArguments.word).isSome = true ↔
      ∀ text ∈ texts, (Host.AgentArguments.word text).isSome = true := fun texts => by
    induction texts with
    | nil => simp
    | cons text more hold =>
      rw [List.forall_mem_cons, ← hold, List.mapM_cons]
      cases Host.AgentArguments.word text <;> cases List.mapM Host.AgentArguments.word more <;>
        simp
  rw [each]
  exact forall₂_congr fun text _ => word_isSome text

open Host.AgentArguments in
private theorem admit_isSome (arguments : List String) :
    (admit arguments).isSome = true ↔ Admitted arguments := by
  constructor
  · intro accepted
    obtain ⟨⟨admitted, words⟩, read⟩ := Option.isSome_iff_exists.mp accepted
    obtain ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
      texts, profile, selected, selection, s, t, u, e, rfl, profiled, criterioned, planned,
      seeded, tiled, banked, sized, made, length, each⟩ :=
      admit_spelled arguments admitted words read
    obtain ⟨positive, occupied, bounded, small⟩ :=
      (AgentConstruction.admit_iff profile selected selection .learnThenAct s t u e).mp
        (by rw [made]; rfl)
    refine ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
      texts, rfl, ⟨profile, profiled⟩, ⟨selected, criterioned⟩, ⟨selection, planned⟩,
      ⟨_, seeded, s.toNat_lt⟩, ⟨_, tiled, positive, t.toNat_lt⟩, ⟨u, banked, occupied, bounded⟩,
      ⟨e, sized, small⟩, fun text mem => ?_⟩
    obtain ⟨i, within, rfl⟩ := List.getElem_of_mem mem
    have paired := List.getElem_mem (h := (by simp [length, within] : i < (texts.zip words).length))
    exact ⟨_, by simpa using each _ paired, (words[i]'(length ▸ within)).toNat_lt⟩
  · rintro ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
      texts, rfl, ⟨profile, profiled⟩, ⟨selected, criterioned⟩, ⟨selection, planned⟩,
      ⟨s, seeded, sb⟩, ⟨t, tiled, tp, tb⟩, ⟨u, banked, up, ub⟩, ⟨e, sized, eb⟩, each⟩
    have seedRead : word seed = some s.toUInt64 :=
      (word_iff _ _).mpr (by simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' sb] using seeded)
    have tilingsRead : word tilings = some t.toUInt64 :=
      (word_iff _ _).mpr (by simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' tb] using tiled)
    obtain ⟨construction, made⟩ := Option.isSome_iff_exists.mp
      ((AgentConstruction.admit_iff profile selected selection .learnThenAct s.toUInt64
        t.toUInt64 u e).mpr
        ⟨by simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' tb] using tp, up, ub, eb⟩)
    obtain ⟨ws, read⟩ := Option.isSome_iff_exists.mp ((words_isSome texts).mpr each)
    unfold admit
    rcases criterioned with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [List.cons_append, (profile_iff _ _ _ _ _).mpr profiled,
        (PlanningSelection.parse_accepted _ _).mpr planned, seedRead, tilingsRead,
        (natural_iff _ _).mpr banked, (natural_iff _ _).mpr sized, Option.bind_eq_bind,
        Option.bind_some] <;>
      split <;> simp_all

private theorem natural_digit (text : String) (n : Nat) (c : Char) (spelled : text.toList = [c])
    (code : c.toNat = 48 + n) (small : n < 10) : Digits.Natural text n :=
  ⟨[], [c], .inl rfl, by simp,
    fun d mem => by simp only [List.mem_singleton] at mem; subst mem; omega, by simp [spelled],
    by simp [code]⟩

theorem agent_arguments_admit : Regula.ExecutableContract Host.AgentArguments.admit
    (Regula.Decides (·.isSome = true) Host.AgentArguments.Admitted) :=
  ⟨decides admit_isSome
    ⟨["0", "0", "1", "1", "final", "per-step", "declared", "learned", "discounted",
        "expectation"],
      ⟨"0", "0", "1", "1", "final", "per-step", "declared", "learned", "discounted",
        "expectation", [], rfl, ⟨⟨.final, .perStep, .declared, .learned⟩, .inl ⟨rfl, rfl⟩,
          .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩⟩, ⟨.discounted, .inl ⟨rfl, rfl⟩⟩,
        ⟨.expectation, rfl⟩, ⟨0, natural_digit "0" 0 '0' (by simp) rfl (by decide), by decide⟩,
        ⟨1, natural_digit "1" 1 '1' (by simp) rfl (by decide), by decide, by decide⟩,
        ⟨1, natural_digit "1" 1 '1' (by simp) rfl (by decide), by decide, by decide⟩,
        ⟨0, natural_digit "0" 0 '0' (by simp) rfl (by decide), by decide⟩, by simp⟩⟩
    ⟨[], fun ⟨_, _, _, _, _, _, _, _, _, _, _, spelled, _⟩ => by simp at spelled⟩⟩

theorem Host_AgentArguments_admit_registered :
    Regula.RegisteredDecision @Host.AgentArguments.admit := ⟨⟩

private theorem admit_fields (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (order : StepOrder) (seed tilings : UInt64)
    (units exponent : Nat) (construction : AgentConstruction) :
    AgentConstruction.admit profile criterion planning order seed tilings units exponent =
        some construction ↔
      construction.profile = profile ∧ construction.criterion = criterion ∧
        construction.planning = planning ∧ construction.order = order ∧
        construction.config.seed = seed ∧ construction.config.tilings = tilings ∧
        construction.config.units.count = units ∧ construction.config.tester = declaredTester ∧
        construction.dimension.capacity = 2 ^ exponent := by
  constructor
  · intro admitted
    unfold AgentConstruction.admit at admitted
    split at admitted
    · split at admitted
      · split at admitted
        · cases admitted
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · cases admitted
      · cases admitted
    · cases admitted
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, tested, sized⟩
    obtain ⟨profile, criterion, planning, order, ⟨seed, tilings, positive,
      ⟨units, occupied, bounded⟩, tester⟩, ⟨capacity, nonzero, power, below⟩⟩ := construction
    dsimp only at tested sized ⊢
    subst tested sized
    have small : exponent < 32 := (Nat.pow_lt_pow_iff_right (by decide)).mp below
    unfold AgentConstruction.admit
    rw [dite_eq_left positive, dite_eq_left ⟨occupied, bounded⟩, dite_eq_left small]

open Host.AgentArguments in
private theorem admit_constructs (arguments : List String) (admitted : DefaultConstruction)
    (words : List UInt64) (accepted : admit arguments = some (admitted, words)) :
    Constructs arguments admitted.construction words := by
  obtain ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
    texts, profile, selected, selection, s, t, u, e, rfl, profiled, criterioned, planned,
    seeded, tiled, banked, sized, made, length, each⟩ :=
    admit_spelled arguments admitted words accepted
  obtain ⟨rfl, rfl, rfl, ordered, rfl, rfl, rfl, tested, capacity⟩ :=
    (admit_fields profile selected selection .learnThenAct s t u e admitted.construction).mp made
  exact ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
    texts, e, rfl, profiled, criterioned, planned, ordered, seeded, tiled, banked, sized,
    capacity, tested, length, each⟩

open Host.AgentArguments in
private theorem constructs_admit (arguments : List String) (construction : AgentConstruction)
    (default : construction.order = .learnThenAct) (words : List UInt64)
    (spelled : Constructs arguments construction words) :
    admit arguments = some (⟨construction, default⟩, words) := by
  obtain ⟨seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion, planning,
    texts, e, rfl, profiled, criterioned, planned, -, seeded, tiled, banked, sized, capacity,
    tested, length, each⟩ := spelled
  have made := (admit_fields construction.profile construction.criterion construction.planning
    .learnThenAct construction.config.seed construction.config.tilings
    construction.config.units.count e construction).mpr
      ⟨rfl, rfl, rfl, default, rfl, rfl, rfl, tested, capacity⟩
  have read := (words_iff texts words).mpr ⟨length, each⟩
  unfold admit
  rcases criterioned with ⟨rfl, chosen⟩ | ⟨rfl, chosen⟩ <;> rw [chosen] at made <;>
    simp only [List.cons_append, (profile_iff _ _ _ _ _).mpr profiled,
      (PlanningSelection.parse_accepted _ _).mpr planned, (word_iff _ _).mpr seeded,
      (word_iff _ _).mpr tiled, (natural_iff _ _).mpr banked, (natural_iff _ _).mpr sized,
      Option.bind_eq_bind, Option.bind_some] <;>
    split <;> simp_all

theorem agent_arguments_admit_value : Regula.ExecutableContract Host.AgentArguments.admit
    (fun admit => ∀ arguments admitted words, admit arguments = some (admitted, words) ↔
      Host.AgentArguments.Constructs arguments admitted.construction words) :=
  ⟨fun arguments admitted words => ⟨admit_constructs arguments admitted words,
    constructs_admit arguments admitted.construction admitted.default words⟩⟩

theorem agent_arguments_constructs_unique (arguments : List String)
    (first second : DefaultConstruction) (words others : List UInt64)
    (spelled : Host.AgentArguments.Constructs arguments first.construction words)
    (respelled : Host.AgentArguments.Constructs arguments second.construction others) :
    first = second ∧ words = others := by
  have one := constructs_admit arguments first.construction first.default words spelled
  have two := constructs_admit arguments second.construction second.default others respelled
  rw [one, Option.some.injEq, Prod.mk.injEq] at two
  exact two

theorem region_member : Regula.ExecutableContract Host.inRegion (fun test =>
    Regula.Decides (· = true)
      (fun input : List Host.Position × Host.Position => input.2 ∈ input.1)
      (Function.uncurry test)) :=
  ⟨decides (fun input => by simp [Function.uncurry, Host.inRegion])
    ⟨([⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩], ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩),
      List.mem_singleton.mpr rfl⟩
    ⟨([], ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩), List.not_mem_nil⟩⟩

theorem Host_inRegion_registered : Regula.RegisteredDecision @Host.inRegion := ⟨⟩

theorem box_member : Regula.ExecutableContract Host.inBox (fun test =>
    Regula.Decides (· = true)
      (fun input : Host.WorldConfig × Host.Position =>
        (0 ≤ input.2.x.val ∧ input.2.x.val < input.1.side) ∧
          (0 ≤ input.2.y.val ∧ input.2.y.val < input.1.side))
      (Function.uncurry test)) :=
  ⟨decides (fun input => Host.inBox_iff input.1 input.2)
    ⟨(⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩,
        ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩), by decide⟩
    ⟨(⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩,
        ⟨⟨-1, by decide⟩, ⟨0, by decide⟩⟩), by decide⟩⟩

theorem Host_inBox_registered : Regula.RegisteredDecision @Host.inBox := ⟨⟩

theorem region_covers : Regula.ExecutableContract Host.covered (fun test =>
    Regula.Decides (· = true)
      (fun input : (Host.WorldConfig × List Host.Position) × Option Host.Position =>
        ∀ tile, input.2 = some tile → tile ∈ input.1.2 ∨ ¬Host.InBox input.1.1 tile)
      (Function.uncurry (Function.uncurry test))) :=
  ⟨decides
    (fun ⟨⟨config, cells⟩, candidate⟩ => by
      cases candidate with
      | none => simp [Function.uncurry, Host.covered]
      | some tile =>
        simp [Function.uncurry, Host.covered, Host.inRegion, ← Host.inBox_iff])
    ⟨((⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩, []), none),
      fun _ absent => nomatch absent⟩
    ⟨((⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩, []),
        some ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩),
      fun covers =>
        (covers _ rfl).elim List.not_mem_nil (fun outside => absurd outside (by decide))⟩⟩

theorem Host_covered_registered : Regula.RegisteredDecision @Host.covered := ⟨⟩

theorem tile_impassable : Regula.ExecutableContract Host.impassable (fun test =>
    Regula.Decides (· = true)
      (fun input : (Host.WorldConfig × Bool) × Host.Position =>
        Host.terrain input.2 input.1.1.raw.seed input.1.1.raw.baseScale = .ok .mountain ∨
          (Host.terrain input.2 input.1.1.raw.seed input.1.1.raw.baseScale = .ok .water ∧
            input.1.2 = false))
      (Function.uncurry (Function.uncurry test))) :=
  ⟨.of_iff
    (fun ⟨⟨config, boat⟩, tile⟩ => by
      show Host.impassable config boat tile = true ↔ _
      unfold Host.impassable
      cases Host.terrain tile config.raw.seed config.raw.baseScale with
      | error refusal => simp
      | ok kind => cases kind <;> simp)
    ⟨((wide, false), ⟨⟨15, by decide⟩, ⟨0, by decide⟩⟩), by decide +kernel⟩
    ⟨((wide, true), last), by decide +kernel⟩⟩

theorem Host_impassable_registered : Regula.RegisteredDecision @Host.impassable := ⟨⟩

open Host.Viewer

theorem goal_kind_decode : Regula.ExecutableContract decodeGoalKind
    (Regula.Decides (·.isSome = true) (fun code => ∃ kind : GoalKind, code = kind.code)) :=
  ⟨.of_roundtrip goalKind_roundtrip
    (fun _ _ decoded => by simpa using List.find?_some decoded)
    none (unwritten := 5) rfl⟩

theorem decodeGoalKind_registered : Regula.RegisteredDecision @decodeGoalKind := ⟨⟩

theorem goal_item_decode : Regula.ExecutableContract decodeGoalItem
    (Regula.Decides (·.isSome = true) (fun code => ∃ item : GoalItem, code = item.code)) :=
  ⟨.of_roundtrip goalItem_roundtrip
    (fun _ _ decoded => by simpa using List.find?_some decoded)
    none (unwritten := 1000) rfl⟩

theorem decodeGoalItem_registered : Regula.RegisteredDecision @decodeGoalItem := ⟨⟩

theorem line_append : Regula.ExecutableContract LineBytes.append (fun append =>
    Regula.Decides (·.isSome = true)
      (fun input : LineBytes × UInt8 => input.1.bytes.size < lineCapacity)
      (Function.uncurry append)) :=
  ⟨decides (fun _ => dite_isSome _) ⟨(.empty, 0), by decide⟩
    ⟨(⟨⟨Array.replicate lineCapacity 0⟩, by simp [ByteArray.size]⟩, 0),
      by simp [ByteArray.size]⟩⟩

theorem LineBytes_append_registered : Regula.RegisteredDecision @LineBytes.append := ⟨⟩

theorem line_step : Regula.ExecutableContract LineDecoder.step (fun step =>
    Regula.Decides (fun result : LineDecoder × Option LineResult => result.2.isSome = true)
      (fun input : LineDecoder × UInt8 => input.2 = 10)
      (Function.uncurry step)) :=
  ⟨decides
    (fun ⟨decoder, byte⟩ => by
      change (decoder.step byte).2.isSome = true ↔ byte = 10
      by_cases delimiter : byte = 10
      · subst delimiter
        exact iff_of_true (by cases decoder <;> rfl) rfl
      · cases decoder with
        | discarding => simp [LineDecoder.step, delimiter]
        | reading line =>
          simp only [LineDecoder.step, beq_iff_eq, delimiter, ite_false]
          cases line.append byte <;> simp)
    ⟨(.reading .empty, 10), rfl⟩ ⟨(.reading .empty, 32), by decide⟩⟩

theorem LineDecoder_step_registered : Regula.RegisteredDecision @LineDecoder.step := ⟨⟩

theorem line_step_value : Regula.ExecutableContract LineDecoder.step (fun step =>
    (∀ decoder, (step decoder 10).1 = .reading .empty) ∧
      (∀ line, (step (.reading line) 10).2 = some (.line line)) ∧
      (step .discarding 10).2 = some .oversized ∧
      ∀ byte, byte ≠ 10 → step .discarding byte = (.discarding, none)) :=
  ⟨⟨LineDecoder.delimiter_resets, fun _ => rfl, rfl, LineDecoder.discard_suffix⟩⟩

theorem phase_accepts : Regula.ExecutableContract Phase.accepts (fun test =>
    Regula.Decides (· = true)
      (fun input : Phase × UInt64 => input.1 = .running input.2 ∨ input.1 = .stopping input.2)
      (Function.uncurry test)) :=
  ⟨decides
    (fun ⟨phase, generation⟩ => by
      show phase.accepts generation = true ↔ phase = .running generation ∨
        phase = .stopping generation
      cases phase <;> simp [Phase.accepts])
    ⟨(.running 0, 0), .inl rfl⟩ ⟨(.idle, 0), by decide⟩⟩

theorem Phase_accepts_registered : Regula.RegisteredDecision @Phase.accepts := ⟨⟩

theorem map_cell_admit : Regula.ExecutableContract MapCell.admit
    (Regula.Decides (·.isSome = true) (fun byte : UInt8 => byte = 255 ∨ byte.toNat < 8)) :=
  ⟨decides
    (fun byte => by
      show (MapCell.admit byte).isSome = true ↔ _
      unfold MapCell.admit
      by_cases unseen : byte = 255
      · simp [unseen]
      · by_cases terrain : byte.toNat < 8 <;> simp [unseen, terrain])
    ⟨255, by decide⟩ ⟨8, by decide⟩⟩

theorem MapCell_admit_registered : Regula.RegisteredDecision @MapCell.admit := ⟨⟩

theorem capture_matches : Regula.ExecutableContract Capture.matches (fun test =>
    Regula.Decides (· = true)
      (fun input : Capture × Identity =>
        input.1.run = input.2.run ∧ input.1.epoch = input.2.agentEpoch)
      (Function.uncurry test)) :=
  ⟨decides (fun input => by simp [Function.uncurry, Capture.matches])
    ⟨(⟨0, 0, 0, 0, 0, false⟩, ⟨0, 0, 0⟩), by decide⟩
    ⟨(⟨1, 0, 0, 0, 0, false⟩, ⟨0, 0, 0⟩), by decide⟩⟩

theorem Capture_matches_registered : Regula.RegisteredDecision @Capture.matches := ⟨⟩

theorem control_body : Regula.ExecutableContract controlBody
    (Regula.Decides (·.isSome = true)
      (fun bytes : ByteArray => bytes.size ≤ controlBodyCapacity)) :=
  ⟨decides (fun _ => dite_isSome _) ⟨ByteArray.empty, Nat.zero_le _⟩
    ⟨⟨Array.replicate 1025 0⟩, by simp [ByteArray.size, controlBodyCapacity]⟩⟩

theorem controlBody_registered : Regula.RegisteredDecision @controlBody := ⟨⟩

private theorem commandParse_isSome (text : String) :
    (Command.parse text).isSome = true ↔ ∃ command, Command.Spelled text command := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun command => Command.parse_spelled text command

theorem command_parse : Regula.ExecutableContract Command.parse
    (Regula.Decides (·.isSome = true) (fun text => ∃ command, Command.Spelled text command)) :=
  ⟨decides commandParse_isSome ⟨"start", .start, .inl ⟨rfl, rfl⟩⟩
    ⟨"", fun ⟨_, spelled⟩ => by simp [Command.Spelled] at spelled⟩⟩

theorem Command_parse_registered : Regula.RegisteredDecision @Command.parse := ⟨⟩

private theorem fromUTF8?_some {bytes : ByteArray} {text : String}
    (read : String.fromUTF8? bytes = some text) : bytes = text.toUTF8 := by
  unfold String.fromUTF8? at read
  split at read
  · cases read
    rfl
  · cases read

private theorem fromUTF8?_toUTF8 (text : String) : String.fromUTF8? text.toUTF8 = some text := by
  simp [String.fromUTF8?, String.fromUTF8, String.toUTF8_eq_toByteArray, text.isValidUTF8]

private theorem text_object_distinct {cs : List Char} {fields : List (String × Json.Value)}
    (spelled : Json.Grammar.Text cs (.object fields)) : (fields.map Prod.fst).Nodup := by
  obtain ⟨before, body, after, -, value, -, -⟩ := spelled
  cases value with
  | emptyObject => simp
  | object _ _ distinct => exact distinct

private theorem controlCommand_spelled (body : ControlBody) (command : Command)
    (accepted : controlCommand body = .ok command) : ControlSpelled body.val command := by
  unfold controlCommand at accepted
  split at accepted
  · rename_i text decoded
    obtain ⟨value, parsed, decodedValue⟩ := Json.except_bind_ok accepted
    clear accepted
    have spelled := Json.parse_sound text value parsed
    unfold Json.decode at decodedValue
    obtain ⟨fields, fielded, decodedFields⟩ := Json.except_bind_ok decodedValue
    clear decodedValue
    have object : value = .object fields := by
      cases value <;> simp only [Json.Value.fields, reduceCtorEq, Except.ok.injEq] at fielded
      rw [fielded]
    rw [object] at spelled
    obtain ⟨⟨result, rest⟩, ran, finished⟩ := Json.except_bind_ok decodedFields
    cases found : fields.find? (fun p => p.1 == "cmd") with
    | none =>
      simp [Json.text, Json.take, found, StateT.run, bind, StateT.bind, Except.bind, pure,
        Except.pure, get, getThe, MonadStateOf.get, StateT.get, StateT.lift, throw, throwThe,
        MonadExceptOf.throw] at ran
    | some pair =>
      simp [Json.text, Json.take, found, StateT.run, bind, StateT.bind, Except.bind, pure,
        Except.pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
        MonadStateOf.set, StateT.lift, liftM, monadLift, MonadLift.monadLift] at ran
      cases worded : pair.2.text with
      | error e => simp [worded] at ran
      | ok word =>
        cases named : Command.parse word with
        | none =>
          simp [worded, named, throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map,
            Except.map] at ran
        | some parsedCommand =>
          simp [worded, named, StateT.pure, pure, Except.pure] at ran
          obtain ⟨rfl, rfl⟩ := ran
          have empty : (fields.filter fun p => p.1 != "cmd") = [] := by
            by_cases none : (fields.filter fun p => p.1 != "cmd").isEmpty = true
            · simpa using none
            · simp only [none, Bool.false_eq_true, ↓reduceIte] at finished
              cases finished
          simp only [empty, List.isEmpty_nil, ↓reduceIte] at finished
          cases finished
          have member : pair ∈ fields := List.mem_of_find?_eq_some found
          have key : pair.1 = "cmd" := by simpa using List.find?_some found
          have only : ∀ other ∈ fields, other.1 = "cmd" := fun other mem => by
            have := List.filter_eq_nil_iff.mp empty other mem
            simpa using this
          have single : fields = [pair] := by
            have distinct := text_object_distinct spelled
            match fields, member, distinct, only with
            | [first], member, _, _ => simp_all
            | first :: second :: more, _, distinct, only =>
              have same : first.1 = second.1 := by
                rw [only first (by simp), only second (by simp)]
              simp [List.nodup_cons, same] at distinct
          have string : pair.2 = .string word := by
            unfold Json.Value.text at worded
            split at worded
            · rename_i same
              split at worded
              · cases worded
              · cases worded
                exact same
            · cases worded
          refine ⟨text, word, fromUTF8?_some decoded, ?_,
            (Command.parse_spelled word _).mp named⟩
          rw [single] at spelled
          obtain ⟨name, item⟩ := pair
          simp only at key string
          rw [key, string] at spelled
          exact spelled
  · cases accepted

private theorem commandText_parse (word : String) (plain : ∀ c ∈ word.toList, Json.Plain c) :
    Json.parse ("{\"cmd\":\"" ++ word ++ "\"}") = .ok (.object [("cmd", .string word)]) := by
  have text : String.ofList (Json.Request.chars [("cmd", .scalar (.text word))]) =
      "{\"cmd\":\"" ++ word ++ "\"}" := by
    apply String.toList_inj.mp
    simp [Json.Request.chars, Json.member, Json.joined, Json.Part.chars, Json.Scalar.chars]
  rw [← text, Json.parse_request _
    ⟨by simpa [Json.Part.Simple, Json.Scalar.Simple, Json.Plain] using plain, by simp⟩]
  rfl

private theorem controlCommand_written (body : ControlBody) (word : String) (command : Command)
    (spelled : Command.Spelled word command)
    (same : body.val = ("{\"cmd\":\"" ++ word ++ "\"}").toUTF8) :
    controlCommand body = .ok command := by
  unfold controlCommand
  rw [same, fromUTF8?_toUTF8]
  rcases spelled with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (simp only [bind, Except.bind]; rw [commandText_parse _ (by decide)]; rfl)

theorem control_command : Regula.ExecutableContract controlCommand
    (Regula.DecidesSoundly (·.isOk = true)
      (fun body : ControlBody => ∃ command, ControlSpelled body.val command)) :=
  ⟨{ sound := fun body accepted => by
       cases decoded : controlCommand body with
       | ok command => exact ⟨command, controlCommand_spelled body command decoded⟩
       | error refusal => rw [decoded] at accepted; exact absurd accepted Bool.false_ne_true
     accepted := ⟨⟨("{\"cmd\":\"" ++ "start" ++ "\"}").toUTF8, by decide⟩, by
       rw [controlCommand_written _ "start" .start (.inl ⟨rfl, rfl⟩) rfl]
       rfl⟩ }⟩

theorem control_command_written : Regula.ExecutableContract controlCommand
    (Regula.DecidesCompletely (·.isOk = true)
      (fun body : ControlBody => ∃ word command, Command.Spelled word command ∧
        body.val = ("{\"cmd\":\"" ++ word ++ "\"}").toUTF8)) :=
  ⟨{ complete := fun body ⟨word, command, spelled, same⟩ => by
       rw [controlCommand_written body word command spelled same]
       rfl
     refused := ⟨⟨ByteArray.empty, by decide⟩, by decide +kernel⟩ }⟩

theorem controlCommand_registered : Regula.RegisteredDecision @controlCommand := ⟨⟩

theorem control_command_value : Regula.ExecutableContract controlCommand (fun decode =>
    ∀ body command, decode body = .ok command → ControlSpelled body.val command) :=
  ⟨controlCommand_spelled⟩

def WireLine (text : String) : Prop :=
  text.utf8ByteSize ≤ lineCapacity ∧ text.contains '\n' = false ∧ text.contains '\r' = false

private theorem wireTextLegal_iff (text : String) : wireTextLegal text = true ↔ WireLine text := by
  simp [wireTextLegal, WireLine, and_assoc]

theorem wire_text_legal : Regula.ExecutableContract wireTextLegal
    (Regula.Decides (· = true) WireLine) :=
  ⟨.of_iff wireTextLegal_iff ⟨"", by simp [wireTextLegal, lineCapacity]⟩
    ⟨"\n", by simp [wireTextLegal, lineCapacity]⟩⟩

theorem wireTextLegal_registered : Regula.RegisteredDecision @wireTextLegal := ⟨⟩

theorem wire_text : Regula.ExecutableContract wireText
    (Regula.Decides (·.isSome = true) WireLine) :=
  ⟨.of_iff (fun text => (dite_isSome _).trans (wireTextLegal_iff text))
    ⟨"", (dite_isSome _).mpr (by simp [wireTextLegal, lineCapacity])⟩
    ⟨"\n", fun accepted =>
      absurd ((dite_isSome _).mp accepted) (by simp [wireTextLegal, lineCapacity])⟩⟩

theorem wireText_registered : Regula.RegisteredDecision @wireText := ⟨⟩

theorem binary32_dyadic : Regula.ExecutableContract binary32Dyadic
    (Regula.Decides (·.isSome = true) (fun value : Binary32 => value.Finite)) :=
  ⟨decides
    (fun value => by
      show (binary32Dyadic value).isSome = true ↔ _
      unfold binary32Dyadic
      split <;> simp_all)
    ⟨.zero, by decide⟩ ⟨⟨0x7fc00000⟩, by decide⟩⟩

theorem binary32Dyadic_registered : Regula.RegisteredDecision @binary32Dyadic := ⟨⟩

theorem binary64_dyadic : Regula.ExecutableContract binary64Dyadic
    (Regula.Decides (·.isSome = true) (fun value : Binary64 => value.Finite)) :=
  ⟨decides
    (fun value => by
      show (binary64Dyadic value).isSome = true ↔ _
      unfold binary64Dyadic
      split <;> simp_all)
    ⟨⟨0⟩, by decide⟩ ⟨⟨0x7ff8000000000000⟩, by decide⟩⟩

theorem binary64Dyadic_registered : Regula.RegisteredDecision @binary64Dyadic := ⟨⟩

private theorem difference_self (bytes : List UInt8) (difference : UInt8) :
    (bytes.zip bytes).foldl (fun (difference : UInt8) pair => difference ||| (pair.1 ^^^ pair.2))
      difference = difference := by
  induction bytes generalizing difference with
  | nil => rfl
  | cons byte rest ih => simp [ih]

private theorem tokenMatches_iff (received expected : String) :
    tokenMatches received expected = true ↔ received = expected := by
  constructor
  · intro matched
    unfold tokenMatches at matched
    split at matched
    · exact absurd matched Bool.false_ne_true
    · simp only [Bool.and_eq_true, beq_iff_eq] at matched
      exact matched.2
  · rintro rfl
    simp [tokenMatches, difference_self]

theorem token_matches : Regula.ExecutableContract tokenMatches (fun test =>
    Regula.Decides (· = true) (fun tokens : String × String => tokens.1 = tokens.2)
      (Function.uncurry test)) :=
  ⟨decides (fun tokens => tokenMatches_iff tokens.1 tokens.2) ⟨("", ""), rfl⟩
    ⟨("", "a"), by decide⟩⟩

theorem tokenMatches_registered : Regula.RegisteredDecision @tokenMatches := ⟨⟩

theorem control_authorizes : Regula.ExecutableContract ControlHeaders.authorizes (fun test =>
    Regula.Decides (· = true)
      (fun input : (ControlHeaders × String) × ControlBody =>
        input.1.1.method = "POST" ∧ input.1.1.mediaType = "application/json" ∧
          input.1.2.isEmpty = false ∧ input.1.1.token = input.1.2 ∧
          input.1.1.length = some input.2.val.size)
      (Function.uncurry (Function.uncurry test))) :=
  ⟨decides
    (fun input => by
      simp [Function.uncurry, ControlHeaders.authorizes, tokenMatches_iff, and_assoc])
    ⟨((⟨"POST", "application/json", "a", some 0⟩, "a"), ⟨ByteArray.empty, Nat.zero_le _⟩),
      by decide⟩
    ⟨((⟨"GET", "application/json", "a", some 0⟩, "a"), ⟨ByteArray.empty, Nat.zero_le _⟩),
      fun authorized => absurd authorized.1 (by decide)⟩⟩

theorem ControlHeaders_authorizes_registered :
    Regula.RegisteredDecision @ControlHeaders.authorizes := ⟨⟩

theorem conversion_fits : Regula.ExecutableContract BrowserConversion.fits (fun test =>
    Regula.Decides (· = true)
      (fun input : BrowserConversion × TelemetryShape =>
        input.1 = .keep ∨
          (input.1 = .nonFinite ∧ (input.2 = .binary32 ∨ input.2 = .binary64)) ∨
          ((input.1 = .unmeasured ∨ input.1 = .absentIndex) ∧ input.2 = .optional .natural) ∨
          ∃ count, (input.1 = .float32 ∧ input.2 = .array count .binary32) ∨
            (input.1 = .float64 ∧ input.2 = .array count .binary64) ∨
            (input.1 = .counts ∧ input.2 = .array count .natural) ∨
            (input.1 = .absentIndices ∧ input.2 = .array count (.optional .natural)))
      (Function.uncurry test)) :=
  ⟨decides
    (fun ⟨conversion, shape⟩ => by
      cases conversion <;> cases shape <;>
        first
        | (simp [Function.uncurry, BrowserConversion.fits]; done)
        | (rename_i element
           cases element <;>
             first
             | (simp [Function.uncurry, BrowserConversion.fits]; done)
             | (rename_i inner
                cases inner <;> simp [Function.uncurry, BrowserConversion.fits])))
    ⟨(.keep, .natural), .inl rfl⟩ ⟨(.nonFinite, .natural), by simp⟩⟩

theorem BrowserConversion_fits_registered : Regula.RegisteredDecision @BrowserConversion.fits := ⟨⟩

def FirstIndexBound (key : String) (upper : Nat) : Prop :=
  ∃ before after,
    browserRules = before ++ (key, BrowserRule.each (.nullable (.range upper))) :: after ∧
      ∀ other, (key, BrowserRule.each (.nullable (.range other))) ∉ before

private theorem indexBound_iff (key : String) (upper : Nat) :
    browserIndexBound key = some upper ↔ FirstIndexBound key upper := by
  unfold browserIndexBound FirstIndexBound
  rw [List.findSome?_eq_some_iff]
  constructor
  · rintro ⟨before, ⟨name, rule⟩, after, parts, found, absent⟩
    dsimp only at found
    split at found
    · rename_i bound
      by_cases same : name = key
      · subst same
        simp only [↓reduceIte, Option.some.injEq] at found
        subst found
        refine ⟨before, after, parts, fun other member => ?_⟩
        have none := absent _ member
        simp at none
      · simp [same] at found
    · simp at found
  · rintro ⟨before, after, parts, absent⟩
    refine ⟨before, _, after, parts, by simp, fun ⟨name, rule⟩ member => ?_⟩
    dsimp only
    split
    · rename_i bound
      by_cases same : name = key
      · subst same
        exact absurd member (absent bound)
      · simp [same]
    · rfl

theorem conversion_indexed : Regula.ExecutableContract BrowserConversion.indexed (fun test =>
    Regula.Decides (· = true)
      (fun input : BrowserConversion × String =>
        input.1 = .absentIndices → ∃ upper, FirstIndexBound input.2 upper ∧ upper ≤ 2 ^ 31)
      (Function.uncurry test)) :=
  ⟨.of_iff
    (fun ⟨conversion, key⟩ => by
      show conversion.indexed key = true ↔
        (conversion = .absentIndices → ∃ upper, FirstIndexBound key upper ∧ upper ≤ 2 ^ 31)
      cases conversion with
      | absentIndices =>
        unfold BrowserConversion.indexed
        cases found : browserIndexBound key with
        | none =>
          constructor
          · intro accepted
            cases accepted
          · intro bounded
            obtain ⟨upper, first, -⟩ := bounded rfl
            rw [(indexBound_iff key upper).mpr first] at found
            cases found
        | some upper =>
          constructor
          · intro within _
            exact ⟨upper, (indexBound_iff key upper).mp found, of_decide_eq_true within⟩
          · intro bounded
            obtain ⟨other, first, within⟩ := bounded rfl
            have same := (indexBound_iff key other).mpr first
            rw [found] at same
            cases same
            exact decide_eq_true within
      | _ => simp [BrowserConversion.indexed])
    ⟨(.keep, ""), by decide⟩ ⟨(.absentIndices, ""), by decide +kernel⟩⟩

theorem BrowserConversion_indexed_registered :
    Regula.RegisteredDecision @BrowserConversion.indexed := ⟨⟩

theorem capture_after : Regula.ExecutableContract Capture.after (fun test =>
    Regula.DecidesSoundly (· = true)
      (fun input : Capture × Capture => input.1 ≠ input.2) (Function.uncurry test)) :=
  ⟨{ sound := fun input accepted same => by
       have later : input.1.after input.2 = true := accepted
       rw [same, Capture.after_irreflexive] at later
       exact Bool.false_ne_true later
     accepted := ⟨(⟨0, 0, 1, 0, 0, false⟩, ⟨0, 0, 0, 0, 0, false⟩), by decide⟩ }⟩

theorem Capture_after_registered : Regula.RegisteredDecision @Capture.after := ⟨⟩

theorem retry_ready : Regula.ExecutableContract Retry.ready (fun test =>
    Regula.DecidesSoundly (· = true)
      (fun input : Retry × UInt64 => input.1.count ≠ failureLimit) (Function.uncurry test)) :=
  ⟨{ sound := fun input accepted spent => by
       have ready : input.1.ready input.2 = true := accepted
       have exhausted : input.1.exhausted = true := by simp [Retry.exhausted, ← spent, Retry.count]
       rw [Retry.exhausted_not_ready input.1 input.2 exhausted] at ready
       exact absurd ready Bool.false_ne_true
     accepted := ⟨(Retry.initial, 0), by decide⟩ }⟩

theorem Retry_ready_registered : Regula.RegisteredDecision @Retry.ready := ⟨⟩

theorem retry_exhausted : Regula.ExecutableContract Retry.exhausted
    (Regula.Decides (· = true) (fun retry : Retry => retry.count = failureLimit)) :=
  ⟨decides (fun retry => by simp [Retry.exhausted, Retry.count])
    ⟨((Retry.initial.failed 0 false).failed 0 false).failed 0 false, by decide⟩
    ⟨Retry.initial, by decide⟩⟩

theorem Retry_exhausted_registered : Regula.RegisteredDecision @Retry.exhausted := ⟨⟩

theorem aggregate_all : Regula.ExecutableContract Agreement.aggregateAll
    (Regula.Decides (·.isSome = true)
      (fun ratios : List (Option Agreement.Ratio) => ∀ ratio ∈ ratios, ratio.isSome = true)) :=
  ⟨decides
    (fun ratios => by
      induction ratios with
      | nil => simp [Agreement.aggregateAll]
      | cons head tail ih =>
        cases head with
        | none => simp [Agreement.aggregateAll]
        | some ratio => simpa [Agreement.aggregateAll] using ih)
    ⟨[], by simp⟩ ⟨[none], by simp⟩⟩

theorem Agreement_aggregateAll_registered : Regula.RegisteredDecision @Agreement.aggregateAll := ⟨⟩

theorem aggregate_ratio : Regula.ExecutableContract Agreement.Aggregate.ratio
    (Regula.Decides (·.isSome = true)
      (fun aggregate : Agreement.Aggregate =>
        0 < aggregate.questions * aggregate.denominator)) :=
  ⟨decides (fun _ => dite_isSome _)
    ⟨Agreement.Aggregate.empty.add ⟨0, 1, by decide, by decide⟩, by decide⟩
    ⟨.empty, by decide⟩⟩

theorem Agreement_Aggregate_ratio_registered :
    Regula.RegisteredDecision @Agreement.Aggregate.ratio := ⟨⟩

theorem clear_disabled : Regula.ExecutableContract LaunchMode.clearDisabled
    (Regula.Decides (·.isSome = true)
      (fun mode : LaunchMode => ∃ command, mode = .fixed command)) :=
  ⟨decides (fun mode => by cases mode <;> simp [LaunchMode.clearDisabled])
    ⟨.fixed "", "", rfl⟩ ⟨.ranked, by simp⟩⟩

theorem LaunchMode_clearDisabled_registered :
    Regula.RegisteredDecision @LaunchMode.clearDisabled := ⟨⟩

theorem capture_follows_complete : Regula.ExecutableContract Capture.follows (fun test =>
    Regula.DecidesCompletely (· = true)
      (fun input : Capture × Capture =>
        input.1.lifetime = input.2.lifetime ∧ input.1.terminal = true ∧
          input.2.terminal = false ∧ input.1.world.toNat = input.2.world.toNat + 1)
      (Function.uncurry test)) :=
  ⟨{ complete := fun input ⟨same, terminal, running, advanced⟩ => by
       show input.1.follows input.2 = true
       rw [Capture.follows_equal_lifetime input.1 input.2 same]
       simp [terminal, running, advanced]
     refused := ⟨(⟨0, 0, 0, 0, 0, false⟩, ⟨0, 0, 0, 0, 0, false⟩), by decide⟩ }⟩

theorem Capture_follows_registered : Regula.RegisteredDecision @Capture.follows := ⟨⟩

theorem capture_follows : Regula.ExecutableContract Capture.follows (fun test =>
    ∀ next previous : Capture, next.lifetime = previous.lifetime →
      test next previous =
        (next.terminal && !previous.terminal &&
          next.world.toNat == previous.world.toNat + 1)) :=
  ⟨Capture.follows_equal_lifetime⟩

private def firstCapture : Capture := ⟨0, 0, 0, 0, 0, false⟩

theorem viewer_admission : Regula.ExecutableContract @Admission.receive (fun receive =>
    (∀ {identity} (state : Admission identity) (capture : Capture),
      (capture.matches identity = false → receive state capture = (.skipped, state)) ∧
        ((receive state capture).1 = .stored →
          (receive state capture).2.previous = some capture) ∧
        ((receive state capture).1 ≠ .stored →
          (receive state capture).2.previous = state.previous)) ∧
      (receive (Admission.empty ⟨0, 0, 0⟩) firstCapture).1 = .stored ∧
      (receive (Admission.empty ⟨1, 0, 0⟩) firstCapture).1 = .skipped) :=
  ⟨⟨fun state capture => ⟨Admission.wrong_identity state capture,
      Admission.stored_capture state capture, Admission.rejected_preserves_history state capture⟩,
    rfl, rfl⟩⟩

theorem viewer_health : Regula.ExecutableContract @HealthAdmission.receive (fun receive =>
    (∀ {identity} (state : HealthAdmission identity) (capture : Capture),
      (capture.matches identity = false → (receive state capture).1 = false) ∧
        ((receive state capture).1 = false → (receive state capture).2 = state) ∧
        ((receive state capture).1 = true →
          (receive state capture).2.previous = some capture)) ∧
      (receive (HealthAdmission.empty ⟨0, 0, 0⟩) firstCapture).1 = true ∧
      (receive (HealthAdmission.empty ⟨1, 0, 0⟩) firstCapture).1 = false) :=
  ⟨⟨fun {identity} state capture =>
      ⟨fun wrong => by simp [HealthAdmission.receive, wrong],
        HealthAdmission.rejected_preserves state capture,
        fun accepted => by
          by_cases same : capture.matches identity = true
          · by_cases later : state.previous.all (capture.after ·) = true
            · simp [HealthAdmission.receive, same, later]
            · simp [HealthAdmission.receive, same, later] at accepted
          · simp [HealthAdmission.receive, same] at accepted⟩,
    rfl, rfl⟩⟩

theorem inventory_owns : Regula.ExecutableContract Host.Inventory.owns (fun owns =>
    Regula.Decides (· = true)
      (fun input : Host.Inventory × Host.Craftable =>
        (input.2 = .axe ∧ input.1.axe = true) ∨ (input.2 = .boat ∧ input.1.boat = true))
      (Function.uncurry owns)) :=
  ⟨decides
    (fun ⟨inventory, tool⟩ => by cases tool <;> simp [Function.uncurry, Host.Inventory.owns])
    ⟨(⟨0, 0, 0, 0, true, false⟩, .axe), by decide⟩
    ⟨(⟨0, 0, 0, 0, false, false⟩, .axe), by decide⟩⟩

theorem Host_Inventory_owns_registered : Regula.RegisteredDecision @Host.Inventory.owns := ⟨⟩

theorem harvest_yield : Regula.ExecutableContract Host.TileKind.harvestYield
    (Regula.Decides (·.isSome = true)
      (fun kind : Host.TileKind => kind = .tree ∨ kind = .stone ∨ kind = .ore)) :=
  ⟨decides (fun kind => by cases kind <;> simp [Host.TileKind.harvestYield])
    ⟨.tree, .inl rfl⟩ ⟨.grass, by decide⟩⟩

theorem Host_TileKind_harvestYield_registered :
    Regula.RegisteredDecision @Host.TileKind.harvestYield := ⟨⟩

theorem checkpoint_due : Regula.ExecutableContract Host.WritableCheckpoint.due (fun due =>
    Regula.Decides (· = true)
      (fun input : Host.WritableCheckpoint × Bool =>
        input.2 = true ∨ input.1.phase.val = 0)
      (Function.uncurry due)) :=
  ⟨decides (fun input => by simp [Function.uncurry, Host.WritableCheckpoint.due])
    ⟨((Host.WritableCheckpoint.admit "checkpoint" 2 .loaded).get (by decide), false),
      by decide⟩
    ⟨(((Host.WritableCheckpoint.admit "checkpoint" 2 .loaded).get (by decide)).advance, false),
      by decide⟩⟩

theorem Host_WritableCheckpoint_due_registered :
    Regula.RegisteredDecision @Host.WritableCheckpoint.due := ⟨⟩

theorem index_bound : Regula.ExecutableContract browserIndexBound
    (Regula.Decides (·.isSome = true)
      (fun key : String =>
        ∃ upper, (key, BrowserRule.each (.nullable (.range upper))) ∈ browserRules)) :=
  ⟨.of_iff
    (fun key => by
      unfold browserIndexBound
      rw [List.findSome?_isSome_iff]
      constructor
      · rintro ⟨⟨name, rule⟩, member, found⟩
        dsimp only at found
        split at found
        · rename_i upper
          by_cases same : name = key
          · exact ⟨upper, same ▸ member⟩
          · simp [same] at found
        · simp at found
      · rintro ⟨upper, member⟩
        exact ⟨_, member, by simp⟩)
    ⟨"agreement_channel_score", by decide +kernel⟩ ⟨"", by decide +kernel⟩⟩

theorem browserIndexBound_registered : Regula.RegisteredDecision @browserIndexBound := ⟨⟩

theorem element_bound : Regula.ExecutableContract browserElementBound
    (Regula.Decides (·.isSome = true)
      (fun key : String => ∃ upper, (key, BrowserRule.each (.range upper)) ∈ browserRules)) :=
  ⟨.of_iff
    (fun key => by
      unfold browserElementBound
      rw [List.findSome?_isSome_iff]
      constructor
      · rintro ⟨⟨name, rule⟩, member, found⟩
        dsimp only at found
        split at found
        · rename_i upper
          by_cases same : name = key
          · exact ⟨upper, same ▸ member⟩
          · simp [same] at found
        · simp at found
      · rintro ⟨upper, member⟩
        exact ⟨_, member, by simp⟩)
    ⟨"tiles", by decide +kernel⟩ ⟨"", by decide +kernel⟩⟩

theorem browserElementBound_registered : Regula.RegisteredDecision @browserElementBound := ⟨⟩

theorem conversion_number : Regula.ExecutableContract BrowserConversion.number (fun test =>
    Regula.Decides (· = true)
      (fun input : BrowserConversion × TelemetryShape =>
        (input.1 = .nonFinite ∧ (input.2 = .binary32 ∨ input.2 = .binary64)) ∨
          ((input.1 = .unmeasured ∨ input.1 = .absentIndex) ∧ input.2 = .optional .natural) ∨
          (input.1 = .keep ∧ (input.2 = .natural ∨ input.2 = .integer ∨ input.2 = .goalKind ∨
            input.2 = .goalItem)))
      (Function.uncurry test)) :=
  ⟨decides
    (fun ⟨conversion, shape⟩ => by
      cases conversion <;> cases shape <;>
        first
        | (simp [Function.uncurry, BrowserConversion.number, BrowserConversion.fits]; done)
        | (rename_i element
           cases element <;>
             simp [Function.uncurry, BrowserConversion.number, BrowserConversion.fits]))
    ⟨(.keep, .natural), .inr (.inr ⟨rfl, .inl rfl⟩)⟩ ⟨(.keep, .text), by simp⟩⟩

theorem BrowserConversion_number_registered :
    Regula.RegisteredDecision @BrowserConversion.number := ⟨⟩

theorem conversion_numbers : Regula.ExecutableContract BrowserConversion.numbers (fun test =>
    Regula.Decides (·.isSome = true)
      (fun input : BrowserConversion × TelemetryShape => ∃ count,
        (input.1 = .float32 ∧ input.2 = .array count .binary32) ∨
          (input.1 = .float64 ∧ input.2 = .array count .binary64) ∨
          (input.1 = .counts ∧ input.2 = .array count .natural) ∨
          (input.1 = .absentIndices ∧ input.2 = .array count (.optional .natural)))
      (Function.uncurry test)) :=
  ⟨decides
    (fun ⟨conversion, shape⟩ => by
      cases conversion <;> cases shape <;>
        first
        | (simp [Function.uncurry, BrowserConversion.numbers, BrowserConversion.fits]; done)
        | (rename_i element
           cases element <;>
             first
             | (simp [Function.uncurry, BrowserConversion.numbers, BrowserConversion.fits]; done)
             | (rename_i inner
                cases inner <;>
                  simp [Function.uncurry, BrowserConversion.numbers, BrowserConversion.fits])))
    ⟨(.float32, .array 1 .binary32), 1, .inl ⟨rfl, rfl⟩⟩
    ⟨(.keep, .natural), by simp⟩⟩

theorem BrowserConversion_numbers_registered :
    Regula.RegisteredDecision @BrowserConversion.numbers := ⟨⟩

theorem owns_identity :
    Regula.ExecutableContract Host.Viewer.Lifecycle.ownsIdentity (fun owns =>
      Regula.Decides (· = true)
        (fun input : Host.Viewer.Lifecycle × UInt64 => input.1.OwnsIdentity input.2)
        (Function.uncurry owns)) :=
  ⟨.of_iff (fun input => Host.Viewer.Lifecycle.ownsIdentity_iff input.1 input.2)
    ⟨(.initial ⟨0, 0, 0⟩ .stopped, 0), by decide⟩
    ⟨(.initial ⟨0, 0, 0⟩ .stopped, 1), by decide⟩⟩

theorem Host_Viewer_Lifecycle_ownsIdentity_registered :
    Regula.RegisteredDecision @Host.Viewer.Lifecycle.ownsIdentity := ⟨⟩

private theorem columns_fit : ∀ entry ∈ browserColumns, ∀ field ∈ browserSchema,
    field.1 = entry.1 → BrowserColumn.fits entry.1 entry.2 field.2 = true := by
  intro entry hEntry field hField hKey
  obtain ⟨shape, hShape, hFits⟩ := browserColumns_live entry hEntry
  have hSame : field.2 = shape :=
    eq_of_mem_of_nodup_fst browserSchema_distinct (hKey ▸ hField) hShape
  exact hSame ▸ hFits

theorem column_fits : Regula.ExecutableContract BrowserColumn.fits (fun fits =>
    Regula.DecidesCompletely (· = true)
      (fun input : (String × BrowserColumn) × TelemetryShape =>
        input.1 ∈ browserColumns ∧ (input.1.1, input.2) ∈ browserSchema)
      (Function.uncurry (Function.uncurry fits))) :=
  ⟨{ complete := fun input listed =>
       columns_fit input.1 listed.1 (input.1.1, input.2) listed.2 rfl
     refused := ⟨(("flag", ⟨"flag", .flag⟩), .text), by decide +kernel⟩ }⟩

theorem BrowserColumn_fits_registered : Regula.RegisteredDecision @BrowserColumn.fits := ⟨⟩

private theorem lookup_listed {β : Type} : ∀ (table : List (String × β)) (key : String) (item : β),
    table.lookup key = some item → ∃ name, (name, item) ∈ table
  | [], _, _, found => by simp at found
  | (name, value) :: rest, key, item, found => by
    rw [List.lookup_cons] at found
    split at found
    · cases found
      exact ⟨name, List.mem_cons_self⟩
    · obtain ⟨other, member⟩ := lookup_listed rest key item found
      exact ⟨other, List.mem_cons_of_mem _ member⟩

private theorem conversion_float32 (key : String) (shape : TelemetryShape) :
    browserConversion key shape = .float32 ↔ ∃ count, shape = .array count .binary32 := by
  have default : shape.defaultConversion = .float32 ↔ ∃ count, shape = .array count .binary32 := by
    cases shape with
    | array count element => cases element <;> simp [TelemetryShape.defaultConversion]
    | _ => simp [TelemetryShape.defaultConversion]
  unfold browserConversion
  cases found : browserOverrides.lookup key with
  | none => exact default
  | some conversion =>
    obtain ⟨name, member⟩ := lookup_listed browserOverrides key conversion found
    have listed : conversion = .unmeasured ∨ conversion = .absentIndex ∨
        conversion = .absentIndices := by
      simp only [browserOverrides, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
        at member
      rcases member with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
    show (if conversion.fits shape then conversion else shape.defaultConversion) = .float32 ↔ _
    split
    · rename_i fits
      constructor
      · intro same
        rcases listed with rfl | rfl | rfl <;> cases same
      · rintro ⟨count, rfl⟩
        rcases listed with rfl | rfl | rfl <;> simp [BrowserConversion.fits] at fits
    · exact default

theorem property_fits : Regula.ExecutableContract BrowserProperty.fits (fun fits =>
    Regula.Decides (· = true)
      (fun input : (String × BrowserProperty) × TelemetryShape =>
        input.1.2.reading = .value ∨ ∃ count, input.2 = .array count .binary32)
      (Function.uncurry (Function.uncurry fits))) :=
  ⟨decides
    (fun ⟨⟨key, property⟩, shape⟩ => by
      show BrowserProperty.fits key property shape = true ↔
        (property.reading = .value ∨ ∃ count, shape = .array count .binary32)
      unfold BrowserProperty.fits
      cases property.reading with
      | value => simp
      | twice =>
        simp only [reduceCtorEq, false_or]
        rw [← conversion_float32 key shape]
        cases browserConversion key shape <;> simp)
    ⟨(("", ⟨"", .value⟩), .text), .inl rfl⟩
    ⟨(("", ⟨"", .twice⟩), .text), by simp⟩⟩

theorem BrowserProperty_fits_registered : Regula.RegisteredDecision @BrowserProperty.fits := ⟨⟩

private theorem phase_live (phase : Host.Viewer.Phase) :
    (phase != .idle) = true ↔ phase ≠ .idle := by
  cases phase with
  | idle => exact ⟨fun differs => absurd differs (by decide), fun differs => absurd rfl differs⟩
  | starting generation => exact ⟨fun _ equal => (nomatch equal), fun _ => rfl⟩
  | running generation => exact ⟨fun _ equal => (nomatch equal), fun _ => rfl⟩
  | stopping generation => exact ⟨fun _ equal => (nomatch equal), fun _ => rfl⟩
  | archiving => exact ⟨fun _ equal => (nomatch equal), fun _ => rfl⟩

private theorem status_failed (status : Option Host.CheckpointStatus) :
    (status == some .failed) = true ↔ status = some .failed := by
  cases status with
  | none => exact ⟨fun same => absurd same (by decide), fun same => nomatch same⟩
  | some value =>
    cases value <;>
      first
      | exact ⟨fun _ => rfl, fun _ => rfl⟩
      | exact ⟨fun same => absurd same (by decide), fun same => nomatch same⟩

theorem control_warning : Regula.ExecutableContract controlWarning (fun warning =>
    Regula.Decides (·.isSome = true)
      (fun input : Host.Viewer.Lifecycle × ControlDetail =>
        input.1.phaseValue = .idle ∧
          (input.2.abnormalExit = true ∨ input.2.log.checkpoint = some .failed))
      (Function.uncurry warning)) :=
  ⟨.of_iff
    (fun ⟨lifecycle, detail⟩ => by
      show (controlWarning lifecycle detail).isSome = true ↔
        (lifecycle.phaseValue = .idle ∧
          (detail.abnormalExit = true ∨ detail.log.checkpoint = some .failed))
      unfold controlWarning
      by_cases idle : lifecycle.phaseValue = .idle
      · have settled : ¬(lifecycle.phaseValue != .idle) = true := fun differs =>
          (phase_live _).mp differs idle
        rw [ite_eq_right settled]
        by_cases abnormal : detail.abnormalExit = true
        · rw [ite_eq_left abnormal]
          exact ⟨fun _ => ⟨idle, .inl abnormal⟩, fun _ => rfl⟩
        · rw [ite_eq_right abnormal]
          by_cases failed : detail.log.checkpoint = some .failed
          · rw [ite_eq_left ((status_failed _).mpr failed)]
            exact ⟨fun _ => ⟨idle, .inr failed⟩, fun _ => rfl⟩
          · have test : ¬(detail.log.checkpoint == some .failed) = true := fun same =>
              failed ((status_failed _).mp same)
            rw [ite_eq_right test]
            exact ⟨fun present => by simp at present,
              fun cause => cause.2.elim (absurd · abnormal) (absurd · failed)⟩
      · rw [ite_eq_left ((phase_live _).mpr idle)]
        exact ⟨fun present => by simp at present, fun cause => absurd cause.1 idle⟩)
    ⟨(.initial ⟨0, 0, 0⟩ .stopped,
        { transition := .initialized, reason := "", clearDisabled := none, log := {},
          abnormalExit := true }), by decide⟩
    ⟨(.initial ⟨0, 0, 0⟩ .stopped,
        { transition := .initialized, reason := "", clearDisabled := none, log := {} }),
      by decide⟩⟩

theorem controlWarning_registered : Regula.RegisteredDecision @controlWarning := ⟨⟩

theorem Interval32_orderedDecidable_registered :
    Regula.RegisteredDecision @Interval32.orderedDecidable := ⟨⟩

theorem Binary32_positiveDecidable_registered :
    Regula.RegisteredDecision @Binary32.positiveDecidable := ⟨⟩

theorem Binary32_instDecidableFinite_registered :
    Regula.RegisteredDecision @Binary32.instDecidableFinite := ⟨⟩

theorem Binary64_instDecidableFinite_registered :
    Regula.RegisteredDecision @Binary64.instDecidableFinite := ⟨⟩

theorem Interval32_instDecidableContains_registered :
    Regula.RegisteredDecision @Interval32.instDecidableContains := ⟨⟩

theorem Features_instDecidableRecent_registered :
    Regula.RegisteredDecision @Features.instDecidableRecent := ⟨⟩

theorem Features_instDecidableDominates_registered :
    Regula.RegisteredDecision @Features.instDecidableDominates := ⟨⟩

theorem Lifetime_instDecidableLegalSum_registered :
    Regula.RegisteredDecision @Lifetime.instDecidableLegalSum := ⟨⟩

theorem Checkpoint_instDecidableValid_registered :
    Regula.RegisteredDecision @Checkpoint.instDecidableValid := ⟨⟩

theorem Checkpoint_instDecidableOptionsValid_registered :
    Regula.RegisteredDecision @Checkpoint.instDecidableOptionsValid := ⟨⟩

theorem Checkpoint_instDecidableInterestAligned_registered :
    Regula.RegisteredDecision @Checkpoint.instDecidableInterestAligned := ⟨⟩

theorem Checkpoint_instDecidableEnsembleAligned_registered :
    Regula.RegisteredDecision @Checkpoint.instDecidableEnsembleAligned := ⟨⟩

theorem Checkpoint_instDecidableEnsembleDistinct_registered :
    Regula.RegisteredDecision @Checkpoint.instDecidableEnsembleDistinct := ⟨⟩

theorem Checkpoint_instDecidableEpisodes_registered :
    Regula.RegisteredDecision @Checkpoint.instDecidableEpisodes := ⟨⟩

theorem Binary32_instDecidableNegative_registered :
    Regula.RegisteredDecision @Binary32.instDecidableNegative := ⟨⟩

theorem Binary32_instDecidableIsNaN_registered :
    Regula.RegisteredDecision @Binary32.instDecidableIsNaN := ⟨⟩

theorem Binary32_instDecidableLess_registered :
    Regula.RegisteredDecision @Binary32.instDecidableLess := ⟨⟩

theorem Binary64_instDecidableIsNaN_registered :
    Regula.RegisteredDecision @Binary64.instDecidableIsNaN := ⟨⟩

theorem Binary64_instDecidableLess_registered :
    Regula.RegisteredDecision @Binary64.instDecidableLess := ⟨⟩

theorem Host_instDecidableWalkable_registered :
    Regula.RegisteredDecision @Host.instDecidableWalkable := ⟨⟩

theorem Host_instDecidableOwns_registered : Regula.RegisteredDecision @Host.instDecidableOwns := ⟨⟩

theorem Host_instDecidableInBox_registered :
    Regula.RegisteredDecision @Host.instDecidableInBox := ⟨⟩

theorem Handcrafted_instDecidableResumable_registered :
    Regula.RegisteredDecision @Handcrafted.instDecidableResumable := ⟨⟩

theorem Host_instDecidableGoalSatisfied_registered :
    Regula.RegisteredDecision @Host.instDecidableGoalSatisfied := ⟨⟩

theorem Host_instDecidableFoodDue_registered :
    Regula.RegisteredDecision @Host.instDecidableFoodDue := ⟨⟩

theorem bounded_admit : Regula.ExecutableContract Bounded32.admit (fun admit =>
    Regula.Decides (· = true)
      (fun input : Interval32 × Binary32 => input.1.Contains input.2)
      (Regula.Dependent.isSome fun input : Interval32 × Binary32 => admit input.1 input.2)) :=
  ⟨present (fun input => accepts_iff (Bounded32.admit_refuses input.1 input.2))
    ⟨(point, .zero), by decide⟩ ⟨(point, ⟨0x7fc00000⟩), by decide⟩⟩

theorem Bounded32_admit_registered : Regula.RegisteredDecision @Bounded32.admit := ⟨⟩

theorem weight_admit : Regula.ExecutableContract Weight.admit (fun admit =>
    Regula.Decides (· = true)
      (fun input : ValueRule × Binary32 => input.1.domain.range.Contains input.2)
      (Regula.Dependent.isSome fun input : ValueRule × Binary32 => admit input.1 input.2)) :=
  ⟨present (fun input => accepts_iff (weight_admit_refuses input.1 input.2))
    ⟨(.differential, .zero), ValueRule.differential.domain.zeroLegal⟩
    ⟨(.differential, ⟨0x7fc00000⟩), fun legal => absurd legal.1 (by decide)⟩⟩

theorem Weight_admit_registered : Regula.RegisteredDecision @Weight.admit := ⟨⟩

theorem feature_index_admit : Regula.ExecutableContract FeatIdx.admit (fun admit =>
    Regula.Decides (· = true)
      (fun input : Dimension × UInt32 => input.2.toNat < input.1.capacity)
      (Regula.Dependent.isSome fun input : Dimension × UInt32 => admit input.1 input.2)) :=
  ⟨present
    (fun input => (accepts_iff_not (feature_index_admit_refuses input.1 input.2)).trans
      Nat.not_le)
    ⟨(narrow, 0), by decide⟩ ⟨(narrow, 1), by decide⟩⟩

theorem FeatIdx_admit_registered : Regula.RegisteredDecision @FeatIdx.admit := ⟨⟩

theorem action_admit : Regula.ExecutableContract Action.admit (fun admit =>
    Regula.Decides (· = true) (fun input : Nat × Nat => input.2 < input.1)
      (Regula.Dependent.isSome fun input : Nat × Nat => admit input.1 input.2)) :=
  ⟨present (fun input => (accepts_iff_not (Action.admit_none input.1 input.2)).trans Nat.not_le)
    ⟨(1, 0), by decide⟩ ⟨(0, 0), by decide⟩⟩

theorem Action_admit_registered : Regula.RegisteredDecision @Action.admit := ⟨⟩

theorem rails_admit : Regula.ExecutableContract StepSizeRails.admit (fun admit =>
    ∀ config : Acorn.Config, (admit config).isSome = true) :=
  ⟨fun config => Option.isSome_iff_ne_none.mpr (rails_admission_total config)⟩

structure SquaredAdmit where
  envelope : Nat
  forecast : Binary32
  outcome : Binary32

theorem squared_admit : Regula.ExecutableContract Agreement.admitSquared (fun admit =>
    Regula.Decides (· = true)
      (fun input : SquaredAdmit => input.forecast.Finite ∧ input.outcome.Finite ∧
        Agreement.squaredUnits input.forecast input.outcome ≤ input.envelope ^ 2)
      (Regula.Dependent.isSome fun input : SquaredAdmit =>
        admit input.envelope input.forecast input.outcome)) :=
  ⟨present
    (fun input => by
      unfold Agreement.admitSquared
      by_cases finite : input.forecast.Finite ∧ input.outcome.Finite
      · rw [ite_eq_left finite, dite_isSome, Nat.lt_succ_iff]
        exact ⟨fun within => ⟨finite.1, finite.2, within⟩, fun accepted => accepted.2.2⟩
      · rw [ite_eq_right finite]
        exact ⟨fun accepted => by simp at accepted,
          fun accepted => absurd ⟨accepted.1, accepted.2.1⟩ finite⟩)
    ⟨⟨0, .zero, .zero⟩, by decide⟩ ⟨⟨0, ⟨0x7fc00000⟩, .zero⟩, by decide⟩⟩

theorem Agreement_admitSquared_registered : Regula.RegisteredDecision @Agreement.admitSquared := ⟨⟩

theorem squared_admit_value : Regula.ExecutableContract Agreement.admitSquared (fun admit =>
    ∀ (envelope : Nat) (forecast outcome : Binary32) (sample : Fin (envelope ^ 2 + 1)),
      admit envelope forecast outcome = some sample →
        sample.val = Agreement.squaredUnits forecast outcome) :=
  ⟨Agreement.admitSquared_exact⟩

theorem event_admit : Regula.ExecutableContract Event.admit (fun admit =>
    Regula.Decides (· = true)
      (fun input : Features.Config × (UInt64 × UInt16) =>
        ∃ event : Event input.1, input.2 = event.words)
      (Regula.Dependent.isSome fun input : Features.Config × (UInt64 × UInt16) =>
        admit input.1 input.2)) :=
  ⟨.of_iff (fun input => written (fun _ => Event.words_roundtrip _) Event.admit_words input.2)
    ⟨(bank, (0, 0)), by decide⟩ ⟨(bank, (0, 1)), by decide⟩⟩

theorem Event_admit_registered : Regula.RegisteredDecision @Event.admit := ⟨⟩

theorem event_admit_value : Regula.ExecutableContract Event.admit (fun admit =>
    ∀ (config : Features.Config) (event : Event config),
      admit config event.words = some event) :=
  ⟨fun _ => Event.words_roundtrip⟩

theorem last_admit : Regula.ExecutableContract admitLast (fun admit =>
    Regula.Decides (· = true)
      (fun input : Features.Config × LastWords =>
        ∃ last : Option (Event input.1), input.2 = lastWords last)
      (Regula.Dependent.isSome fun input : Features.Config × LastWords =>
        admit input.1 input.2)) :=
  ⟨.of_iff (fun input => written (fun _ => admitLast_roundtrip _) admitLast_words input.2)
    ⟨(bank, (0, 0, 0)), by decide⟩ ⟨(bank, (2, 0, 0)), by decide⟩⟩

theorem admitLast_registered : Regula.RegisteredDecision @admitLast := ⟨⟩

theorem last_admit_value : Regula.ExecutableContract admitLast (fun admit =>
    ∀ (config : Features.Config) (last : Option (Event config)),
      admit config (lastWords last) = some last) :=
  ⟨fun _ => admitLast_roundtrip⟩

structure ProgressAdmit where
  config : Features.Config
  clock : UInt64
  raw : ProgressWords

theorem progress_admit : Regula.ExecutableContract Progress.admit (fun admit =>
    Regula.Decides (· = true)
      (fun input : ProgressAdmit => ∃ progress : Progress input.config,
        input.clock = progress.clock ∧ input.raw = progress.words)
      (Regula.Dependent.isSome fun input : ProgressAdmit =>
        admit input.config input.clock input.raw)) :=
  ⟨.of_iff
    (fun input => by
      change (Progress.admit input.config input.clock input.raw).isSome = true ↔ _
      constructor
      · intro accepted
        obtain ⟨progress, admitted⟩ := Option.isSome_iff_exists.mp accepted
        exact ⟨progress, Progress.admit_words _ _ _ admitted⟩
      · rintro ⟨progress, clock, words⟩
        rw [clock, words, Progress.words_roundtrip]
        rfl)
    ⟨⟨bank, 0, ⟨0, 0, 0, (0, 0, 0), [(0, 0, .zero)]⟩⟩, by decide⟩
    ⟨⟨bank, 0, ⟨0, 0, 0, (0, 0, 0), []⟩⟩, by decide⟩⟩

theorem Progress_admit_registered : Regula.RegisteredDecision @Progress.admit := ⟨⟩

theorem progress_admit_value : Regula.ExecutableContract Progress.admit (fun admit =>
    ∀ (config : Features.Config) (progress : Progress config),
      admit config progress.clock progress.words = some progress) :=
  ⟨fun _ => Progress.words_roundtrip⟩

structure AssignmentAdmit where
  dimension : Dimension
  config : Features.Config
  raw : AssignmentWords

theorem assignment_admit : Regula.ExecutableContract Assignment.admit (fun admit =>
    Regula.Decides (· = true)
      (fun input : AssignmentAdmit => ∃ assignment : Assignment input.config,
        input.raw = assignment.words input.dimension)
      (Regula.Dependent.isSome fun input : AssignmentAdmit =>
        admit input.dimension input.config input.raw)) :=
  ⟨.of_iff
    (fun input => written (fun _ => Assignment.words_roundtrip input.dimension _)
      (Assignment.admit_words input.dimension) input.raw)
    ⟨⟨narrow, bank, ⟨0, 0, 0, 0⟩⟩, by decide⟩ ⟨⟨narrow, bank, ⟨2, 0, 0, 0⟩⟩, by decide⟩⟩

theorem Assignment_admit_registered : Regula.RegisteredDecision @Assignment.admit := ⟨⟩

theorem assignment_admit_value : Regula.ExecutableContract Assignment.admit (fun admit =>
    ∀ (dimension : Dimension) (config : Features.Config) (assignment : Assignment config),
      admit dimension config (assignment.words dimension) = some assignment) :=
  ⟨fun dimension _ => Assignment.words_roundtrip dimension⟩

structure BoxChecked where
  config : Host.WorldConfig
  x : Int
  y : Int

private theorem checked_coordinates {config : Host.WorldConfig} (raw : Int × Int)
    (position : Host.BoxPosition config)
    (admitted : Host.BoxPosition.checked config raw.1 raw.2 = some position) :
    raw = (position.position.x.val, position.position.y.val) := by
  unfold Host.BoxPosition.checked at admitted
  split at admitted
  · rename_i column
    split at admitted
    · rename_i row
      cases admitted
      simp [Host.BoxPosition.position, Int.toNat_of_nonneg column.1, Int.toNat_of_nonneg row.1]
    · contradiction
  · contradiction

theorem box_position_checked : Regula.ExecutableContract Host.BoxPosition.checked
    (fun checked =>
      Regula.Decides (· = true)
        (fun input : BoxChecked => ∃ position : Host.BoxPosition input.config,
          (input.x, input.y) = (position.position.x.val, position.position.y.val))
        (Regula.Dependent.isSome fun input : BoxChecked =>
          checked input.config input.x input.y)) :=
  ⟨.of_iff
    (fun input => written (parse := fun raw : Int × Int =>
      Host.BoxPosition.checked input.config raw.1 raw.2)
      (fun _ => Host.BoxPosition.checked_position _) checked_coordinates (input.x, input.y))
    ⟨⟨wide, 0, 0⟩, by decide⟩ ⟨⟨wide, -1, 0⟩, by decide⟩⟩

theorem Host_BoxPosition_checked_registered :
    Regula.RegisteredDecision @Host.BoxPosition.checked := ⟨⟩

theorem box_position_checked_value : Regula.ExecutableContract Host.BoxPosition.checked
    (fun checked =>
      ∀ (config : Host.WorldConfig) (position : Host.BoxPosition config),
        checked config position.position.x.val position.position.y.val = some position) :=
  ⟨fun _ => Host.BoxPosition.checked_position⟩

theorem campaign_admit : Regula.ExecutableContract Host.CampaignPlan.admit (fun admit =>
    Regula.Decides (· = true)
      (fun input : Nat × Host.CampaignSpec => 0 < input.2.steps.toNat ∧
        (input.2.cycles.toNat ≠ 0 ∨ 0 < min input.2.goals.toNat input.1))
      (Regula.Dependent.isOk fun input : Nat × Host.CampaignSpec => admit input.1 input.2)) :=
  ⟨succeeds
    (fun input => by
      unfold Host.CampaignPlan.admit
      by_cases steps : 0 < input.2.steps.toNat
      · by_cases productive : input.2.cycles.toNat ≠ 0 ∨ 0 < min input.2.goals.toNat input.1
        · simp [steps, productive, Except.isOk, Except.toBool]
        · simp [steps, productive, Except.isOk, Except.toBool]
      · simp [steps, Except.isOk, Except.toBool])
    ⟨(0, ⟨1, 0, 0, 1⟩), by decide⟩ ⟨(0, ⟨0, 0, 0, 0⟩), by decide⟩⟩

theorem Host_CampaignPlan_admit_registered :
    Regula.RegisteredDecision @Host.CampaignPlan.admit := ⟨⟩

theorem assignment_distinct : Regula.ExecutableContract @Assignment.distinct (fun test =>
    Regula.Decides (· = true)
      (fun input : (config : Features.Config) ×
          Vector (Assignment config) Acorn.FeatureConstants.skillCount =>
        ∀ (left right : Fin Acorn.FeatureConstants.skillCount)
          (unit : Fin input.1.units.count) (first second : Bonus),
          input.2[left.val] = .selected unit first →
            input.2[right.val] = .selected unit second → left = right)
      (fun input : (config : Features.Config) ×
          Vector (Assignment config) Acorn.FeatureConstants.skillCount =>
        @test input.1 input.2)) :=
  ⟨decides
    (fun input => by
      show Assignment.distinct input.2 = true ↔ _
      rw [Assignment.distinct_iff]
      constructor
      · intro distinct left right unit first second held other
        exact distinct left right unit (by rw [held]; rfl) (by rw [other]; rfl)
      · intro distinct left right unit held other
        cases first : input.2[left.val] with
        | neutral =>
          rw [first] at held
          contradiction
        | selected leftUnit leftBonus =>
          cases second : input.2[right.val] with
          | neutral =>
            rw [second] at other
            contradiction
          | selected rightUnit rightBonus =>
            rw [first] at held
            rw [second] at other
            cases held
            cases other
            exact distinct left right _ leftBonus rightBonus first second)
    ⟨⟨bank, .replicate _ .neutral⟩, fun left right unit first second held => by
      simp at held⟩
    ⟨⟨bank, .replicate _ chosen⟩, fun distinct =>
      absurd (distinct ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ spark spark
        (by simp [chosen]) (by simp [chosen])) (by decide)⟩⟩

theorem Assignment_distinct_registered : Regula.RegisteredDecision @Assignment.distinct := ⟨⟩

theorem harvest_key : Regula.ExecutableContract Host.harvestKey (fun admit =>
    Regula.Decides (· = true)
      (fun input : Host.WorldConfig × Host.Position =>
        (-1 ≤ input.2.x.val ∧ input.2.x.val ≤ input.1.side) ∧
          (-1 ≤ input.2.y.val ∧ input.2.y.val ≤ input.1.side))
      (Regula.Dependent.isSome fun input : Host.WorldConfig × Host.Position =>
        admit input.1 input.2)) :=
  ⟨present
    (fun input => by
      unfold Host.harvestKey
      by_cases column : -1 ≤ input.2.x.val ∧ input.2.x.val ≤ input.1.side
      · by_cases row : -1 ≤ input.2.y.val ∧ input.2.y.val ≤ input.1.side <;>
          simp [column, row]
      · simp [column])
    ⟨(wide, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩), by decide⟩
    ⟨(wide, ⟨⟨-2, by decide⟩, ⟨0, by decide⟩⟩), by decide⟩⟩

theorem Host_harvestKey_registered : Regula.RegisteredDecision @Host.harvestKey := ⟨⟩

structure MapIndex where
  side : MapSide
  x : Int
  y : Int

theorem map_index : Regula.ExecutableContract mapIndex (fun admit =>
    Regula.Decides (· = true)
      (fun input : MapIndex =>
        0 ≤ input.x ∧ input.x < input.side.val ∧ 0 ≤ input.y ∧ input.y < input.side.val)
      (Regula.Dependent.isSome fun input : MapIndex => admit input.side input.x input.y)) :=
  ⟨present
    (fun input => by
      unfold mapIndex
      split <;> simp_all)
    ⟨⟨⟨1, by decide⟩, 0, 0⟩, by decide⟩ ⟨⟨⟨1, by decide⟩, -1, 0⟩, by decide⟩⟩

theorem mapIndex_registered : Regula.RegisteredDecision @mapIndex := ⟨⟩

theorem sse_line : Regula.ExecutableContract sseLine (fun admit =>
    Regula.Decides (· = true)
      (fun input : Nat × String => input.2.utf8ByteSize ≤ input.1 ∧
        input.2.contains '\n' = false ∧ input.2.contains '\r' = false)
      (Regula.Dependent.isSome fun input : Nat × String => admit input.1 input.2)) :=
  ⟨present (fun _ => dite_isSome _) ⟨(0, ""), by simp⟩ ⟨(0, "\n"), by simp⟩⟩

theorem sseLine_registered : Regula.RegisteredDecision @sseLine := ⟨⟩

theorem checkpoint_decode : Regula.ExecutableContract Checkpoint.decode
    (Regula.Decides (·.isSome = true)
      (fun bytes : List UInt8 => ∃ payload : Checkpoint.Payload, bytes = Checkpoint.encode payload)) :=
  ⟨decides (fun bytes => written Checkpoint.roundtrip Checkpoint.decode_written bytes)
    ⟨Checkpoint.encode (Checkpoint.snapshot ranked ranked.initial), _, rfl⟩
    ⟨[], fun ⟨payload, same⟩ => by
      simp [Checkpoint.encode, Checkpoint.magic, Acorn.FeatureConstants.checkpointMagic] at same⟩⟩

theorem Checkpoint_decode_registered : Regula.RegisteredDecision @Checkpoint.decode := ⟨⟩

theorem checkpoint_decode_value : Regula.ExecutableContract Checkpoint.decode (fun decode =>
    ∀ payload : Checkpoint.Payload, decode (Checkpoint.encode payload) = some payload) :=
  ⟨Checkpoint.roundtrip⟩

structure SaveBytes where
  construction : AgentConstruction
  state : construction.State

theorem checkpoint_save : Regula.ExecutableContract Checkpoint.saveBytes (fun save =>
    Regula.Decides (·.isOk = true)
      (fun input : SaveBytes => Resumable input.construction.profile)
      (fun input : SaveBytes => save input.construction input.state)) :=
  ⟨decides
    (fun input => by
      change (Checkpoint.saveBytes input.construction input.state).isOk = true ↔ _
      rw [← resumable_iff]
      cases supported : input.construction.profile.checkpointSupported with
      | true => simp [Checkpoint.save_supported input.construction input.state supported,
          Except.isOk, Except.toBool]
      | false => simp [Checkpoint.save_refuses input.construction input.state supported,
          Except.isOk, Except.toBool])
    ⟨⟨construction resumable, AgentConstruction.initial _⟩, rfl, rfl, rfl, rfl⟩
    ⟨⟨construction primitive, AgentConstruction.initial _⟩,
      fun supported => nomatch supported.1⟩⟩

theorem Checkpoint_saveBytes_registered : Regula.RegisteredDecision @Checkpoint.saveBytes := ⟨⟩

private theorem holds_selected {config : Features.Config} (unit : Fin config.units.count)
    (assignment : Assignment config) :
    assignment.holds unit = true ↔ ∃ bonus, assignment = .selected unit bonus := by
  cases assignment with
  | neutral => simp [Assignment.holds]
  | selected other bonus =>
    simp only [Assignment.holds, beq_iff_eq, Assignment.selected.injEq]
    exact ⟨fun same => ⟨bonus, same, rfl⟩, fun ⟨_, same, _⟩ => same⟩

structure AssignmentHolds where
  config : Features.Config
  unit : Fin config.units.count
  assignment : Assignment config

theorem assignment_holds : Regula.ExecutableContract @Assignment.holds (fun test =>
    Regula.Decides (· = true)
      (fun input : AssignmentHolds => ∃ bonus, input.assignment = .selected input.unit bonus)
      (fun input : AssignmentHolds => @test input.config input.unit input.assignment)) :=
  ⟨decides (fun input => holds_selected input.unit input.assignment)
    ⟨⟨bank, ⟨0, by decide⟩, chosen⟩, spark, rfl⟩
    ⟨⟨bank, ⟨0, by decide⟩, .neutral⟩, fun ⟨_, same⟩ => nomatch same⟩⟩

theorem Assignment_holds_registered : Regula.RegisteredDecision @Assignment.holds := ⟨⟩

structure AssignmentSame where
  config : Features.Config
  left : Assignment config
  right : Assignment config

theorem assignment_same : Regula.ExecutableContract @Assignment.same (fun test =>
    Regula.Decides (· = true)
      (fun input : AssignmentSame => input.left.identity = input.right.identity)
      (fun input : AssignmentSame => @test input.config input.left input.right)) :=
  ⟨decides (fun input => Assignment.same_iff input.left input.right)
    ⟨⟨bank, .neutral, .neutral⟩, rfl⟩ ⟨⟨bank, .neutral, chosen⟩, fun same => nomatch same⟩⟩

theorem Assignment_same_registered : Regula.RegisteredDecision @Assignment.same := ⟨⟩

structure InterestSame where
  config : Features.Config
  interest : Features.Interest config
  target : Assignment config

theorem interest_same : Regula.ExecutableContract @Features.Interest.sameAssignment (fun test =>
    Regula.Decides (· = true)
      (fun input : InterestSame =>
        ∃ prior, input.interest = .learned prior ∧ prior.identity = input.target.identity)
      (fun input : InterestSame => @test input.config input.interest input.target)) :=
  ⟨decides (fun input => Features.Interest.sameAssignment_iff input.interest input.target)
    ⟨⟨bank, .learned .neutral, .neutral⟩, .neutral, rfl, rfl⟩
    ⟨⟨bank, .learned .neutral, chosen⟩, fun ⟨prior, learned, same⟩ => by
      cases learned
      exact nomatch same⟩⟩

theorem Features_Interest_sameAssignment_registered :
    Regula.RegisteredDecision @Features.Interest.sameAssignment := ⟨⟩

theorem less_useful : Regula.ExecutableContract @Features.Lifecycle.lessUseful (fun test =>
    ∀ {shape actions config criterion dimension discounts}
      (state : Features.Lifecycle shape actions config criterion dimension discounts)
      (unit other : Fin config.units.count),
      test state unit other = true ↔
        state.progress.units[unit.val].utility.value.key <
          state.progress.units[other.val].utility.value.key) :=
  ⟨Features.Lifecycle.lessUseful_iff⟩

structure Consistent where
  count : Word.Count
  snapshot : PolicySnapshot count
  behaviour : Vector Binary32 count.word.toNat

theorem snapshot_consistent : Regula.ExecutableContract @PolicySnapshot.consistent (fun test =>
    Regula.Decides (· = true)
      (fun input : Consistent => input.snapshot.probabilities = input.behaviour)
      (fun input : Consistent => @test input.count input.snapshot input.behaviour)) :=
  ⟨decides (fun input => PolicySnapshot.consistent_iff input.snapshot input.behaviour)
    ⟨⟨metaCount, level, level.probabilities⟩, rfl⟩
    ⟨⟨metaCount, level, Vector.replicate _ .zero⟩, by decide +kernel⟩⟩

theorem PolicySnapshot_consistent_registered :
    Regula.RegisteredDecision @PolicySnapshot.consistent := ⟨⟩

structure AssignmentUsing where
  dimension : Dimension
  config : Features.Config
  slot : Fin config.units.count → FeatIdx dimension
  raw : AssignmentWords

theorem assignment_admit_using : Regula.ExecutableContract Assignment.admitUsing (fun admit =>
    Regula.Decides (· = true)
      (fun input : AssignmentUsing => ∃ assignment : Assignment input.config,
        input.raw = Assignment.wordsUsing input.slot assignment)
      (Regula.Dependent.isSome fun input : AssignmentUsing =>
        admit input.dimension input.config input.slot input.raw)) :=
  ⟨.of_iff
    (fun input => written (fun _ => Assignment.wordsUsing_roundtrip input.dimension input.slot _)
      (Assignment.admitUsing_words input.dimension input.slot) input.raw)
    ⟨⟨narrow, bank, fun _ => ⟨0, by decide⟩, ⟨0, 0, 0, 0⟩⟩, by decide⟩
    ⟨⟨narrow, bank, fun _ => ⟨0, by decide⟩, ⟨2, 0, 0, 0⟩⟩, by decide⟩⟩

theorem Assignment_admitUsing_registered : Regula.RegisteredDecision @Assignment.admitUsing := ⟨⟩

theorem assignment_admit_using_value :
    Regula.ExecutableContract Assignment.admitUsing (fun admit =>
      ∀ (dimension : Dimension) (config : Features.Config)
        (slot : Fin config.units.count → FeatIdx dimension) (assignment : Assignment config),
        admit dimension config slot (Assignment.wordsUsing slot assignment) = some assignment) :=
  ⟨fun dimension _ => Assignment.wordsUsing_roundtrip dimension⟩

structure ControllerStep where
  config : Acorn.Config
  dimension : Dimension
  actions : Nat
  controller : Controller config dimension actions
  features : SwiftTd.ActiveSet dimension
  raw : Nat
  reward : Binary32

theorem controller_step_raw : Regula.ExecutableContract @Controller.stepRaw (fun step =>
    Regula.Decides (· = true) (fun input : ControllerStep => input.raw < input.actions)
      (Regula.Dependent.isSome fun input : ControllerStep =>
        @step input.config input.dimension input.actions input.controller input.features
          input.raw input.reward)) :=
  ⟨present
    (fun input => by
      unfold Controller.stepRaw Action.admit
      by_cases inside : input.raw < input.actions <;> simp [inside])
    ⟨⟨⟨.control, .differential⟩, narrow, 1, .initial _ _ _, .empty _, 0, .zero⟩, by decide⟩
    ⟨⟨⟨.control, .differential⟩, narrow, 1, .initial _ _ _, .empty _, 1, .zero⟩, by decide⟩⟩

theorem Controller_stepRaw_registered : Regula.RegisteredDecision @Controller.stepRaw := ⟨⟩

structure AgentRestore where
  interface : Interface
  profile : FeatureProfile
  config : Features.Config
  criterion : Criterion
  dimension : Dimension
  planning : PlanningSelection
  state : Agent interface profile config criterion dimension planning
  image : AgentImage interface profile config criterion dimension

theorem agent_restore : Regula.ExecutableContract @Agent.restore (fun restore =>
    Regula.Decides (· = true) (fun input : AgentRestore => Resumable input.profile)
      (Regula.Dependent.isSome fun input : AgentRestore =>
        @restore input.interface input.profile input.config input.criterion input.dimension
          input.planning input.state input.image)) :=
  ⟨present
    (fun input => by
      rw [← resumable_iff]
      cases supported : input.profile.checkpointSupported <;> simp [Agent.restore, supported])
    ⟨⟨Grid.interface, resumable, bank, .discounted, narrow, .none, .initial _ _ _ _ _ _,
      (Agent.initial _ _ _ _ _ PlanningSelection.none).image⟩, rfl, rfl, rfl, rfl⟩
    ⟨⟨Grid.interface, primitive, bank, .discounted, narrow, .none, .initial _ _ _ _ _ _,
      (Agent.initial _ _ _ _ _ PlanningSelection.none).image⟩,
      fun supported => nomatch supported.1⟩⟩

theorem Agent_restore_registered : Regula.RegisteredDecision @Agent.restore := ⟨⟩

structure PredictionAdvance where
  profile : FeatureProfile
  criterion : Criterion
  dimension : Dimension
  state : PredictionControl Grid.interface profile criterion dimension
  config : Features.Config
  bank : Bank Host.patchShape config
  obs : Host.Observation
  reward : Binary32
  raw : Nat
  own : Bool

theorem prediction_advance_raw :
    Regula.ExecutableContract @PredictionControl.advanceRaw (fun advance =>
      Regula.Decides (· = true)
        (fun input : PredictionAdvance => input.raw < Acorn.FeatureConstants.primitiveCount)
        (Regula.Dependent.isSome fun input : PredictionAdvance =>
          @advance input.profile input.criterion input.dimension input.state input.config
            input.bank input.obs input.reward input.raw input.own)) :=
  ⟨present
    (fun input => by
      change ((Action.admit Acorn.FeatureConstants.primitiveCount input.raw).map _).isSome =
        true ↔ _
      cases admitted : Action.admit Acorn.FeatureConstants.primitiveCount input.raw with
      | none =>
        have outside := (Action.admit_none _ _).mp admitted
        exact ⟨fun present => absurd present Bool.false_ne_true,
          fun inside => absurd inside (Nat.not_lt.mpr outside)⟩
      | some action =>
        have inside : ¬Acorn.FeatureConstants.primitiveCount ≤ input.raw := fun outside =>
          absurd ((Action.admit_none _ _).mpr outside) (by simp [admitted])
        exact ⟨fun _ => Nat.lt_of_not_le inside, fun _ => rfl⟩)
    ⟨⟨resumable, .discounted, narrow, .initial _ _ _ _, bank, .initial _ _, blank, .zero, 0,
      false⟩, by decide⟩
    ⟨⟨resumable, .discounted, narrow, .initial _ _ _ _, bank, .initial _ _, blank, .zero,
      Acorn.FeatureConstants.primitiveCount, false⟩, by decide⟩⟩

theorem PredictionControl_advanceRaw_registered :
    Regula.RegisteredDecision @PredictionControl.advanceRaw := ⟨⟩

structure PredicateEval where
  arity : Nat
  values : Fin arity → Nat
  program : ClockProgram.Predicate arity

def Ordered (input : PredicateEval) : Prop :=
  (∀ values : Fin 6 → Nat, input = ⟨6, values, ClockProgram.agreementFollows⟩ →
      values 0 = values 3 →
        values 5 = 0 ∧ (values 4 < values 1 ∨ (values 1 = values 4 ∧ values 2 = 1))) ∧
    ∀ values : Fin 14 → Nat, input = ⟨14, values, ClockProgram.snapshotFollows⟩ →
      values 0 = values 7 → values 9 = 0 ∧ values 8 ≤ values 1

theorem predicate_eval : Regula.ExecutableContract @ClockProgram.Predicate.eval (fun eval =>
    Regula.DecidesSoundly (· = true) Ordered
      (fun input : PredicateEval => @eval input.arity input.values input.program)) :=
  ⟨{ sound := fun input accepted =>
       ⟨fun values same clocks => by
          subst same
          exact ClockProgram.agreementFollows_same values clocks accepted,
        fun values same clocks => by
          subst same
          exact ClockProgram.snapshotFollows_same values clocks accepted⟩
     accepted := ⟨⟨14, fun index => if index = 4 then 1 else 0, ClockProgram.snapshotFollows⟩,
       ClockProgram.snapshotFollows_goal _ (by decide) (by decide) (by decide) (by decide)
         (by decide)⟩ }⟩

theorem ClockProgram_Predicate_eval_registered :
    Regula.RegisteredDecision @ClockProgram.Predicate.eval := ⟨⟩

theorem predicate_eval_programs :
    Regula.ExecutableContract @ClockProgram.Predicate.eval (fun eval =>
    ∀ values : Fin 14 → Nat, values 0 = values 7 → values 1 = values 8 → values 9 = 0 →
      values 3 = values 10 → values 11 < values 4 →
        eval values ClockProgram.snapshotFollows = true) :=
  ⟨ClockProgram.snapshotFollows_goal⟩

structure CandidateWeight where
  dimension : Dimension
  config : Features.Config
  weights : WeightArray (.discounted .g99) dimension
  unit : Fin config.units.count

theorem candidate_of_weight : Regula.ExecutableContract @candidateOfWeight (fun admit =>
    Regula.Decides (· = true)
      (fun input : CandidateWeight =>
        0 < (input.weights.get (unitFeature input.dimension input.config input.unit)).value.key)
      (Regula.Dependent.isSome fun input : CandidateWeight =>
        @admit input.dimension input.config input.weights input.unit)) :=
  ⟨present (fun _ => @dite_isSome _ _ (Binary32.positiveDecidable _) _)
    ⟨⟨double, pair, split, ⟨0, by decide⟩⟩, by decide⟩
    ⟨⟨double, pair, split, ⟨1, by decide⟩⟩, by decide⟩⟩

theorem candidateOfWeight_registered : Regula.RegisteredDecision @candidateOfWeight := ⟨⟩

theorem candidate_of_weight_value : Regula.ExecutableContract @candidateOfWeight (fun admit =>
    ∀ (dimension : Dimension) (config : Features.Config)
      (weights : WeightArray (.discounted .g99) dimension) (unit : Fin config.units.count)
      (candidate : Candidate config), @admit dimension config weights unit = some candidate →
        candidate.key =
          (weights.get (unitFeature dimension config candidate.unit)).value.bits.toNat) :=
  ⟨candidateOfWeight_key⟩

private theorem held_selected {config : Features.Config} (interest : Interest config)
    (unit : Fin config.units.count) (bonus : Bonus) :
    interest.held = .selected unit bonus ↔ interest = .learned (.selected unit bonus) := by
  cases interest with
  | learned assignment =>
    exact ⟨fun same => congrArg Interest.learned same, fun same => Interest.learned.inj same⟩
  | declared origin tag => exact ⟨fun same => (nomatch same), fun same => (nomatch same)⟩

def Replaceable {shape : PatchShape} {actions : Word.Count} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount}
    (state : Features.Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit : Fin config.units.count) : Prop :=
  state.progress.units[unit.val].birth.toNat + config.tester.maturity <
      state.progress.clock.toNat ∧
    (free = true ∨ ∀ skill ∈ state.consumers.skills.toList,
      ∀ bonus, skill.interest ≠ .learned (.selected unit bonus))

private theorem eligible_iff {shape : PatchShape} {actions : Word.Count}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : Features.Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit : Fin config.units.count) :
    state.eligible free unit = true ↔ Replaceable state free unit := by
  have held : ∀ assignment : Assignment config,
      ¬assignment.holds unit = true ↔ ∀ bonus, assignment ≠ .selected unit bonus := by
    intro assignment
    cases assignment with
    | neutral => simp [Assignment.holds]
    | selected other bonus =>
      simp only [Assignment.holds, beq_iff_eq, ne_eq, Assignment.selected.injEq, not_and]
      constructor
      · intro differs _ same
        exact absurd same differs
      · intro differs same
        exact differs bonus same rfl
  simp only [Features.Lifecycle.eligible, Features.Lifecycle.mature, Ensemble.holds,
    Replaceable, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_false, held, ne_eq, held_selected]

theorem lifecycle_candidate :
    Regula.ExecutableContract @Features.Lifecycle.candidate (fun candidate =>
    ∀ {shape actions config criterion dimension discounts}
        (state : Features.Lifecycle shape actions config criterion dimension discounts)
        (free : Bool),
        (candidate state free = none ↔ ∀ unit, ¬Replaceable state free unit) ∧
          ∀ unit, candidate state free = some unit → Replaceable state free unit ∧
            ∀ other, Replaceable state free other →
              state.progress.units[unit.val].utility.value.key ≤
                state.progress.units[other.val].utility.value.key) :=
  ⟨fun state free =>
    ⟨by
      rw [Features.Lifecycle.candidate_none_iff, Features.Lifecycle.eligibleCount,
        List.countP_eq_zero]
      constructor
      · intro none unit replaceable
        exact none unit (List.mem_finRange unit) ((eligible_iff state free unit).mpr replaceable)
      · intro none unit _ eligible
        exact none unit ((eligible_iff state free unit).mp eligible),
    fun unit selected =>
      ⟨(eligible_iff state free unit).mp (state.candidate_eligible free unit selected),
        fun other replaceable =>
          state.candidate_least free unit selected other
            ((eligible_iff state free other).mpr replaceable)⟩⟩⟩

theorem total_ratio : Regula.ExecutableContract @Agreement.Total.ratio (fun ratio =>
    Regula.Decides (·.isSome = true)
      (fun input : (envelope : Nat) × Agreement.Total envelope =>
        0 < input.2.count.val ∧ 0 < input.1)
      (fun input : (envelope : Nat) × Agreement.Total envelope => @ratio input.1 input.2)) :=
  ⟨decides (fun input => (dite_isSome _).trans (product_positive _ _))
    ⟨⟨1, ⟨⟨1, by decide⟩, 0, Nat.zero_le _⟩⟩, by decide⟩
    ⟨⟨1, .empty 1⟩, by decide⟩⟩

theorem Agreement_Total_ratio_registered : Regula.RegisteredDecision @Agreement.Total.ratio := ⟨⟩

theorem channel_ratio : Regula.ExecutableContract @Agreement.Channel.ratio (fun ratio =>
    Regula.Decides (·.isSome = true)
      (fun input : (discount : Discount) × Agreement.Channel discount =>
        input.2.fault = none ∧ 0 < input.2.total.count.val)
      (fun input : (discount : Discount) × Agreement.Channel discount =>
        @ratio input.1 input.2)) :=
  ⟨decides
    (fun input => by
      have present : (Agreement.Total.ratio input.2.total).isSome = true ↔
          0 < input.2.total.count.val :=
        (dite_isSome _).trans ((product_positive _ _).trans
          ⟨fun positive => positive.1, fun count => ⟨count, envelope_positive input.1⟩⟩)
      show (Agreement.Channel.ratio input.2).isSome = true ↔ _
      unfold Agreement.Channel.ratio
      cases fault : input.2.fault with
      | some failure => simp
      | none => simpa using present)
    ⟨⟨.g99, ⟨⟨⟨1, by decide⟩, 0, Nat.zero_le _⟩, none, none, none, ⟨0, by decide⟩, none⟩⟩,
      rfl, by decide⟩
    ⟨⟨.g99, .empty .g99⟩, fun accepted => absurd accepted.2 (by decide)⟩⟩

theorem Agreement_Channel_ratio_registered :
    Regula.RegisteredDecision @Agreement.Channel.ratio := ⟨⟩

structure GoalHeadline where
  goals : Nat
  attempts : Nat
  state : GoalAchievement.State goals attempts

theorem goal_headline :
    Regula.ExecutableContract @GoalAchievement.State.headline (fun headline =>
      Regula.Decides (· = true)
        (fun input : GoalHeadline => input.state.invalid = false ∧ input.goals ≠ 0)
        (Regula.Dependent.isSome fun input : GoalHeadline =>
          @headline input.goals input.attempts input.state)) :=
  ⟨present
    (fun input => by
      cases invalid : input.state.invalid <;> by_cases empty : input.goals = 0 <;>
        simp [GoalAchievement.State.headline, invalid, empty])
    ⟨⟨1, 0, .empty 1 0⟩, rfl, by decide⟩ ⟨⟨0, 0, .empty 0 0⟩, fun accepted => accepted.2 rfl⟩⟩

theorem GoalAchievement_State_headline_registered :
    Regula.RegisteredDecision @GoalAchievement.State.headline := ⟨⟩

def Stopped {config : Host.WorldConfig} {α : Type} {goal : Host.Goal} {cap : UInt64}
    (attempt : Host.Attempt config α goal cap) : Prop :=
  attempt.steps.val = cap.toNat ∨
    (attempt.steps.val ≠ 0 ∧ attempt.run.carried.events.done = true)

structure AttemptFinished where
  config : Host.WorldConfig
  agent : Type
  goal : Host.Goal
  cap : UInt64
  attempt : Host.Attempt config agent goal cap

theorem attempt_finished : Regula.ExecutableContract @Host.Attempt.finished (fun finished =>
    Regula.Decides (· = true)
      (fun input : AttemptFinished => Stopped input.attempt)
      (fun input : AttemptFinished =>
        @finished input.config input.agent input.goal input.cap input.attempt)) :=
  ⟨decides
    (fun input => by
      show input.attempt.finished = true ↔ _
      simp [Host.Attempt.finished, Stopped])
    ⟨⟨_, _, _, 0, fresh 0⟩, Or.inl rfl⟩
    ⟨⟨_, _, _, 1, fresh 1⟩, fun stopped => Or.elim stopped (by decide) (fun later => later.1 rfl)⟩⟩

theorem Host_Attempt_finished_registered : Regula.RegisteredDecision @Host.Attempt.finished := ⟨⟩

structure BoundaryClosing where
  size : Nat
  plan : Host.CampaignPlan size
  decision : Host.BoundaryDecision plan

theorem boundary_closing :
    Regula.ExecutableContract @Host.BoundaryDecision.closing (fun closing =>
      Regula.Decides (· = true)
        (fun input : BoundaryClosing => input.decision = .complete ∨ input.decision = .stopped)
        (fun input : BoundaryClosing => @closing input.size input.plan input.decision)) :=
  ⟨decides
    (fun input => by
      show input.decision.closing = true ↔ _
      cases input.decision <;> simp [Host.BoundaryDecision.closing])
    ⟨⟨1, plan, .complete⟩, .inl rfl⟩
    ⟨⟨1, plan, .continue ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩,
      fun closing => closing.elim (nomatch ·) (nomatch ·)⟩⟩

theorem Host_BoundaryDecision_closing_registered :
    Regula.RegisteredDecision @Host.BoundaryDecision.closing := ⟨⟩

structure CheckpointDue where
  size : Nat
  plan : Host.CampaignPlan size
  capability : Host.WritableCheckpoint
  decision : Host.BoundaryDecision plan

theorem checkpoint_due_at :
    Regula.ExecutableContract @Host.WritableCheckpoint.dueAt (fun dueAt =>
      Regula.Decides (· = true)
        (fun input : CheckpointDue => input.decision = .complete ∨
          input.decision = .stopped ∨ input.capability.phase.val = 0)
        (fun input : CheckpointDue =>
          @dueAt input.size input.plan input.capability input.decision)) :=
  ⟨decides
    (fun input => by
      show input.capability.dueAt input.decision = true ↔ _
      cases input.decision <;>
        simp [Host.WritableCheckpoint.dueAt, Host.WritableCheckpoint.due,
          Host.BoundaryDecision.closing])
    ⟨⟨1, plan, writer, .complete⟩, .inl rfl⟩
    ⟨⟨1, plan, writer.advance, .continue ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩,
      fun due => due.elim (nomatch ·) (·.elim (nomatch ·) (fun zero => absurd zero (by decide)))⟩⟩

theorem Host_WritableCheckpoint_dueAt_registered :
    Regula.RegisteredDecision @Host.WritableCheckpoint.dueAt := ⟨⟩

structure MemberAt where
  bound : Nat
  item : Fin bound
  items : List (Fin bound)
  fits : bound < 2 ^ 32

theorem costed_mem : Regula.ExecutableContract @Costed.mem (fun mem =>
    Regula.Decides (fun result : Costed Bool => result.val = true)
      (fun input : MemberAt => input.item ∈ input.items)
      (fun input : MemberAt => @mem input.bound input.item input.items input.fits)) :=
  ⟨decides
    (fun input => by rw [Costed.mem_val]; exact decide_eq_true_iff)
    ⟨⟨2, 0, [0], by decide⟩, List.mem_singleton_self 0⟩
    ⟨⟨2, 0, [1], by decide⟩, by decide⟩⟩

theorem Costed_mem_registered : Regula.RegisteredDecision @Costed.mem := ⟨⟩

structure VectorsAt where
  count : Nat
  first : Vector Binary32 count
  second : Vector Binary32 count

theorem costed_vector_eq : Regula.ExecutableContract @Costed.vectorEq (fun vectorEq =>
    Regula.Decides (fun result : Costed Bool => result.val = true)
      (fun input : VectorsAt => input.first = input.second)
      (fun input : VectorsAt => @vectorEq input.count input.first input.second)) :=
  ⟨decides
    (fun input => by rw [Costed.vectorEq_val]; exact decide_eq_true_iff)
    ⟨⟨1, #v[⟨0⟩], #v[⟨0⟩]⟩, rfl⟩
    ⟨⟨1, #v[⟨0⟩], #v[⟨1⟩]⟩, by decide⟩⟩

theorem Costed_vectorEq_registered : Regula.RegisteredDecision @Costed.vectorEq := ⟨⟩

structure ListDecode where
  element : Type
  codec : Checkpoint.Codec element
  count : Nat
  bytes : List UInt8

theorem list_decode : Regula.ExecutableContract @Checkpoint.decodeList (fun decode =>
    Regula.DecidesCompletely (· = true)
      (fun input : ListDecode => ∃ written : List input.element × List UInt8,
        input.count = written.1.length ∧
          input.bytes = written.1.flatMap input.codec.encode ++ written.2)
      (Regula.Dependent.isSome fun input : ListDecode =>
        @decode input.element input.codec input.count input.bytes)) :=
  ⟨reads
    (fun input written same => by
      rw [same.1, same.2, Checkpoint.list_roundtrip]
      rfl)
    ⟨⟨UInt8, Checkpoint.byteCodec, 1, []⟩, by decide⟩⟩

theorem Checkpoint_decodeList_registered : Regula.RegisteredDecision @Checkpoint.decodeList := ⟨⟩

theorem list_decode_value : Regula.ExecutableContract @Checkpoint.decodeList (fun decode =>
    ∀ (α : Type) (codec : Checkpoint.Codec α) (values : List α) (suffix : List UInt8),
      @decode α codec values.length (values.flatMap codec.encode ++ suffix) =
        some (values, suffix)) :=
  ⟨fun _ => Checkpoint.list_roundtrip⟩

structure ListDecodeInto where
  element : Type
  codec : Checkpoint.Codec element
  count : Nat
  bytes : List UInt8
  reversed : List element

theorem list_decode_into : Regula.ExecutableContract @Checkpoint.decodeListInto (fun decode =>
    Regula.DecidesCompletely (· = true)
      (fun input : ListDecodeInto => ∃ written : List input.element × List UInt8,
        input.count = written.1.length ∧
          input.bytes = written.1.flatMap input.codec.encode ++ written.2)
      (Regula.Dependent.isSome fun input : ListDecodeInto =>
        @decode input.element input.codec input.count input.bytes input.reversed)) :=
  ⟨reads
    (fun input written same => by
      rw [same.1, same.2, Checkpoint.list_into_roundtrip]
      rfl)
    ⟨⟨UInt8, Checkpoint.byteCodec, 1, [], []⟩, by decide⟩⟩

theorem Checkpoint_decodeListInto_registered :
    Regula.RegisteredDecision @Checkpoint.decodeListInto := ⟨⟩

theorem list_decode_into_value :
    Regula.ExecutableContract @Checkpoint.decodeListInto (fun decode =>
      ∀ (α : Type) (codec : Checkpoint.Codec α) (values : List α) (suffix : List UInt8)
        (reversed : List α),
        @decode α codec values.length (values.flatMap codec.encode ++ suffix) reversed =
          some (reversed.reverse ++ values, suffix)) :=
  ⟨fun _ => Checkpoint.list_into_roundtrip⟩

structure FormatDecodeInto where
  element : Type
  format : Checkpoint.Format element
  count : Nat
  bytes : List UInt8
  reversed : List element

theorem format_decode_into : Regula.ExecutableContract @Checkpoint.Format.decodeInto
    (fun decode =>
      Regula.DecidesCompletely (· = true)
        (fun input : FormatDecodeInto => input.format.Lawful ∧
          ∃ written : List input.element × List UInt8, input.count = written.1.length ∧
            input.bytes = written.1.flatMap input.format.encode ++ written.2)
        (Regula.Dependent.isSome fun input : FormatDecodeInto =>
          @decode input.element input.format input.count input.bytes input.reversed)) :=
  ⟨{ complete := fun input ⟨lawful, written, same⟩ => by
        change (Checkpoint.Format.decodeInto input.format input.count input.bytes
          input.reversed).isSome = true
        rw [same.1, same.2, Checkpoint.Format.decodeInto_lawful lawful]
        rfl
     refused := ⟨⟨Nat, Checkpoint.Format.natural, 1, [], []⟩, nofun⟩ }⟩

theorem Checkpoint_Format_decodeInto_registered :
    Regula.RegisteredDecision @Checkpoint.Format.decodeInto := ⟨⟩

theorem format_decode_into_value :
    Regula.ExecutableContract @Checkpoint.Format.decodeInto (fun decode =>
      ∀ (α : Type) (format : Checkpoint.Format α), format.Lawful →
        ∀ (values : List α) (suffix : List UInt8) (reversed : List α),
          @decode α format values.length (values.flatMap format.encode ++ suffix) reversed =
            some (reversed.reverse ++ values, suffix)) :=
  ⟨fun _ _ lawful => Checkpoint.Format.decodeInto_lawful lawful⟩

structure BufferOffer where
  element : Type
  capacity : Nat
  buffer : Buffer element capacity
  value : element

theorem buffer_offer : Regula.ExecutableContract @Buffer.offer (fun offer =>
    Regula.Decides (· = true)
      (fun input : BufferOffer => input.buffer.values.length < input.capacity)
      (Regula.Dependent.isSome fun input : BufferOffer =>
        @offer input.element input.capacity input.buffer input.value)) :=
  ⟨present (fun input => Buffer.offer_iff input.buffer input.value)
    ⟨⟨Unit, 1, .empty, ()⟩, by decide⟩ ⟨⟨Unit, 0, .empty, ()⟩, by decide⟩⟩

theorem Buffer_offer_registered : Regula.RegisteredDecision @Buffer.offer := ⟨⟩

structure SchemaCovers where
  element : Type
  fits : String → element → TelemetryShape → Bool
  table : List (String × element)
  schema : List (String × TelemetryShape)

theorem schema_covers : Regula.ExecutableContract @schemaCovers (fun covers =>
    Regula.DecidesSoundly (· = true)
      (fun input : SchemaCovers => ∀ entry ∈ input.table, ∃ shape,
        (entry.1, shape) ∈ input.schema ∧ input.fits entry.1 entry.2 shape = true)
      (fun input : SchemaCovers =>
        @covers input.element input.fits input.table input.schema)) :=
  ⟨{ sound := fun input => schemaCovers_sound input.fits input.table input.schema
     accepted := ⟨⟨Bool, fun _ item _ => item, [("a", true)], [("a", .natural)]⟩, by decide⟩ }⟩

theorem schemaCovers_registered : Regula.RegisteredDecision @schemaCovers := ⟨⟩

theorem schema_covers_empty : Regula.ExecutableContract @schemaCovers (fun covers =>
    ∀ (α : Type) (fits : String → α → TelemetryShape → Bool)
      (schema : List (String × TelemetryShape)), @covers α fits [] schema = true) :=
  ⟨fun _ _ _ => rfl⟩

theorem find_index : Regula.ExecutableContract @Costed.findIdx? (fun find =>
    (∀ {α : Type} (items : Array α) (test : α → Costed Bool),
      ((find items test).val.val = none ↔ ∀ item ∈ items, (test item).val = false) ∧
        ∀ index, (find items test).val.val = some index ↔
          ∃ within : index < items.size, (test items[index]).val = true ∧
            ∀ earlier (before : earlier < index), (test items[earlier]).val = false) ∧
      (find #[false, true] (fun b => pure b)).val.val = some 1 ∧
      (find (#[] : Array Bool) (fun b => pure b)).val.val = none) :=
  ⟨⟨fun items test => by
    simp only [Costed.findIdx?_val, Array.findIdx?_eq_none_iff,
      Array.findIdx?_eq_some_iff_getElem, Bool.not_eq_true, implies_true, and_self],
    by simp [Costed.findIdx?_val, List.findIdx?_cons]; rfl,
    by simp only [Costed.findIdx?_val, Array.findIdx?_empty]⟩⟩

theorem assignment_identity : Regula.ExecutableContract @Assignment.identity (fun identity =>
    Regula.Decides (· = true)
      (fun input : (config : Features.Config) × Assignment config =>
        ∃ unit bonus, input.2 = .selected unit bonus)
      (Regula.Dependent.isSome fun input : (config : Features.Config) × Assignment config =>
        @identity input.1 input.2)) :=
  ⟨present
    (fun input => by
      cases input.2 with
      | neutral => simp [Assignment.identity]
      | selected unit bonus => simp [Assignment.identity])
    ⟨⟨bank, chosen⟩, ⟨0, by decide⟩, spark, rfl⟩
    ⟨⟨bank, .neutral⟩, fun ⟨_, _, same⟩ => nomatch same⟩⟩

theorem Assignment_identity_registered : Regula.RegisteredDecision @Assignment.identity := ⟨⟩

theorem assignment_identity_value :
    Regula.ExecutableContract @Assignment.identity (fun identity =>
      ∀ (config : Features.Config),
        @identity config .neutral = none ∧
          ∀ (unit : Fin config.units.count) (bonus : Bonus),
            @identity config (.selected unit bonus) = some unit) :=
  ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩⟩

structure TotalObserve where
  envelope : Nat
  total : Agreement.Total envelope
  sample : Fin (envelope ^ 2 + 1)

theorem total_observe : Regula.ExecutableContract @Agreement.Total.observe (fun observe =>
    Regula.Decides (· = true)
      (fun input : TotalObserve => input.total.count.val < Agreement.countLimit)
      (Regula.Dependent.isSome fun input : TotalObserve =>
        @observe input.envelope input.total input.sample)) :=
  ⟨present
    (fun input => by
      unfold Agreement.Total.observe
      rw [dite_isSome]
      exact Nat.add_lt_add_iff_right)
    ⟨⟨0, .empty 0, 0⟩, by decide⟩
    ⟨⟨0, ⟨⟨Agreement.countLimit, by decide⟩, 0, Nat.zero_le _⟩, 0⟩, by decide⟩⟩

theorem Agreement_Total_observe_registered :
    Regula.RegisteredDecision @Agreement.Total.observe := ⟨⟩

theorem total_observe_value : Regula.ExecutableContract @Agreement.Total.observe (fun observe =>
    ∀ (envelope : Nat) (total next : Agreement.Total envelope)
      (sample : Fin (envelope ^ 2 + 1)), @observe envelope total sample = some next →
        next.count.val = total.count.val + 1 ∧ next.sum = total.sum + sample.val) :=
  ⟨fun _ total next sample written => Agreement.Total.observe_exact total next sample written⟩

theorem action_direction : Regula.ExecutableContract Host.Action.direction
    (Regula.Decides (·.isSome = true) (fun action : Host.Action =>
      action = .north ∨ action = .south ∨ action = .east ∨ action = .west)) :=
  ⟨decides (fun action => by cases action <;> simp [Host.Action.direction])
    ⟨.north, .inl rfl⟩ ⟨.wait, by simp⟩⟩

theorem Host_Action_direction_registered : Regula.RegisteredDecision @Host.Action.direction := ⟨⟩

theorem world_step : Regula.ExecutableContract @Host.World.step (fun step =>
    ∀ (config : Host.WorldConfig) (world next : Host.World config) (action : Host.Action)
      (events : Host.StepResult), @step config world action = .ok (next, events) →
        next.time = world.time + 1) :=
  ⟨fun _ => Host.World.step_clock⟩

structure LifecycleMature where
  actions : Word.Count
  shape : PatchShape
  config : Features.Config
  criterion : Criterion
  dimension : Dimension
  discounts : List Discount
  state : Features.Lifecycle shape actions config criterion dimension discounts
  unit : Fin config.units.count

theorem lifecycle_mature : Regula.ExecutableContract @Features.Lifecycle.mature (fun mature =>
    Regula.Decides (· = true)
      (fun input : LifecycleMature =>
        input.state.progress.units[input.unit.val].birth.toNat + input.config.tester.maturity <
          input.state.progress.clock.toNat)
      (fun input : LifecycleMature =>
        @mature input.actions input.shape input.config input.criterion input.dimension
          input.discounts input.state input.unit)) :=
  ⟨decides (fun _ => decide_eq_true_iff)
    ⟨⟨_, _, _, _, _, _, lifecycle aged (.replicate _ (.learned .neutral)), ⟨0, by decide⟩⟩,
      by decide⟩
    ⟨⟨_, _, _, _, _, _, lifecycle (.initial bank) (.replicate _ (.learned .neutral)),
      ⟨0, by decide⟩⟩, by decide⟩⟩

theorem Features_Lifecycle_mature_registered :
    Regula.RegisteredDecision @Features.Lifecycle.mature := ⟨⟩

structure LifecycleEligible where
  actions : Word.Count
  shape : PatchShape
  config : Features.Config
  criterion : Criterion
  dimension : Dimension
  discounts : List Discount
  state : Features.Lifecycle shape actions config criterion dimension discounts
  free : Bool
  unit : Fin config.units.count

theorem lifecycle_eligible :
    Regula.ExecutableContract @Features.Lifecycle.eligible (fun eligible =>
      Regula.Decides (· = true)
        (fun input : LifecycleEligible => Replaceable input.state input.free input.unit)
        (fun input : LifecycleEligible =>
          @eligible input.actions input.shape input.config input.criterion input.dimension
            input.discounts input.state input.free input.unit)) :=
  ⟨decides (fun input => eligible_iff input.state input.free input.unit)
    ⟨⟨_, _, _, _, _, _, lifecycle aged (.replicate _ (.learned .neutral)), true,
      ⟨0, by decide⟩⟩, by decide, .inl rfl⟩
    ⟨⟨_, _, _, _, _, _, lifecycle (.initial bank) (.replicate _ (.learned .neutral)), true,
      ⟨0, by decide⟩⟩, fun replaceable => absurd replaceable.1 (by decide)⟩⟩

theorem Features_Lifecycle_eligible_registered :
    Regula.RegisteredDecision @Features.Lifecycle.eligible := ⟨⟩

structure EnsembleHolds where
  actions : Word.Count
  config : Features.Config
  criterion : Criterion
  dimension : Dimension
  discounts : List Discount
  ensemble : Ensemble actions config criterion dimension discounts
  unit : Fin config.units.count

theorem ensemble_holds : Regula.ExecutableContract @Ensemble.holds (fun holds =>
    Regula.Decides (· = true)
      (fun input : EnsembleHolds => ∃ skill ∈ input.ensemble.skills.toList, ∃ bonus,
        skill.interest = .learned (.selected input.unit bonus))
      (fun input : EnsembleHolds =>
        @holds input.actions input.config input.criterion input.dimension input.discounts
          input.ensemble input.unit)) :=
  ⟨decides
    (fun input => by
      show input.ensemble.holds input.unit = true ↔ _
      simp only [Ensemble.holds, List.any_eq_true, holds_selected, held_selected])
    ⟨⟨⟨1, by decide⟩, bank, .discounted, narrow, [],
      .initial _ _ _ _ (.replicate _ (.learned chosen)), ⟨0, by decide⟩⟩,
      Skill.initial _ _ _ (.learned chosen),
      by simp [Ensemble.initial, Acorn.FeatureConstants.skillCount], spark, rfl⟩
    ⟨⟨⟨1, by decide⟩, bank, .discounted, narrow, [],
      .initial _ _ _ _ (.replicate _ (.declared .spatialPotentials ⟨0, by decide⟩)),
      ⟨0, by decide⟩⟩,
      fun ⟨skill, member, bonus, learned⟩ => by
        simp only [Ensemble.initial, Vector.map_replicate, Vector.toList_replicate,
          List.mem_replicate] at member
        rw [member.2] at learned
        exact nomatch learned⟩⟩

theorem Ensemble_holds_registered : Regula.RegisteredDecision @Ensemble.holds := ⟨⟩

theorem lifecycle_prefer : Regula.ExecutableContract @Features.Lifecycle.prefer (fun prefer =>
    ∀ {shape actions config criterion dimension discounts}
      (state : Features.Lifecycle shape actions config criterion dimension discounts)
      (free : Bool) (best : Option (Fin config.units.count)) (unit : Fin config.units.count),
      (¬Replaceable state free unit → prefer state free best unit = best) ∧
        (Replaceable state free unit →
          prefer state free none unit = some unit ∧
            ∀ prior, prefer state free (some prior) unit =
              if state.progress.units[unit.val].utility.value.key <
                  state.progress.units[prior.val].utility.value.key then some unit
              else some prior)) :=
  ⟨fun state free best unit =>
    ⟨fun fixed => by
        have refused : state.eligible free unit = false :=
          Bool.eq_false_iff.mpr fun eligible =>
            fixed ((eligible_iff state free unit).mp eligible)
        simp [Features.Lifecycle.prefer, refused],
      fun replaceable => by
        have eligible := (eligible_iff state free unit).mpr replaceable
        refine ⟨by simp [Features.Lifecycle.prefer, eligible], fun prior => ?_⟩
        by_cases less : state.lessUseful unit prior = true
        · have strict := (state.lessUseful_iff unit prior).mp less
          simp [Features.Lifecycle.prefer, eligible, less, strict]
        · have refused := Bool.eq_false_iff.mpr less
          have loose : ¬(state.progress.units[unit.val].utility.value.key <
              state.progress.units[prior.val].utility.value.key) := fun strict =>
            less ((state.lessUseful_iff unit prior).mpr strict)
          simp [Features.Lifecycle.prefer, eligible, refused, loose]⟩⟩

structure AssignmentPotential where
  dimension : Dimension
  config : Features.Config
  assignment : Assignment config
  active : SwiftTd.ActiveSet dimension

theorem assignment_potential : Regula.ExecutableContract @Assignment.potential (fun potential =>
    Regula.Decides (· = true)
      (fun input : AssignmentPotential =>
        ∃ unit bonus, input.assignment = .selected unit bonus ∧
          unitFeature input.dimension input.config unit ∈ input.active.indices)
      (fun input : AssignmentPotential =>
        @potential input.dimension input.config input.assignment input.active)) :=
  ⟨decides
    (fun input => by
      show input.assignment.potential input.active = true ↔ _
      cases input.assignment with
      | neutral => simp [Assignment.potential_def, Assignment.feature]
      | selected unit bonus =>
        simp only [Assignment.potential_def, Assignment.feature, decide_eq_true_eq,
          Assignment.selected.injEq]
        exact ⟨fun member => ⟨unit, bonus, ⟨rfl, rfl⟩, member⟩,
          fun ⟨_, _, ⟨same, _⟩, member⟩ => same ▸ member⟩)
    ⟨⟨double, pair, .selected ⟨0, by decide⟩ spark, ⟨[⟨1, by decide⟩], by simp⟩⟩,
      ⟨0, by decide⟩, spark, rfl, by decide⟩
    ⟨⟨double, pair, .selected ⟨1, by decide⟩ spark, ⟨[⟨1, by decide⟩], by simp⟩⟩,
      fun ⟨_, _, same, member⟩ => by
        cases same
        exact absurd member (by decide)⟩⟩

theorem Assignment_potential_registered : Regula.RegisteredDecision @Assignment.potential := ⟨⟩

theorem episode_end : Regula.ExecutableContract @TemporalDecision.episodeEnd (fun episodeEnd =>
    Regula.Decides (·.isSome = true)
      (fun input : (actions : Word.Count) × TemporalDecision actions =>
        ∃ event, input.2.ended = some event)
      (fun input : (actions : Word.Count) × TemporalDecision actions =>
        @episodeEnd input.1 input.2)) :=
  ⟨decides
    (fun input => by
      show input.2.episodeEnd.isSome = true ↔ _
      simp [TemporalDecision.episodeEnd, Option.isSome_iff_exists])
    ⟨⟨⟨1, by decide⟩, ⟨.primitive, ⟨0, by decide⟩, .replicate _ .zero, .replicate _ .zero, false,
      .replicate _ .zero, none, none, some ⟨⟨0, by decide⟩, ⟨0, by decide⟩, .goal⟩⟩⟩, _, rfl⟩
    ⟨⟨⟨1, by decide⟩, ⟨.primitive, ⟨0, by decide⟩, .replicate _ .zero, .replicate _ .zero, false,
      .replicate _ .zero, none, none, none⟩⟩, fun ⟨_, same⟩ => nomatch same⟩⟩

theorem TemporalDecision_episodeEnd_registered :
    Regula.RegisteredDecision @TemporalDecision.episodeEnd := ⟨⟩

theorem episode_end_value :
    Regula.ExecutableContract @TemporalDecision.episodeEnd (fun episodeEnd =>
      ∀ {actions} (decision : TemporalDecision actions) (event : EndEvent),
        decision.ended = some event →
          ∃ ending, episodeEnd decision = some ending ∧ ending.slot = event.slot ∧
            ending.duration = event.age.val.toUInt32 ∧
            (ending.reason.val = 0 ↔ event.reason = .goal) ∧
            (ending.reason.val = 1 ↔ event.reason = .duration) ∧
            (ending.reason.val = 2 ↔ event.reason = .interrupted)) :=
  ⟨fun decision event ended => by
    simp only [TemporalDecision.episodeEnd, ended, Option.map_some]
    refine ⟨_, rfl, rfl, rfl, ?_⟩
    cases event.reason <;> simp⟩

structure AssignmentFeature where
  dimension : Dimension
  config : Features.Config
  assignment : Assignment config

theorem assignment_feature : Regula.ExecutableContract @Assignment.feature (fun feature =>
    Regula.Decides (· = true)
      (fun input : AssignmentFeature => ∃ unit bonus, input.assignment = .selected unit bonus)
      (Regula.Dependent.isSome fun input : AssignmentFeature =>
        @feature input.dimension input.config input.assignment)) :=
  ⟨present
    (fun input => by
      cases input.assignment with
      | neutral => simp [Assignment.feature]
      | selected unit bonus => simp [Assignment.feature])
    ⟨⟨narrow, bank, chosen⟩, ⟨0, by decide⟩, spark, rfl⟩
    ⟨⟨narrow, bank, .neutral⟩, fun ⟨_, _, same⟩ => nomatch same⟩⟩

theorem Assignment_feature_registered : Regula.RegisteredDecision @Assignment.feature := ⟨⟩

theorem assignment_feature_value :
    Regula.ExecutableContract @Assignment.feature (fun feature =>
      ∀ (dimension : Dimension) (config : Features.Config),
        @feature dimension config .neutral = none ∧
          ∀ (unit : Fin config.units.count) (bonus : Bonus),
            @feature dimension config (.selected unit bonus) =
              some (unitFeature dimension config unit)) :=
  ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩⟩

structure NextReady where
  dimension : Dimension
  entry : SwiftTd.Entry dimension
  before : Bool

theorem next_ready : Regula.ExecutableContract @SwiftTd.nextReady (fun next =>
    Regula.Decides (· = true)
      (fun input : NextReady =>
        (∃ delta vDelta decay, input.entry = .first delta vDelta decay) ∨
          (∃ target, input.entry = .terminal target) ∨ input.entry = .clear ∨
          input.entry = .release ∨
          (input.before = true ∧
            ((∃ features target, input.entry = .plan features target) ∨
              ∃ idx, input.entry = .retire idx)))
      (fun input : NextReady => @next input.dimension input.entry input.before)) :=
  ⟨decides
    (fun input => by
      show SwiftTd.nextReady input.entry input.before = true ↔ _
      cases input.entry <;> simp [SwiftTd.nextReady])
    ⟨⟨narrow, .clear, false⟩, .inr (.inr (.inl rfl))⟩
    ⟨⟨narrow, .retire ⟨0, by decide⟩, false⟩, by simp⟩⟩

theorem SwiftTd_nextReady_registered : Regula.RegisteredDecision @SwiftTd.nextReady := ⟨⟩

private theorem zero_read : Checkpoint.Format.decodeNatural [0] = some (0, []) := rfl

theorem natural_decode : Regula.ExecutableContract Checkpoint.Format.decodeNatural
    (fun decode =>
      Regula.Decides (·.isSome = true)
        (fun bytes : List UInt8 =>
          ∃ value rest, bytes = Checkpoint.Format.encodeNatural value ++ rest)
        decode) :=
  ⟨decides
    (fun bytes => by
      constructor
      · intro accepted
        obtain ⟨⟨value, rest⟩, read⟩ := Option.isSome_iff_exists.mp accepted
        exact ⟨value, rest, Checkpoint.Format.natural_canonical bytes value rest read⟩
      · rintro ⟨value, rest, rfl⟩
        rw [Checkpoint.Format.natural_lawful]
        rfl)
    ⟨[0], 0, [], Checkpoint.Format.natural_canonical _ _ _ zero_read⟩
    ⟨[], fun ⟨value, rest, same⟩ => by
      have read := Checkpoint.Format.natural_lawful value rest
      rw [← same] at read
      exact absurd read nofun⟩⟩

theorem Checkpoint_Format_decodeNatural_registered :
    Regula.RegisteredDecision @Checkpoint.Format.decodeNatural := ⟨⟩

theorem natural_decode_value : Regula.ExecutableContract Checkpoint.Format.decodeNatural
    (fun decode => ∀ (value : Nat) (suffix : List UInt8),
      decode (Checkpoint.Format.encodeNatural value ++ suffix) = some (value, suffix)) :=
  ⟨Checkpoint.Format.natural_lawful⟩

theorem natural_decode_into : Regula.ExecutableContract Checkpoint.Format.decodeNaturalInto
    (fun decode =>
      Regula.Decides (·.isSome = true)
        (fun input : List UInt8 × List Nat => ∃ value rest,
          input.1 = Checkpoint.Format.encodeNatural value ++ rest ∧ (input.2 = [] ∨ value ≠ 0))
        (Function.uncurry decode)) :=
  ⟨decides
    (fun input => by
      rcases input with ⟨bytes, lower⟩
      change (Checkpoint.Format.decodeNaturalInto bytes lower).isSome = true ↔ _
      have exact : ∀ value rest, Checkpoint.Format.decodeNatural bytes = some (value, rest) ↔
          bytes = Checkpoint.Format.encodeNatural value ++ rest := fun value rest =>
        ⟨Checkpoint.Format.natural_canonical bytes value rest,
          fun same => same ▸ Checkpoint.Format.natural_lawful value rest⟩
      cases lower with
      | nil =>
        change (Checkpoint.Format.decodeNatural bytes).isSome = true ↔ _
        simp only [true_or, and_true]
        constructor
        · intro accepted
          obtain ⟨⟨value, rest⟩, read⟩ := Option.isSome_iff_exists.mp accepted
          exact ⟨value, rest, (exact value rest).mp read⟩
        · rintro ⟨value, rest, same⟩
          rw [(exact value rest).mpr same]
          rfl
      | cons digit digits =>
        rw [Checkpoint.Format.decodeNaturalInto_lower,
          show Checkpoint.Format.decodeNaturalInto bytes [] =
            Checkpoint.Format.decodeNatural bytes from rfl]
        simp only [reduceCtorEq, false_or]
        cases read : Checkpoint.Format.decodeNatural bytes with
        | none =>
          simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff]
          rintro ⟨value, rest, same, -⟩
          rw [(exact value rest).mpr same] at read
          exact absurd read nofun
        | some pair =>
          rcases pair with ⟨high, tail⟩
          simp only [Option.bind_some]
          constructor
          · intro accepted
            by_cases zero : high = 0
            · simp [zero] at accepted
            · exact ⟨high, tail, (exact high tail).mp read, zero⟩
          · rintro ⟨value, rest, same, nonzero⟩
            have both := ((exact value rest).mpr same).symm.trans read
            simp only [Option.some.injEq, Prod.mk.injEq] at both
            rw [← both.1]
            simp [nonzero])
    ⟨([0], []), 0, [], Checkpoint.Format.natural_canonical _ _ _ zero_read, .inl rfl⟩
    ⟨([0], [1]), fun ⟨value, rest, same, nonzero⟩ => by
      have read := Checkpoint.Format.natural_lawful value rest
      rw [← same] at read
      have both := zero_read.symm.trans read
      simp only [Option.some.injEq, Prod.mk.injEq] at both
      rcases nonzero with empty | positive
      · exact absurd empty nofun
      · exact positive both.1.symm⟩⟩

theorem Checkpoint_Format_decodeNaturalInto_registered :
    Regula.RegisteredDecision @Checkpoint.Format.decodeNaturalInto := ⟨⟩

theorem natural_decode_into_value :
    Regula.ExecutableContract Checkpoint.Format.decodeNaturalInto (fun decode =>
      ∀ (bytes : List UInt8) (lower : Nat) (digits : List Nat),
        decode bytes (lower :: digits) =
          (decode bytes []).bind fun (high, tail) =>
            if high = 0 then none
            else some ((lower :: digits).foldl (fun value next => value * 128 + next) high,
              tail)) :=
  ⟨Checkpoint.Format.decodeNaturalInto_lower⟩

theorem food_due : Regula.ExecutableContract Host.foodDue (fun due =>
    Regula.Decides (· = true)
      (fun input : UInt64 × UInt64 => input.2.toNat ∣ input.1.toNat)
      (Function.uncurry due)) :=
  ⟨decides
    (fun input => by
      change Host.foodDue input.1 input.2 = true ↔ _
      rw [Host.foodDue_iff]
      unfold Host.FoodDue
      by_cases zero : input.2 = 0
      · simp only [zero, UInt64.toNat_zero, Nat.zero_dvd, true_and, ne_eq, not_true_eq_false,
          false_and, or_false]
        exact ⟨fun same => by rw [same]; rfl, fun same => UInt64.toNat_inj.mp same⟩
      · simp [zero, Nat.dvd_iff_mod_eq_zero])
    ⟨(0, 0), Nat.dvd_refl 0⟩ ⟨(1, 0), by decide⟩⟩

theorem Host_foodDue_registered : Regula.RegisteredDecision @Host.foodDue := ⟨⟩

theorem coordinate_float : Regula.ExecutableContract Host.coordinateFloat (fun convert =>
    ∀ coordinate : Host.Coordinate, convert coordinate =
      let magnitude := Binary32.ofUInt64 coordinate.val.natAbs.toUInt64
      if coordinate.val < 0 then ⟨magnitude.bits ^^^ 0x80000000⟩ else magnitude) :=
  ⟨Host.coordinateFloat_eq⟩

theorem rotate_left : Regula.ExecutableContract Rng.rotateLeft (fun rotate =>
    (∀ word count : UInt64,
      (rotate word count).toBitVec = word.toBitVec.rotateLeft (count.toNat % 64)) ∧
      rotate 1 1 = 2 ∧ rotate 0x8000000000000000 1 = 1) :=
  ⟨⟨Rng.rotateLeft_toBitVec, by decide, by decide⟩⟩

def splitMix (word : BitVec 64) : BitVec 64 :=
  let mixed := word + 0x9e3779b97f4a7c15#64
  let mixed := (mixed ^^^ mixed >>> 30) * 0xbf58476d1ce4e5b9#64
  let mixed := (mixed ^^^ mixed >>> 27) * 0x94d049bb133111eb#64
  mixed ^^^ mixed >>> 31

private theorem mix_splitMix (word : UInt64) :
    (Rng.mix64 word).toBitVec = splitMix word.toBitVec := by
  simp only [Rng.mix64, Rng.mixFinal, Rng.increment, splitMix, UInt64.toBitVec_xor,
    UInt64.toBitVec_mul, UInt64.toBitVec_add, UInt64.toBitVec_shiftRight,
    BitVec.ushiftRight_eq']
  rfl

theorem unit_feature : Regula.ExecutableContract unitFeature (fun slot =>
    (∀ (dimension : Dimension) (config : Features.Config) (unit : Fin config.units.count),
      (slot dimension config unit).val =
        (splitMix (splitMix (splitMix (config.seed.toBitVec ^^^ 0x1D#64 ^^^
            0x9e3779b97f4a7c15#64) ^^^ 0x1D#64) ^^^
            (BitVec.ofNat 64 unit.val).rotateLeft 17)).toNat % dimension.capacity) ∧
      (slot double pair ⟨0, by decide⟩).val = 1 ∧ (slot double pair ⟨1, by decide⟩).val = 0) :=
  ⟨⟨fun dimension config unit => by
      obtain ⟨exponent, power⟩ := dimension.powerOfTwo
      have small : exponent ≤ 32 := by
        have := dimension.wordBound
        rw [power] at this
        exact Nat.le_of_lt ((Nat.pow_lt_pow_iff_right (by decide)).mp this)
      have hash : (Rng.hash3 (config.seed ^^^ 0x1D) 0x1D unit.val.toUInt64).toBitVec =
          splitMix (splitMix (splitMix (config.seed.toBitVec ^^^ 0x1D#64 ^^^
            0x9e3779b97f4a7c15#64) ^^^ 0x1D#64) ^^^ (BitVec.ofNat 64 unit.val).rotateLeft 17) := by
        simp only [Rng.hash3, mix_splitMix, UInt64.toBitVec_xor, Rng.rotateLeft_toBitVec]
        rfl
      rw [← hash]
      show ((Rng.hash3 (config.seed ^^^ 0x1D) 0x1D unit.val.toUInt64).toUInt32 &&&
        (dimension.capacity - 1).toUInt32).toNat = _
      have below : dimension.capacity - 1 < 2 ^ 32 := by have := dimension.wordBound; omega
      rw [UInt32.toNat_and, UInt64.toNat_toUInt32, Nat.toUInt32_eq, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt below, UInt64.toNat_toBitVec, power,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 small)],
    by decide, by decide⟩⟩

theorem reach_distance : Regula.ExecutableContract Host.ReachRelation.distance (fun distance =>
    (∀ (relation : Host.ReachRelation) (steps : Nat), distance relation ≤ steps ↔
      relation.dx.val.natAbs ≤ FeatureConstants.reachRadius + steps ∧
        relation.dy.val.natAbs ≤ FeatureConstants.reachRadius + steps) ∧
      distance ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ = 0 ∧
      distance ⟨⟨5, by decide⟩, ⟨-2, by decide⟩⟩ = 2) :=
  ⟨⟨fun relation steps => by
      unfold Host.ReachRelation.distance
      constructor
      · intro within
        constructor <;> omega
      · intro ⟨across, down⟩
        omega,
    rfl, rfl⟩⟩

theorem numeral_chars : Regula.ExecutableContract Json.Numeral.chars (fun spell =>
    (∀ numeral : Json.Numeral, spell numeral =
      (if numeral.negative then ['-'] else []) ++ numeral.whole ++
        (numeral.fraction.map ('.' :: ·)).getD [] ++
        (numeral.exponent.map fun exponent => (if exponent.upper then 'E' else 'e') ::
          ((exponent.sign.map fun negative => if negative then '-' else '+').toList ++
            exponent.digits)).getD []) ∧
      (∀ numeral : Json.Numeral, numeral.Formed →
        Json.Numeral.scan (spell numeral) = some (numeral, [])) ∧
      spell ⟨true, ['1'], some ['5'], some ⟨true, some false, ['2']⟩⟩ =
        ['-', '1', '.', '5', 'E', '+', '2']) :=
  ⟨⟨fun numeral => by
      rcases numeral with ⟨negative, whole, _ | fraction, _ | ⟨upper, _ | _ | _, digits⟩⟩ <;> rfl,
    Json.Numeral.scan_chars, rfl⟩⟩

private theorem fnv_fold (bytes : List UInt8) (state : UInt64) :
    (bytes.foldl Rng.fnvStep state).toNat =
      bytes.foldl (fun state byte => (state ^^^ byte.toNat) * 1099511628211 % 2 ^ 64)
        state.toNat := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte rest hold =>
    have step : (Rng.fnvStep state byte).toNat =
        (state.toNat ^^^ byte.toNat) * 1099511628211 % 2 ^ 64 := by
      rw [Rng.fnvStep, UInt64.toNat_mul, UInt64.toNat_xor, UInt8.toNat_toUInt64]
      rfl
    rw [List.foldl_cons, List.foldl_cons, hold, step]

theorem fnv_hash : Regula.ExecutableContract Rng.fnv (fun hash =>
    (∀ bytes : List UInt8, (hash bytes).toNat =
      bytes.foldl (fun state byte => (state ^^^ byte.toNat) * 1099511628211 % 2 ^ 64)
        14695981039346656037) ∧
      hash [] = 0xcbf29ce484222325 ∧ hash [0x61] = 0xaf63dc4c8601ec8c) :=
  ⟨⟨fun bytes => fnv_fold bytes Rng.fnvOffset, rfl, by decide⟩⟩

def littleEndian (width value : Nat) : List UInt8 :=
  (List.range width).map fun place => UInt8.ofNat (value / 256 ^ place)

private theorem encodeNat_littleEndian (width value : Nat) :
    Checkpoint.encodeNat width value = littleEndian width value := by
  induction width generalizing value with
  | zero => rfl
  | succ width hold =>
    rw [Checkpoint.encodeNat, hold, littleEndian, littleEndian, List.range_succ_eq_map,
      List.map_cons, List.map_map, Nat.pow_zero, Nat.div_one]
    congr 1
    apply List.map_congr_left
    intro place _
    simp only [Function.comp_apply, Nat.pow_succ', Nat.div_div_eq_div_mul]

theorem u64_codec : Regula.ExecutableContract Checkpoint.u64Codec (fun codec =>
    (∀ word : UInt64, codec.encode word = littleEndian 8 word.toNat) ∧ codec.Canonical ∧
      codec.encode 0x0102 = [2, 1, 0, 0, 0, 0, 0, 0]) :=
  ⟨⟨fun word => encodeNat_littleEndian 8 word.toNat, Checkpoint.u64Codec_canonical, rfl⟩⟩

theorem header_codec : Regula.ExecutableContract Checkpoint.headerCodec (fun codec =>
    (∀ header : Checkpoint.Header, codec.encode header =
      littleEndian 4 header.version.toNat ++ littleEndian 4 header.capacity.toNat ++
        littleEndian 4 header.learners.toNat ++ littleEndian 8 header.seed.toNat ++
        littleEndian 8 header.clock.toNat ++ littleEndian 4 header.criterion.toNat ++
        littleEndian 4 header.gain.bits.toNat ++ littleEndian 8 header.tilings.toNat ++
        littleEndian 4 header.units.toNat ++ littleEndian 4 header.supported.toNat ++
        littleEndian 4 header.order.toNat) ∧ codec.Canonical) :=
  ⟨⟨fun header => by
      simp only [Checkpoint.headerCodec, Checkpoint.Codec.iso, Checkpoint.Codec.pair,
        Checkpoint.u32Codec, Checkpoint.u64Codec, Checkpoint.binary32Codec, Checkpoint.wordCodec,
        encodeNat_littleEndian, List.append_assoc],
    Checkpoint.headerCodec_canonical⟩⟩

def twentyStepDay : Host.WorldConfig :=
  ⟨⟨0, ⟨64, by decide⟩, 20, 0, 0, 0, 0, ⟨0x3f800000⟩⟩, by decide, by decide⟩

theorem day_phase : Regula.ExecutableContract @Host.World.dayPhase (fun phase =>
    (∀ {config : Host.WorldConfig} (world : Host.World config) (bucket : Nat), bucket < 8 →
      (bucket ≤ (phase world).val ↔
        if world.time.toNat % config.raw.dayLength.toNat < config.raw.dayLength.toNat / 2 then
          bucket < 4 ∧ bucket * max 1 (config.raw.dayLength.toNat / 8) ≤
            world.time.toNat % config.raw.dayLength.toNat
        else bucket ≤ 4 ∨ (bucket - 4) * max 1 (config.raw.dayLength.toNat / 8) ≤
          world.time.toNat % config.raw.dayLength.toNat - config.raw.dayLength.toNat / 2)) ∧
      (phase { Host.World.empty twentyStepDay with time := 9 }).val = 3 ∧
      (phase { Host.World.empty twentyStepDay with time := 10 }).val = 4) :=
  ⟨⟨fun {config} world bucket below => by
      have positive : 0 < max 1 (config.raw.dayLength.toNat / 8) :=
        Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)
      have scaled := fun count slot =>
        Nat.le_div_iff_mul_le (k := max 1 (config.raw.dayLength.toNat / 8)) (x := count)
          (y := slot) positive
      unfold Host.World.dayPhase
      simp only [FeatureConstants.dayPhases]
      split
      · rw [← scaled]
        dsimp only
        generalize world.time.toNat % config.raw.dayLength.toNat /
          max 1 (config.raw.dayLength.toNat / 8) = quotient
        constructor
        · intro within
          exact ⟨by omega, by omega⟩
        · intro ⟨_, within⟩
          omega
      · rw [← scaled]
        dsimp only
        generalize (world.time.toNat % config.raw.dayLength.toNat -
          config.raw.dayLength.toNat / 2) / max 1 (config.raw.dayLength.toNat / 8) = quotient
        omega,
    by decide, by decide⟩⟩

theorem snapshot_masses : Regula.ExecutableContract @PolicySnapshot.probabilities (fun masses =>
    (∀ {count : Word.Count} (snapshot : PolicySnapshot count) (action : Fin count.word.toNat),
      let top := (snapshot.values.toList.drop 1).foldl
        (fun best value => if Binary32.Less best value then value else best)
        (snapshot.values.get ⟨0, count.positive⟩)
      let threshold := top.sub ⟨0x358637bd⟩
      let tied := ((List.finRange count.word.toNat).filter fun other =>
        decide (Binary32.LessOrEqual threshold (snapshot.values.get other))).length
      (masses snapshot).get action =
        (snapshot.epsilon.value.div (Binary32.ofUInt64 count.word)).add
          (if Binary32.LessOrEqual threshold (snapshot.values.get action) then
            ((⟨0x3f800000⟩ : Binary32).sub snapshot.epsilon.value).div
              (Binary32.ofUInt64 tied.toUInt64)
          else ⟨0⟩)) ∧
      (masses (count := ⟨2, by decide⟩)
        ⟨#v[⟨0x3f800000⟩, ⟨0⟩], SwiftTd.ExploreRate.never⟩).toList = [⟨0x3f800000⟩, ⟨0⟩]) :=
  ⟨⟨fun snapshot action => by
      simp only [PolicySnapshot.probabilities_def, PolicySnapshot.candidates_def,
        PolicySnapshot.best_def]
      show (Vector.map _ _).get action = _
      simp only [Vector.get, Vector.toArray_map, Array.getElem_map]
      rfl,
    by decide +kernel⟩⟩

theorem craft_recipe : Regula.ExecutableContract Host.Craftable.recipe (fun recipe =>
    recipe .axe = (3, 2) ∧ recipe .boat = (4, 0)) :=
  ⟨⟨rfl, rfl⟩⟩

theorem goal_kind_code : Regula.ExecutableContract Host.Viewer.GoalKind.code (fun code =>
    (code none = 0 ∧ code (some .reach) = 1 ∧ code (some .collect) = 2 ∧
      code (some .craft) = 3 ∧ code (some .survive) = 4) ∧
      (∀ number : Nat, (∃ kind, code kind = number) ↔ number < 5) ∧
      ∀ first second, code first = code second → first = second) :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun number => by
      constructor
      · rintro ⟨kind, rfl⟩
        rcases kind with _ | kind
        · decide
        · cases kind <;> decide
      · intro below
        match number, below with
        | 0, _ => exact ⟨none, rfl⟩
        | 1, _ => exact ⟨some .reach, rfl⟩
        | 2, _ => exact ⟨some .collect, rfl⟩
        | 3, _ => exact ⟨some .craft, rfl⟩
        | 4, _ => exact ⟨some .survive, rfl⟩,
    fun first second same => by
      rcases first with _ | first <;> rcases second with _ | second <;>
        (try cases first) <;> (try cases second) <;> first | rfl | exact absurd same (by decide)⟩⟩

theorem goal_item_code : Regula.ExecutableContract Host.Viewer.GoalItem.code (fun code =>
    (code none = 0 ∧ code (some (.inl .wood)) = 1 ∧ code (some (.inl .stone)) = 2 ∧
      code (some (.inl .food)) = 3 ∧ code (some (.inl .gold)) = 4 ∧
      code (some (.inr .axe)) = 11 ∧ code (some (.inr .boat)) = 12) ∧
      (∀ number : Nat, (∃ item, code item = number) ↔ number ∈ [0, 1, 2, 3, 4, 11, 12]) ∧
      ∀ first second, code first = code second → first = second) :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun number => by
      constructor
      · rintro ⟨item, rfl⟩
        rcases item with _ | item | tool
        · decide
        · cases item <;> decide
        · cases tool <;> decide
      · intro listed
        simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
        rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨none, rfl⟩
        · exact ⟨some (.inl .wood), rfl⟩
        · exact ⟨some (.inl .stone), rfl⟩
        · exact ⟨some (.inl .food), rfl⟩
        · exact ⟨some (.inl .gold), rfl⟩
        · exact ⟨some (.inr .axe), rfl⟩
        · exact ⟨some (.inr .boat), rfl⟩,
    fun first second same => by
      rcases first with _ | first | first <;> rcases second with _ | second | second <;>
        (try cases first) <;> (try cases second) <;> first | rfl | exact absurd same (by decide)⟩⟩

theorem interface_layout : Regula.ExecutableContract Interface.layout (fun layout =>
    ∀ interface : Interface, (layout interface).length = interface.signals.length + 1 ∧
      (layout interface)[0]? = some .g99 ∧
        ∀ position : Nat, (layout interface)[position + 1]? = interface.signals[position]?) :=
  ⟨fun interface => ⟨by simp [Interface.layout], by simp [Interface.layout],
    fun position => by simp [Interface.layout]⟩⟩

private theorem rankWidth_fits (dimension : Dimension) :
    ∃ exponent, rankWidth dimension = 2 ^ exponent ∧
      (exponent = 0 ∨ 3 * (2 ^ exponent) ^ 2 ≤ dimension.capacity) ∧
        dimension.capacity < 3 * (2 ^ (exponent + 1)) ^ 2 := by
  have count : FeatureConstants.skillCount = 3 := rfl
  refine ⟨rankExponent dimension, rankWidth_eq dimension, ?_, ?_⟩
  · by_cases room : FeatureConstants.skillCount ≤ dimension.capacity
    · have budget := rankWidth_budget dimension room
      rw [rankWidth_eq, count, ← Nat.pow_two] at budget
      exact .inr budget
    · refine .inl ?_
      have first : ¬FeatureConstants.skillCount * ((1 <<< (0 + 1)) * (1 <<< (0 + 1))) ≤
          dimension.capacity := fun fits => room (by rw [count] at fits ⊢; omega)
      show rankExponentFrom dimension.capacity (14 + 1) 0 = 0
      rw [rankExponentFrom]
      simp only [first, ↓reduceIte]
  · have maximal := rankWidth_maximal dimension
    rwa [count, ← Nat.pow_two] at maximal

theorem rank_width : Regula.ExecutableContract rankWidth (fun width =>
    ∀ dimension : Dimension, ∃ exponent, width dimension = 2 ^ exponent ∧
      (exponent = 0 ∨ 3 * (2 ^ exponent) ^ 2 ≤ dimension.capacity) ∧
        dimension.capacity < 3 * (2 ^ (exponent + 1)) ^ 2) :=
  ⟨rankWidth_fits⟩

theorem rank_dimension : Regula.ExecutableContract rankDimension (fun ranked =>
    ∀ dimension : Dimension, ∃ exponent, (ranked dimension).capacity = 2 ^ exponent ∧
      (exponent = 0 ∨ 3 * (2 ^ exponent) ^ 2 ≤ dimension.capacity) ∧
        dimension.capacity < 3 * (2 ^ (exponent + 1)) ^ 2) :=
  ⟨rankWidth_fits⟩

theorem world_side : Regula.ExecutableContract Host.WorldConfig.side (fun side =>
    ∀ config : Host.WorldConfig, ((side config : Nat) : Int) = config.raw.side.val ∧
      0 < side config) :=
  ⟨fun config => by
    have positive := config.positiveSide
    unfold Host.WorldConfig.side
    omega⟩

theorem box_position : Regula.ExecutableContract @Host.BoxPosition.position (fun position =>
    ∀ (config : Host.WorldConfig) (body : Host.BoxPosition config),
      (position body).x.val = body.x.val ∧ (position body).y.val = body.y.val) :=
  ⟨fun _ _ => ⟨rfl, rfl⟩⟩

theorem box_center : Regula.ExecutableContract Host.BoxPosition.center (fun center =>
    ∀ config : Host.WorldConfig, (center config).x.val = config.side / 2 ∧
      (center config).y.val = config.side / 2) :=
  ⟨fun _ => ⟨rfl, rfl⟩⟩

structure OccupancyFree where
  activation : Type
  exploration : Type
  occupancy : Occupancy activation exploration

theorem occupancy_free : Regula.ExecutableContract @Occupancy.free (fun free =>
    Regula.Decides (· = true) (fun input : OccupancyFree => input.occupancy = .idle)
      (fun input : OccupancyFree => @free input.activation input.exploration input.occupancy)) :=
  ⟨decides
    (fun input => by
      rcases input with ⟨activation, exploration, occupancy⟩
      cases occupancy <;> simp [Occupancy.free])
    ⟨⟨Unit, Unit, .idle⟩, rfl⟩ ⟨⟨Unit, Unit, .exploring ()⟩, nofun⟩⟩

theorem Occupancy_free_registered : Regula.RegisteredDecision @Occupancy.free := ⟨⟩

theorem ranks_subtasks : Regula.ExecutableContract FeatureProfile.ranksSubtasks (fun ranks =>
    Regula.Decides (· = true) (fun profile : FeatureProfile => profile.subtasks = .learned)
      ranks) :=
  ⟨decides
    (fun profile => by
      rcases profile with ⟨mode, credit, rate, subtasks⟩
      cases subtasks <;> simp [FeatureProfile.ranksSubtasks])
    ⟨⟨.final, .perStep, .declared, .learned⟩, rfl⟩
    ⟨⟨.final, .perStep, .declared, .spatial⟩, nofun⟩⟩

theorem FeatureProfile_ranksSubtasks_registered :
    Regula.RegisteredDecision @FeatureProfile.ranksSubtasks := ⟨⟩

theorem uses_hierarchy : Regula.ExecutableContract FeatureProfile.usesHierarchy (fun uses =>
    Regula.Decides (· = true) (fun profile : FeatureProfile => profile.mode ≠ .primitiveOnly)
      uses) :=
  ⟨decides
    (fun profile => by
      rcases profile with ⟨mode, credit, rate, subtasks⟩
      cases mode <;> simp [FeatureProfile.usesHierarchy])
    ⟨⟨.final, .perStep, .declared, .learned⟩, nofun⟩
    ⟨⟨.primitiveOnly, .perStep, .declared, .learned⟩, fun other => other rfl⟩⟩

theorem FeatureProfile_usesHierarchy_registered :
    Regula.RegisteredDecision @FeatureProfile.usesHierarchy := ⟨⟩

private theorem reserved_iff (interface : Interface) (channel : UInt64) :
    interface.reserved channel = true ↔ ∃ position : Nat,
      position < interface.layout.length ∧ channel = interface.feedback + position.toUInt64 := by
  unfold Interface.reserved
  rw [decide_eq_true_iff]
  constructor
  · intro inside
    refine ⟨(channel - interface.feedback).toNat, inside, ?_⟩
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_sub, Nat.toUInt64, UInt64.toNat_ofNat']
    have := channel.toNat_lt
    have := interface.feedback.toNat_lt
    omega
  · rintro ⟨position, inside, rfl⟩
    have word : (interface.feedback + position.toUInt64 - interface.feedback).toNat =
        position % 2 ^ 64 := by
      simp only [UInt64.toNat_add, UInt64.toNat_sub, Nat.toUInt64, UInt64.toNat_ofNat']
      have := interface.feedback.toNat_lt
      omega
    rw [word]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) inside

theorem interface_reserved : Regula.ExecutableContract Interface.reserved (fun reserved =>
    Regula.Decides (· = true)
      (fun input : Interface × UInt64 => ∃ position : Nat,
        position < input.1.layout.length ∧ input.2 = input.1.feedback + position.toUInt64)
      (Function.uncurry reserved)) :=
  ⟨.of_iff (fun input => reserved_iff input.1 input.2)
    ⟨(Grid.interface, Grid.interface.feedback), by decide⟩
    ⟨(Grid.interface, Grid.interface.feedback - 1), by decide⟩⟩

theorem Interface_reserved_registered : Regula.RegisteredDecision @Interface.reserved := ⟨⟩

structure ActivationLearning where
  mode : Bool
  activation : OptionActivation mode

theorem activation_learning : Regula.ExecutableContract @OptionActivation.learning
    (fun learning =>
      Regula.Decides (· = true) (fun input : ActivationLearning => input.mode = true)
        (fun input : ActivationLearning => @learning input.mode input.activation)) :=
  ⟨decides (fun _ => Iff.rfl) ⟨⟨true, .first true false⟩, rfl⟩
    ⟨⟨false, .first false false⟩, nofun⟩⟩

theorem OptionActivation_learning_registered :
    Regula.RegisteredDecision @OptionActivation.learning := ⟨⟩

def sourced (source : TemporalSource) : TemporalDecision metaCount :=
  ⟨source, firstAction metaCount, .replicate _ .zero, .replicate _ .zero, false,
    .replicate _ .zero, none, none, none⟩

structure DecisionOwn where
  actions : Word.Count
  decision : TemporalDecision actions

theorem decision_own : Regula.ExecutableContract @TemporalDecision.own (fun own =>
    Regula.Decides (· = true)
      (fun input : DecisionOwn => ∀ slot, input.decision.source ≠ .option slot)
      (fun input : DecisionOwn => @own input.actions input.decision)) :=
  ⟨decides
    (fun input => by
      rcases input with ⟨actions, decision⟩
      cases source : decision.source <;> simp [TemporalDecision.own, source])
    ⟨⟨metaCount, sourced .primitive⟩, fun _ => nofun⟩
    ⟨⟨metaCount, sourced (.option ⟨0, by decide⟩)⟩, fun other => other ⟨0, by decide⟩ rfl⟩⟩

theorem TemporalDecision_own_registered : Regula.RegisteredDecision @TemporalDecision.own := ⟨⟩

theorem skill_of_meta : Regula.ExecutableContract skillOfMeta (fun skill =>
    Regula.Decides (·.isSome = true)
      (fun action : Action metaCount.word.toNat => action.val ≠ 0) skill) :=
  ⟨.of_iff
    (fun action => by
      unfold skillOfMeta
      by_cases zero : action.val = 0 <;> simp [zero])
    ⟨⟨1, by decide⟩, by decide⟩ ⟨⟨0, by decide⟩, by decide⟩⟩

theorem skillOfMeta_registered : Regula.RegisteredDecision @skillOfMeta := ⟨⟩

theorem skill_of_meta_value : Regula.ExecutableContract skillOfMeta (fun skill =>
    ∀ (action : Action metaCount.word.toNat) (named : Fin Acorn.FeatureConstants.skillCount),
      skill action = some named ↔ action.val = named.val + 1) :=
  ⟨fun action named => by
    unfold skillOfMeta
    by_cases zero : action.val = 0
    · simp [zero]
    · simp only [zero, ↓reduceDIte, Option.some.injEq, Fin.ext_iff]
      constructor <;> intro same <;> omega⟩

structure RunServe where
  count : Word.Count
  run : ExploratoryRun count

theorem run_serve : Regula.ExecutableContract @ExploratoryRun.serve (fun serve =>
    Regula.Decides (· = true) (fun input : RunServe => 0 < input.run.remaining.val)
      (Regula.Dependent.isSome fun input : RunServe => @serve input.count input.run)) :=
  ⟨present (fun _ => dite_isSome _)
    ⟨⟨metaCount, ⟨firstAction metaCount, ⟨1, by decide⟩⟩⟩, by decide⟩
    ⟨⟨metaCount, ⟨firstAction metaCount, ⟨0, by decide⟩⟩⟩, by decide⟩⟩

theorem ExploratoryRun_serve_registered : Regula.RegisteredDecision @ExploratoryRun.serve := ⟨⟩

theorem run_serve_value : Regula.ExecutableContract @ExploratoryRun.serve (fun serve =>
    ∀ {count : Word.Count} (run next : ExploratoryRun count) (action : Action count.word.toNat),
      serve run = some (action, next) ↔ 0 < run.remaining.val ∧ action = run.action ∧
        next.action = run.action ∧ next.remaining.val + 1 = run.remaining.val) :=
  ⟨fun run next action => by
    constructor
    · intro served
      refine ⟨Nat.pos_of_ne_zero fun spent => ?_, ExploratoryRun.serve_exact run next action served⟩
      rw [(ExploratoryRun.spent run).mpr spent] at served
      contradiction
    · rintro ⟨remaining, rfl, same, fewer⟩
      obtain ⟨nextAction, nextRemaining⟩ := next
      dsimp only at same fewer
      subst same
      simp only [ExploratoryRun.serve, remaining, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq,
        ExploratoryRun.mk.injEq, true_and]
      apply Fin.ext
      dsimp only
      omega⟩

structure OccupancyExecuting where
  actions : Word.Count
  mode : Bool
  occupancy : Occupancy (OptionActivation mode) (CommittedRun actions mode)

theorem occupancy_executing : Regula.ExecutableContract @Occupancy.executing (fun executing =>
    Regula.Decides (·.isSome = true)
      (fun input : OccupancyExecuting =>
        (∃ slot activation, input.occupancy = .option slot activation) ∨
          ∃ run : CommittedRun input.actions input.mode,
            input.occupancy = .exploring run ∧ run.origin ≠ none)
      (fun input : OccupancyExecuting =>
        @executing input.actions input.mode input.occupancy)) :=
  ⟨decides
    (fun input => by
      rcases input with ⟨actions, mode, occupancy⟩
      rcases occupancy with _ | run | ⟨slot, activation⟩
      · simp [Occupancy.executing]
      · cases origin : run.origin <;> simp [Occupancy.executing, origin]
      · simp [Occupancy.executing])
    ⟨⟨metaCount, true, .option ⟨0, by decide⟩ (.first true false)⟩,
      .inl ⟨⟨0, by decide⟩, .first true false, rfl⟩⟩
    ⟨⟨metaCount, true, .idle⟩, fun specified => by
      rcases specified with ⟨_, _, same⟩ | ⟨_, same, _⟩ <;> exact nomatch same⟩⟩

theorem Occupancy_executing_registered : Regula.RegisteredDecision @Occupancy.executing := ⟨⟩

theorem occupancy_executing_value : Regula.ExecutableContract @Occupancy.executing
    (fun executing =>
      ∀ {actions : Word.Count} {mode : Bool}
        (occupancy : Occupancy (OptionActivation mode) (CommittedRun actions mode))
        (slot : Fin Acorn.FeatureConstants.skillCount),
        executing occupancy = some slot ↔ (∃ activation, occupancy = .option slot activation) ∨
          ∃ run activation, occupancy = .exploring run ∧ run.origin = some (slot, activation)) :=
  ⟨fun occupancy slot => by
    rcases occupancy with _ | run | ⟨held, activation⟩
    · simp [Occupancy.executing]
    · cases origin : run.origin with
      | none => simp [Occupancy.executing, origin]
      | some found =>
        obtain ⟨origin', activation⟩ := found
        simp [Occupancy.executing, origin]
    · simp [Occupancy.executing]⟩

def spot : Candidate bank := ⟨⟨0, by decide⟩, spark⟩

structure BestOf where
  config : Features.Config
  items : List (Candidate config)

theorem best_of : Regula.ExecutableContract @best (fun scan =>
    Regula.Decides (· = true) (fun input : BestOf => input.items ≠ [])
      (Regula.Dependent.isSome fun input : BestOf => @scan input.config input.items)) :=
  ⟨present
    (fun input => by
      rcases input with ⟨config, items⟩
      cases items <;> simp [best])
    ⟨⟨bank, [spot]⟩, by decide⟩ ⟨⟨bank, []⟩, by decide⟩⟩

theorem best_registered : Regula.RegisteredDecision @best := ⟨⟩

theorem best_of_value : Regula.ExecutableContract @best (fun scan =>
    ∀ {config : Features.Config} (items : List (Candidate config)) (winner : Candidate config),
      scan items = some winner → winner ∈ items ∧ ∀ candidate ∈ items, winner.Dominates candidate) :=
  ⟨best_spec⟩

structure AssignmentRetain where
  config : Features.Config
  chosen : List (Candidate config)
  assignment : Assignment config

theorem assignment_retain : Regula.ExecutableContract @Assignment.retain (fun retain =>
    Regula.Decides (· = true)
      (fun input : AssignmentRetain => ∃ unit bonus, input.assignment = .selected unit bonus ∧
        ∃ candidate ∈ input.chosen, candidate.unit = unit)
      (Regula.Dependent.isSome fun input : AssignmentRetain =>
        @retain input.config input.chosen input.assignment)) :=
  ⟨.of_iff
    (fun input => by
      rcases input with ⟨config, chosen, assignment⟩
      cases assignment <;> simp [Regula.Dependent.isSome, Assignment.retain, List.find?_isSome])
    ⟨⟨bank, [spot], chosen⟩, by decide⟩ ⟨⟨bank, [], chosen⟩, by decide⟩⟩

theorem Assignment_retain_registered : Regula.RegisteredDecision @Assignment.retain := ⟨⟩

theorem assignment_retain_value : Regula.ExecutableContract @Assignment.retain (fun retain =>
    ∀ {config : Features.Config} (before after : List (Candidate config))
      (candidate : Candidate config) (unit : Fin config.units.count) (bonus : Bonus),
      candidate.unit = unit → (∀ earlier ∈ before, earlier.unit ≠ unit) →
        ∃ raised, retain (before ++ candidate :: after) (.selected unit bonus) =
            some (.selected unit raised) ∧ (raised = bonus ∨ raised = candidate.score) ∧
          bonus.value.bits.toNat ≤ raised.value.bits.toNat ∧
          candidate.score.value.bits.toNat ≤ raised.value.bits.toNat) :=
  ⟨fun before after candidate unit bonus named earlier => by
    have first : (before ++ candidate :: after).find? (·.unit == unit) = some candidate :=
      List.find?_eq_some_iff_append.mpr ⟨by simp [named],
        before, after, rfl, fun other inside => by simp [earlier other inside]⟩
    refine ⟨bonus.max candidate.score, by simp [Assignment.retain, first], ?_,
      Bonus.le_max bonus candidate.score⟩
    unfold Bonus.max
    split
    · exact .inr rfl
    · exact .inl rfl⟩

structure KeptSlot where
  config : Features.Config
  held : Vector (Assignment config) Acorn.FeatureConstants.skillCount
  chosen : List (Candidate config)
  slot : Fin Acorn.FeatureConstants.skillCount

private theorem kept_iff {config : Features.Config}
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (chosen : List (Candidate config)) (slot : Fin Acorn.FeatureConstants.skillCount) :
    (kept held chosen slot).isSome = true ↔ ∃ unit bonus, held[slot.val] = .selected unit bonus ∧
      (∃ candidate ∈ chosen, candidate.unit = unit) ∧
      ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
        ∀ earlier, held[other.val] ≠ .selected unit earlier := by
  unfold kept
  split
  · rename_i taken
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro unit bonus selected _ free
    obtain ⟨other, -, sameEarlier⟩ := List.any_eq_true.mp taken
    simp only [Bool.and_eq_true, decide_eq_true_eq] at sameEarlier
    obtain ⟨earlierSlot, same⟩ := sameEarlier
    rw [selected] at same
    cases earlier : held[other.val] with
    | neutral => simp [earlier, Assignment.same] at same
    | selected otherUnit otherBonus =>
      simp only [earlier, Assignment.same, beq_iff_eq] at same
      exact free other earlierSlot otherBonus (by rw [earlier, same])
  · rename_i untaken
    cases selected : held[slot.val] with
    | neutral => simp [Assignment.retain]
    | selected unit bonus =>
      simp only [Assignment.retain, Option.isSome_map, List.find?_isSome, beq_iff_eq,
        Assignment.selected.injEq]
      constructor
      · intro named
        refine ⟨unit, bonus, ⟨rfl, rfl⟩, named, fun other earlierSlot earlier same => ?_⟩
        apply untaken
        apply List.any_eq_true.mpr
        refine ⟨other, List.mem_finRange _, ?_⟩
        simp [earlierSlot, same, selected, Assignment.same]
      · rintro ⟨_, _, ⟨rfl, rfl⟩, named, _⟩
        exact named

theorem kept_slot : Regula.ExecutableContract @kept (fun keep =>
    Regula.Decides (· = true)
      (fun input : KeptSlot => ∃ unit bonus, input.held[input.slot.val] = .selected unit bonus ∧
        (∃ candidate ∈ input.chosen, candidate.unit = unit) ∧
        ∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < input.slot.val →
          ∀ earlier, input.held[other.val] ≠ .selected unit earlier)
      (Regula.Dependent.isSome fun input : KeptSlot =>
        @keep input.config input.held input.chosen input.slot)) :=
  ⟨.of_iff (fun input => kept_iff input.held input.chosen input.slot)
    ⟨⟨bank, #v[chosen, .neutral, .neutral], [spot], ⟨0, by decide⟩⟩, by decide⟩
    ⟨⟨bank, #v[chosen, .neutral, .neutral], [spot], ⟨1, by decide⟩⟩, by decide⟩⟩

theorem kept_registered : Regula.RegisteredDecision @kept := ⟨⟩

theorem kept_slot_value : Regula.ExecutableContract @kept (fun keep =>
    ∀ {config : Features.Config}
      (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
      (chosen : List (Candidate config)) (slot : Fin Acorn.FeatureConstants.skillCount),
      ((∃ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val ∧
          ∃ unit bonus earlier, held[slot.val] = .selected unit bonus ∧
            held[other.val] = .selected unit earlier) →
        keep held chosen slot = none) ∧
      ((∀ other : Fin Acorn.FeatureConstants.skillCount, other.val < slot.val →
          ∀ unit bonus earlier, held[slot.val] = .selected unit bonus →
            held[other.val] ≠ .selected unit earlier) →
        keep held chosen slot = held[slot.val].retain chosen)) :=
  ⟨fun held chosen slot => by
    constructor
    · rintro ⟨other, earlierSlot, unit, bonus, earlier, selected, before⟩
      unfold kept
      have taken : ((List.finRange Acorn.FeatureConstants.skillCount).any fun other =>
          decide (other.val < slot.val) && held[other.val].same held[slot.val]) = true :=
        List.any_eq_true.mpr ⟨other, List.mem_finRange _, by
          simp [earlierSlot, selected, before, Assignment.same]⟩
      simp only [taken, ↓reduceIte]
    · intro fresh
      unfold kept
      split
      · rename_i taken
        obtain ⟨other, -, sameEarlier⟩ := List.any_eq_true.mp taken
        simp only [Bool.and_eq_true, decide_eq_true_eq] at sameEarlier
        obtain ⟨earlierSlot, same⟩ := sameEarlier
        cases selected : held[slot.val] with
        | neutral => simp [Assignment.retain]
        | selected unit bonus =>
          rw [selected] at same
          cases before : held[other.val] with
          | neutral => simp [before, Assignment.same] at same
          | selected otherUnit otherBonus =>
            simp only [before, Assignment.same, beq_iff_eq] at same
            exact absurd (by rw [before, same]) (fresh other earlierSlot unit bonus otherBonus selected)
      · rfl⟩

def sixteen : Dimension := ⟨16, by decide, ⟨4, rfl⟩, by decide⟩

def single : RankedFeatures sixteen :=
  .ofSlots (Vector.ofFn fun position => if position.val = 0 then some ⟨0, by decide⟩ else none)
    (by decide)
    (index_distinct _ fun first second _ left right => by
      apply Fin.ext
      simp only [Vector.getElem_ofFn] at left right
      by_cases zero : first.val = 0 <;> by_cases other : second.val = 0 <;> simp_all)

structure RankedPosition where
  dimension : Dimension
  ranked : RankedFeatures dimension
  feature : FeatIdx dimension

theorem ranked_position : Regula.ExecutableContract @RankedFeatures.position (fun position =>
    Regula.Decides (· = true)
      (fun input : RankedPosition => ∃ held : RankIdx input.dimension,
        input.ranked.slots[held.val] = some input.feature)
      (Regula.Dependent.isSome fun input : RankedPosition =>
        @position input.dimension input.ranked input.feature)) :=
  ⟨present
    (fun input => ⟨fun accepted => by
        obtain ⟨found, located⟩ := Option.isSome_iff_exists.mp accepted
        exact ⟨found, RankedFeatures.position_slot _ _ _ located⟩,
      fun ⟨held, holds⟩ => by
        obtain ⟨found, located⟩ := RankedFeatures.position_complete _ held _ holds
        rw [located]
        rfl⟩)
    ⟨⟨sixteen, single, ⟨0, by decide⟩⟩, ⟨0, by decide⟩, by decide⟩
    ⟨⟨sixteen, .empty sixteen, ⟨0, by decide⟩⟩, fun ⟨_, holds⟩ => by
      simp [RankedFeatures.empty, RankedFeatures.ofSlots] at holds⟩⟩

theorem RankedFeatures_position_registered :
    Regula.RegisteredDecision @RankedFeatures.position := ⟨⟩

theorem ranked_position_value : Regula.ExecutableContract @RankedFeatures.position
    (fun position =>
      ∀ {dimension : Dimension} (ranked : RankedFeatures dimension) (feature : FeatIdx dimension)
        (found : RankIdx dimension),
        position ranked feature = some found ↔ ranked.slots[found.val] = some feature) :=
  ⟨fun ranked feature found => by
    constructor
    · exact RankedFeatures.position_slot ranked feature found
    · intro holds
      obtain ⟨located, returned⟩ := RankedFeatures.position_complete ranked found feature holds
      rw [returned, RankedFeatures.slot_unique ranked located found feature
        (RankedFeatures.position_slot ranked feature located returned) holds]⟩

structure ActiveSlot where
  interface : Interface
  profile : FeatureProfile
  config : Features.Config
  criterion : Criterion
  dimension : Dimension
  state : TemporalControl interface profile config criterion dimension

def phased (phase : Occupancy (OptionActivation true) (CommittedRun Grid.interface.actions true)) :
    TemporalControl Grid.interface ⟨.final, .perStep, .declared, .learned⟩ bank .discounted
      narrow :=
  let initial := TemporalControl.initial Grid.interface ⟨.final, .perStep, .declared, .learned⟩ bank
    .discounted narrow
  { initial with runtime := { initial.runtime with
      references := { initial.runtime.references with phase := phase } } }

theorem active_slot : Regula.ExecutableContract @TemporalControl.activeSlot (fun active =>
    Regula.Decides (·.isSome = true)
      (fun input : ActiveSlot =>
        (∃ slot activation, input.state.runtime.references.phase = .option slot activation) ∨
          ∃ run, input.state.runtime.references.phase = .exploring run ∧ run.origin ≠ none)
      (fun input : ActiveSlot => @active input.interface input.profile input.config
        input.criterion input.dimension input.state)) :=
  ⟨decides
    (fun input => by
      rcases input with ⟨interface, profile, config, criterion, dimension, state⟩
      show (state.runtime.references.phase.executing).isSome = true ↔ _
      rcases state.runtime.references.phase with _ | run | ⟨slot, activation⟩
      · simp [Occupancy.executing]
      · cases origin : run.origin <;> simp [Occupancy.executing, origin]
      · simp [Occupancy.executing])
    ⟨⟨Grid.interface, _, bank, .discounted, narrow,
        phased (.option ⟨0, by decide⟩ (.first true false))⟩,
      .inl ⟨⟨0, by decide⟩, .first true false, rfl⟩⟩
    ⟨⟨Grid.interface, _, bank, .discounted, narrow, phased .idle⟩, fun specified => by
      rcases specified with ⟨_, _, same⟩ | ⟨_, same, _⟩ <;> exact nomatch same⟩⟩

theorem TemporalControl_activeSlot_registered :
    Regula.RegisteredDecision @TemporalControl.activeSlot := ⟨⟩

theorem active_slot_value : Regula.ExecutableContract @TemporalControl.activeSlot (fun active =>
    ∀ {interface profile config criterion dimension}
      (state : TemporalControl interface profile config criterion dimension)
      (slot : Fin Acorn.FeatureConstants.skillCount),
      active state = some slot ↔
        (∃ activation, state.runtime.references.phase = .option slot activation) ∨
          ∃ run activation, state.runtime.references.phase = .exploring run ∧
            run.origin = some (slot, activation)) :=
  ⟨fun state slot => occupancy_executing_value.1 state.runtime.references.phase slot⟩

structure ForceNamed where
  action : Type
  force : Force action
  rest : Option action
  now : Instant

theorem force_named : Regula.ExecutableContract @Force.named (fun named =>
    Regula.Decides (· = true)
      (fun input : ForceNamed =>
        ((input.force.lapse = none ∨ ∃ lapse, input.force.lapse = some lapse ∧
            input.now.nanoseconds < lapse.nanoseconds) ∧ input.force.action ≠ none) ∨
          ((∃ lapse, input.force.lapse = some lapse ∧
            lapse.nanoseconds ≤ input.now.nanoseconds) ∧ input.rest ≠ none))
      (Regula.Dependent.isSome fun input : ForceNamed =>
        @named input.action input.force input.rest input.now)) :=
  ⟨decides
    (fun input => by
      rcases input with ⟨α, ⟨action, lapse⟩, rest, now⟩
      show (Force.named ⟨action, lapse⟩ rest now).isSome = true ↔ _
      rcases lapse with _ | lapse
      · cases action <;> simp [Force.named]
      · by_cases early : now.nanoseconds < lapse.nanoseconds
        · have late : ¬lapse.nanoseconds ≤ now.nanoseconds := Nat.not_le.mpr early
          cases action <;> simp [Force.named, early, late]
        · have late : lapse.nanoseconds ≤ now.nanoseconds := Nat.le_of_not_lt early
          cases rest <;> simp [Force.named, early, late])
    ⟨⟨Unit, ⟨some (), none⟩, none, ⟨0⟩⟩, .inl ⟨.inl rfl, nofun⟩⟩
    ⟨⟨Unit, ⟨none, none⟩, none, ⟨0⟩⟩, by simp⟩⟩

theorem Force_named_registered : Regula.RegisteredDecision @Force.named := ⟨⟩

theorem force_named_value : Regula.ExecutableContract @Force.named (fun named =>
    ∀ {α : Type} (force : Force α) (rest : Option α) (now : Instant),
      (force.lapse = none → named force rest now = force.action) ∧
        ∀ lapse, force.lapse = some lapse →
          named force rest now = if now.nanoseconds < lapse.nanoseconds then force.action
            else rest) :=
  ⟨fun force rest now => ⟨Force.named_lasting force rest now,
    fun lapse lapses => Force.named_lapse force rest now lapse lapses⟩⟩

theorem state_restore : Regula.ExecutableContract @AgentConstruction.State.restore
    (fun restore =>
      ∀ {construction : AgentConstruction} (state : construction.State)
        (image : construction.Image)
        (admitted : ∃ bytes, Checkpoint.loadCandidate construction bytes = .ok image),
        (restore state image admitted).isSome = true ↔ Resumable construction.profile) :=
  ⟨fun state image admitted => by
    have same := congrArg Option.isSome (state.restore_agent image admitted)
    rw [Option.isSome_map] at same
    rw [same]
    exact agent_restore.1.iff ⟨_, _, _, _, _, _, state.agent, image.image⟩⟩

private theorem runPrefix_stops {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
    (state : Agent Grid.interface profile config criterion dimension planning)
    (events : List (AgentInput config criterion dimension)) :
    (state.runPrefix events).2 = true ↔ AgentInput.stop ∈ events := by
  induction events generalizing state with
  | nil => simp [Agent.runPrefix]
  | cons event rest folded =>
    cases event <;> simp [Agent.runPrefix, Agent.input, folded]

theorem agent_run_prefix : Regula.ExecutableContract @Agent.runPrefix (fun runPrefix =>
    ∀ {profile config criterion dimension planning}
      (state : Agent Grid.interface profile config criterion dimension planning)
      (events : List (AgentInput config criterion dimension)),
      AgentPath state events (runPrefix state events).1 (runPrefix state events).2 ∧
        ((runPrefix state events).2 = true ↔ AgentInput.stop ∈ events) ∧
        runPrefix state (.stop :: events) = (state, true) ∧
        runPrefix state (.clear :: events) =
          runPrefix (Agent.initial Grid.interface profile config criterion dimension planning)
            events) :=
  ⟨fun state events => ⟨Agent.prefix_path state events, runPrefix_stops state events,
    Agent.stop_suffix state events, Agent.clear_suffix state events⟩⟩

private theorem serve_isSome {interface : Interface} {profile : FeatureProfile}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (state.serve features).isSome = true ↔ ∃ committed,
      state.runtime.references.phase = .exploring committed ∧
        0 < committed.run.remaining.val := by
  unfold TemporalControl.serve
  rcases state.runtime.references.phase with _ | committed | ⟨slot, activation⟩
  · simp
  · have remains := run_serve.1.iff ⟨_, committed.run⟩
    change (committed.run.serve).isSome = true ↔ _ at remains
    rw [show (∃ other, Occupancy.exploring committed = .exploring other ∧
        0 < other.run.remaining.val) ↔ 0 < committed.run.remaining.val from
      ⟨fun ⟨_, same, positive⟩ => by cases same; exact positive,
        fun positive => ⟨_, rfl, positive⟩⟩, ← remains]
    dsimp only
    cases committed.run.serve <;> rfl
  · simp

private theorem serveDraw_isSome {interface : Interface} {profile : FeatureProfile}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (state.serveDraw features).isSome = true ↔ ∃ committed,
      state.runtime.references.phase = .exploring committed ∧
        0 < committed.run.remaining.val := by
  unfold TemporalControl.serveDraw
  rcases state.runtime.references.phase with _ | committed | ⟨slot, activation⟩
  · simp
  · have remains := run_serve.1.iff ⟨_, committed.run⟩
    change (committed.run.serve).isSome = true ↔ _ at remains
    rw [show (∃ other, Occupancy.exploring committed = .exploring other ∧
        0 < other.run.remaining.val) ↔ 0 < committed.run.remaining.val from
      ⟨fun ⟨_, same, positive⟩ => by cases same; exact positive,
        fun positive => ⟨_, rfl, positive⟩⟩, ← remains]
    dsimp only
    cases committed.run.serve <;> rfl
  · simp

theorem temporal_serve : Regula.ExecutableContract @TemporalControl.serve (fun serve =>
    ∀ {interface profile config criterion dimension}
      (state : TemporalControl interface profile config criterion dimension)
      (features : SwiftTd.ActiveSet dimension),
      (serve state features).isSome = true ↔ ∃ committed,
        state.runtime.references.phase = .exploring committed ∧
          0 < committed.run.remaining.val) :=
  ⟨fun state features => serve_isSome state features⟩

theorem temporal_serve_frame : Regula.ExecutableContract @TemporalControl.serve (fun serve =>
    ∀ {interface profile config criterion dimension}
      (state next : TemporalControl interface profile config criterion dimension)
      (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions),
      serve state features = some (next, decision) →
        ∃ committed rest, state.runtime.references.phase = .exploring committed ∧
          committed.run.serve = some (decision.action, rest) ∧
          decision.source = .explorationContinuation ∧
          next.runtime.references.phase = .exploring (.bare rest) ∧
          next.runtime.references.rng = state.runtime.references.rng) :=
  ⟨fun state next features decision served => state.serve_frame next features decision served⟩

theorem serve_draw : Regula.ExecutableContract @TemporalControl.serveDraw (fun serve =>
    ∀ {interface profile config criterion dimension}
      (state : TemporalControl interface profile config criterion dimension)
      (features : SwiftTd.ActiveSet dimension),
      (serve state features).isSome = true ↔ ∃ committed,
        state.runtime.references.phase = .exploring committed ∧
          0 < committed.run.remaining.val) :=
  ⟨fun state features => serveDraw_isSome state features⟩

theorem serve_draw_frame : Regula.ExecutableContract @TemporalControl.serveDraw (fun serve =>
    ∀ {interface profile config criterion dimension}
      (state next : TemporalControl interface profile config criterion dimension)
      (features : SwiftTd.ActiveSet dimension) (skip : Bool)
      (decision : TemporalDecision interface.actions),
      serve state features = some (next, skip, decision) →
        ∃ committed rest, state.runtime.references.phase = .exploring committed ∧
          committed.run.serve = some (decision.action, rest) ∧
          (skip = true ↔ committed.origin = none) ∧
          decision.source = .explorationContinuation ∧
          next.runtime.references.phase = .exploring (.bare rest) ∧
          next.runtime.references.rng = state.runtime.references.rng) :=
  ⟨fun state next features skip decision served => by
    unfold TemporalControl.serveDraw at served
    cases phase : state.runtime.references.phase with
    | idle => simp [phase] at served
    | option slot activation => simp [phase] at served
    | exploring committed =>
      simp only [phase] at served
      cases hs : committed.run.serve with
      | none => simp [hs] at served
      | some pair =>
        simp only [hs, bind, Option.bind, pure, Option.some.injEq] at served
        cases served
        refine ⟨committed, pair.2, rfl, hs, ?_, rfl, ?_, ?_⟩
        · cases committed.origin <;> simp
        · split <;> rfl
        · split
          all_goals exact congrArg (·.rng) (state.interrupt_frame committed.origin).2.1⟩

def silent : (horizons : List Discount) → Cumulants horizons
  | [] => .nil
  | _ :: rest => .cons none .zero (silent rest)

def quiet : Frame Grid.interface :=
  ⟨[], Nat.zero_le _, nofun, Vector.replicate _ 0, silent _, Vector.replicate _ false, false⟩

def foreignHeld : TemporalControl Grid.interface ⟨.final, .perStep, .declared, .learned⟩ bank
    .discounted narrow :=
  let held := phased (.option ⟨0, by decide⟩ (.first true false))
  held.withSkill ⟨0, by decide⟩
    { held.runtime.lifecycle.consumers.skills.get ⟨0, by decide⟩ with
      interest := .declared .featureChannels ⟨0, by decide⟩ }

private theorem foreignHeld_unsourced (features : SwiftTd.ActiveSet narrow) :
    (foreignHeld.runtime.lifecycle.consumers.skills.get ⟨0, by decide⟩).interest.potential
      features quiet.declared = none := by
  have declared : (foreignHeld.runtime.lifecycle.consumers.skills.get ⟨0, by decide⟩).interest =
      .declared .featureChannels ⟨0, by decide⟩ := by
    simp [foreignHeld, TemporalControl.withSkill, Vector.get, Fin.cast]
  rw [declared]
  rfl

def foreignFree : TemporalControl Grid.interface ⟨.final, .perStep, .declared, .spatial⟩ bank
    .discounted narrow :=
  let initial := TemporalControl.initial Grid.interface ⟨.final, .perStep, .declared, .spatial⟩
    bank .discounted narrow
  initial.withSkill ⟨2, by decide⟩
    { initial.runtime.lifecycle.consumers.skills.get ⟨2, by decide⟩ with
      interest := .declared .featureChannels ⟨2, by decide⟩ }

private theorem select_unsourced {interface : Interface} {profile : FeatureProfile}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (hierarchy : profile.usesHierarchy = true)
    (held : state.runtime.references.phase = .option slot activation)
    (unsourced : (state.runtime.lifecycle.consumers.skills.get slot).interest.potential features
      declared = none) :
    state.selectWithOperations models plan features declared reward goal = none := by
  unfold TemporalControl.selectWithOperations
  have phase : (state.prepareSelection models features reward).runtime.references.phase =
      .option slot activation := by
    rw [← held]
    unfold TemporalControl.prepareSelection
    dsimp only
    split <;> split <;> rfl
  have lifecycle := state.prepare_lifecycle models features reward
  generalize state.prepareSelection models features reward = prepared at phase lifecycle
  have served : prepared.serve features = none := by
    unfold TemporalControl.serve
    rw [phase]
  simp only [served, hierarchy, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [phase]
  dsimp only
  rw [show ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
      slot).interest.potential features declared = none by rw [← unsourced, ← lifecycle]; rfl]
  rfl

private theorem drawFirst_unsourced {interface : Interface} {profile : FeatureProfile}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (hierarchy : profile.usesHierarchy = true)
    (held : state.runtime.references.phase = .option slot activation)
    (unsourced : (state.runtime.lifecycle.consumers.skills.get slot).interest.potential features
      declared = none) :
    state.drawFirst models plan features declared goal = none := by
  unfold TemporalControl.drawFirst
  have phase : (state.prepareDraw models features).runtime.references.phase =
      .option slot activation := by
    rw [← held]
    unfold TemporalControl.prepareDraw
    dsimp only
    split <;> rfl
  have lifecycle : (state.prepareDraw models features).runtime.lifecycle =
      state.runtime.lifecycle := by
    unfold TemporalControl.prepareDraw
    dsimp only
    split <;> rfl
  generalize state.prepareDraw models features = prepared at phase lifecycle
  have served : prepared.serveDraw features = none := by
    unfold TemporalControl.serveDraw
    rw [phase]
  simp only [served, hierarchy, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [phase]
  dsimp only
  rw [show ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
      slot).interest.potential features declared = none by rw [← unsourced, ← lifecycle]; rfl]
  rfl

theorem select_operations : Regula.ExecutableContract @TemporalControl.selectWithOperations
    (fun select =>
      (∀ {interface profile config criterion dimension}
        (state : TemporalControl interface profile config criterion dimension), state.Aligned →
        ∀ (models : OptionModelOps criterion dimension)
          (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
          (features : SwiftTd.ActiveSet dimension) (observation : Frame interface)
          (reward : Binary32) (goal : Bool),
          ∃ next decision, select state models plan features observation.declared reward goal =
            some (next, decision) ∧ next.Aligned) ∧
        ∃ (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
          (criterion : Criterion) (dimension : Dimension)
          (state : TemporalControl interface profile config criterion dimension)
          (models : OptionModelOps criterion dimension)
          (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
          (features : SwiftTd.ActiveSet dimension) (observation : Frame interface)
          (reward : Binary32) (goal : Bool),
          select state models plan features observation.declared reward goal = none) :=
  ⟨⟨fun state aligned models plan features observation reward goal =>
      state.select_total aligned models plan features observation reward goal,
    ⟨Grid.interface, _, bank, .discounted, narrow, foreignHeld,
      modelOperations .discounted narrow,
      planningBoundary .none, .empty narrow, quiet, .zero, false,
      select_unsourced _ _ _ _ _ _ _ ⟨0, by decide⟩ (.first true false) rfl rfl
        (foreignHeld_unsourced _)⟩⟩⟩

theorem temporal_select : Regula.ExecutableContract @TemporalControl.select (fun select =>
    (∀ {interface profile config criterion dimension}
      (state : TemporalControl interface profile config criterion dimension), state.Aligned →
      ∀ (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
        (observation : Frame interface) (reward : Binary32) (goal : Bool),
        ∃ next decision, select state planning features observation.declared reward goal =
          some (next, decision) ∧ next.Aligned) ∧
      ∃ (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
        (criterion : Criterion) (dimension : Dimension)
        (state : TemporalControl interface profile config criterion dimension)
        (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
        (observation : Frame interface) (reward : Binary32) (goal : Bool),
        select state planning features observation.declared reward goal = none) :=
  ⟨⟨fun state aligned planning features observation reward goal =>
      state.select_total aligned _ _ features observation reward goal,
    ⟨Grid.interface, _, bank, .discounted, narrow, foreignHeld, .none, .empty narrow, quiet,
      .zero,
      false, select_unsourced _ _ _ _ _ _ _ ⟨0, by decide⟩ (.first true false) rfl rfl
        (foreignHeld_unsourced _)⟩⟩⟩

theorem temporal_step : Regula.ExecutableContract @TemporalControl.step (fun step =>
    (∀ {interface profile config criterion dimension}
      (state : TemporalControl interface profile config criterion dimension), state.Aligned →
      ∀ (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
        (observation : Frame interface) (reward : Binary32) (goal : Bool),
        ∃ next decision, step state planning features observation reward goal =
          some (next, decision) ∧ next.Aligned) ∧
      ∃ (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
        (criterion : Criterion) (dimension : Dimension)
        (state : TemporalControl interface profile config criterion dimension)
        (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
        (observation : Frame interface) (reward : Binary32) (goal : Bool),
        step state planning features observation reward goal = none) :=
  ⟨⟨fun state aligned planning features observation reward goal =>
      state.step_total aligned planning features observation reward goal,
    ⟨Grid.interface, _, bank, .discounted, narrow, foreignHeld, .none, .empty narrow, quiet,
      .zero,
      false, by
        rw [TemporalControl.step_parts]
        change (foreignHeld.selectWithOperations _ _ _ quiet.declared _ _).map _ = none
        rw [select_unsourced foreignHeld _ _ _ _ _ _ ⟨0, by decide⟩ (.first true false) rfl rfl
          (foreignHeld_unsourced _)]
        rfl⟩⟩⟩

theorem draw_first : Regula.ExecutableContract @TemporalControl.drawFirst (fun draw =>
    (∀ {interface profile config criterion dimension}
      (state : TemporalControl interface profile config criterion dimension), state.Aligned →
      ∀ (models : OptionModelOps criterion dimension)
        (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
        (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (goal : Bool),
        ∃ next owed decision, draw state models plan features observation.declared goal =
          some (next, owed, decision) ∧ next.Aligned) ∧
      ∃ (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
        (criterion : Criterion) (dimension : Dimension)
        (state : TemporalControl interface profile config criterion dimension)
        (models : OptionModelOps criterion dimension)
        (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
        (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (goal : Bool),
        draw state models plan features observation.declared goal = none) :=
  ⟨⟨fun state aligned models plan features observation goal =>
      state.drawFirst_total aligned models plan features observation goal,
    ⟨Grid.interface, _, bank, .discounted, narrow, foreignHeld,
      modelOperations .discounted narrow,
      planningBoundary .none, .empty narrow, quiet, false,
      drawFirst_unsourced _ _ _ _ _ _ ⟨0, by decide⟩ (.first true false) rfl rfl
        (foreignHeld_unsourced _)⟩⟩⟩

theorem dispatch_meta : Regula.ExecutableContract @TemporalControl.dispatchMeta (fun dispatch =>
    ∀ {interface profile config criterion dimension}
      (state : TemporalControl interface profile config criterion dimension)
      (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
      (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
      (decision : PolicyDecision metaCount) (ended : Option EndEvent),
      (dispatch state models features declared reward goal decision ended).isSome = true ↔
        ∀ slot : Fin Acorn.FeatureConstants.skillCount, decision.action.val = slot.val + 1 →
          (∃ assignment,
              state.runtime.lifecycle.consumers.skills[slot.val].interest = .learned assignment) ∨
            ∃ tag, state.runtime.lifecycle.consumers.skills[slot.val].interest =
              .declared declared.origin tag) :=
  ⟨fun state models features declared reward goal decision ended => by
    rw [TemporalControl.dispatchMeta_eq]
    have kept := state.learnMeta_interest features decision
    generalize state.learnMeta features decision = learned at kept
    dsimp only
    cases named : skillOfMeta decision.action with
    | none =>
      refine ⟨fun _ slot same =>
        absurd ((skill_of_meta_value.1 _ slot).mpr same) (by simp [named]), fun _ => rfl⟩
    | some slot =>
      dsimp only
      have value := (skill_of_meta_value.1 decision.action slot).mp named
      have only : ∀ other : Fin Acorn.FeatureConstants.skillCount,
          decision.action.val = other.val + 1 → other = slot := fun other same =>
        Fin.ext (by omega)
      have interest : (learned.runtime.lifecycle.consumers.skills.get slot).interest =
          state.runtime.lifecycle.consumers.skills[slot.val].interest := kept slot
      rw [interest]
      constructor
      · intro accepted other same
        rw [only other same]
        revert accepted
        cases state.runtime.lifecycle.consumers.skills[slot.val].interest with
        | learned assignment => exact fun _ => .inl ⟨assignment, rfl⟩
        | declared origin tag =>
          simp only [Interest.potential_def]
          split
          · rename_i same
            exact fun _ => .inr ⟨tag, by rw [same]⟩
          · simp [bind, Option.bind]
      · intro sourced
        rcases sourced slot value with
          ⟨assignment, learnedInterest⟩ | ⟨tag, declaredInterest⟩
        · rw [learnedInterest]
          rfl
        · rw [declaredInterest]
          simp [Interest.potential_def, bind, Option.bind]⟩

theorem at_boundary : Regula.ExecutableContract @TemporalControl.atBoundary (fun boundary =>
    (∀ {interface profile config criterion dimension}
      (state : TemporalControl interface profile config criterion dimension), state.Aligned →
      ∀ (models : OptionModelOps criterion dimension)
        (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
        (features : SwiftTd.ActiveSet dimension) (observation : Frame interface)
        (reward : Binary32) (goal : Bool)
        (closing : Option (Closing interface.actions config criterion dimension interface.layout
          (EndingPayload (profile.mode != .frozen))))
        (ended : Option EndEvent),
        ∃ next decision, boundary state models plan features observation.declared reward goal
          closing ended = some (next, decision) ∧ next.Aligned) ∧
      ∃ (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
        (criterion : Criterion) (dimension : Dimension)
        (state : TemporalControl interface profile config criterion dimension)
        (models : OptionModelOps criterion dimension)
        (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
        (features : SwiftTd.ActiveSet dimension) (observation : Frame interface)
        (reward : Binary32) (goal : Bool)
        (closing : Option (Closing interface.actions config criterion dimension interface.layout
          (EndingPayload (profile.mode != .frozen))))
        (ended : Option EndEvent),
        boundary state models plan features observation.declared reward goal closing ended =
          none) :=
  ⟨⟨fun state aligned models plan features observation reward goal closing ended =>
      state.boundary_total aligned models plan features observation reward goal closing ended,
    ⟨Grid.interface, _, bank, .discounted, narrow, foreignFree,
      modelOperations .discounted narrow,
      planningBoundary .none, .empty narrow, quiet, .zero, false, none, none,
      Option.isNone_iff_eq_none.mp (by decide +kernel)⟩⟩⟩

theorem draw_boundary : Regula.ExecutableContract @TemporalControl.drawBoundary (fun boundary =>
    (∀ {interface profile config criterion dimension}
      (state : TemporalControl interface profile config criterion dimension), state.Aligned →
      ∀ (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
        (features : SwiftTd.ActiveSet dimension) (observation : Frame interface)
        (closing : Option (Closing interface.actions config criterion dimension interface.layout
          (EndingPayload (profile.mode != .frozen))))
        (estimate : Binary32),
        ∃ next owed decision, boundary state plan features observation.declared closing estimate =
          some (next, owed, decision) ∧ next.Aligned) ∧
      ∃ (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
        (criterion : Criterion) (dimension : Dimension)
        (state : TemporalControl interface profile config criterion dimension)
        (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
        (features : SwiftTd.ActiveSet dimension) (observation : Frame interface)
        (closing : Option (Closing interface.actions config criterion dimension interface.layout
          (EndingPayload (profile.mode != .frozen))))
        (estimate : Binary32),
        boundary state plan features observation.declared closing estimate = none) :=
  ⟨⟨fun state aligned plan features observation closing estimate =>
      state.drawBoundary_total aligned plan features observation closing estimate,
    ⟨Grid.interface, _, bank, .discounted, narrow, foreignFree, planningBoundary .none,
      .empty narrow, quiet, none, .zero, Option.isNone_iff_eq_none.mp (by decide +kernel)⟩⟩⟩

theorem released_environment : Regula.ExecutableContract @Host.Released.environment
    (fun environment =>
      ∀ {config α goal cap} (released : Host.Released config α goal cap),
        (∀ transition, environment released = .ok transition ↔
          released = .accepted transition) ∧
          ∀ error, environment released = .error error ↔
            ∃ selected, released = .refused error selected) :=
  ⟨fun released => by
    cases released with
    | accepted transition =>
      exact ⟨fun other => by simp [Host.Released.environment],
        fun error => by simp [Host.Released.environment]⟩
    | refused error selected =>
      exact ⟨fun other => by simp [Host.Released.environment],
        fun other => by simp [Host.Released.environment]⟩⟩

theorem owned_environment : Regula.ExecutableContract @Host.OwnedStep.environment
    (fun environment =>
      ∀ {config α goal cap} (selected : Host.OwnedStep config α goal cap),
        (environment selected).map (fun transition => (transition.world, transition.result)) =
            selected.before.run.world.step selected.action ∧
          ∀ transition, environment selected = .ok transition →
            transition.selected = selected) :=
  ⟨fun selected => by
    unfold Host.OwnedStep.environment
    split
    · rename_i error stepped
      exact ⟨by rw [stepped]; rfl, fun _ refused => nomatch refused⟩
    · rename_i world result stepped
      exact ⟨stepped.symm, fun _ accepted => by cases accepted; rfl⟩⟩

theorem prepared_environment : Regula.ExecutableContract @Host.PreparedStep.environment
    (fun environment =>
      ∀ {config α β goal cap} (prepared : Host.PreparedStep config α β goal cap),
        (environment prepared).map (fun transition => (transition.world, transition.result)) =
            prepared.before.run.world.step prepared.action ∧
          ∀ transition, environment prepared = .ok transition →
            transition.prepared = prepared) :=
  ⟨fun prepared => by
    unfold Host.PreparedStep.environment
    split
    · rename_i error stepped
      exact ⟨by rw [stepped]; rfl, fun _ refused => nomatch refused⟩
    · rename_i world result stepped
      exact ⟨stepped.symm, fun _ accepted => by cases accepted; rfl⟩⟩

private theorem sense_exact {config : Host.WorldConfig} {α : Type} {goal : Host.Goal}
    {cap : UInt64} (attempt : Host.Attempt config α goal cap) :
    (attempt.sense = .ok none ↔ Stopped attempt) ∧
      (∀ error, attempt.sense = .error error ↔
        ¬Stopped attempt ∧ attempt.run.world.observe = .error error) ∧
      ∀ input, attempt.sense = .ok (some input) → input.before = attempt := by
  have finished : attempt.finished = true ↔ Stopped attempt := by
    simp [Host.Attempt.finished, Stopped]
  have bound := attempt.steps.isLt
  unfold Host.Attempt.sense
  by_cases stopped : Stopped attempt
  · have done := finished.mpr stopped
    simp [done, stopped, pure, Except.pure]
  · have running : attempt.finished = false := by
      cases h : attempt.finished
      · rfl
      · exact absurd (finished.mp h) stopped
    have below : attempt.steps.val < cap.toNat := by
      have : attempt.steps.val ≠ cap.toNat := fun same => stopped (.inl same)
      omega
    simp only [running, Bool.false_eq_true, ite_false, below, dite_true, stopped,
      not_false_eq_true, true_and]
    split
    · rename_i failure observed
      refine ⟨⟨fun same => (nomatch same), False.elim⟩, fun other => ?_,
        fun _ refused => (nomatch refused)⟩
      rw [observed]
      constructor
      · intro same
        cases same
        rfl
      · intro same
        cases same
        rfl
    · rename_i observation observed
      refine ⟨⟨fun same => (nomatch same), False.elim⟩, fun other => ?_,
        fun input accepted => ?_⟩
      · constructor
        · intro same
          exact (nomatch same)
        · intro same
          rw [observed] at same
          exact (nomatch same)
      · cases accepted
        rfl

theorem attempt_sense : Regula.ExecutableContract @Host.Attempt.sense (fun sense =>
    ∀ {config α goal cap} (attempt : Host.Attempt config α goal cap),
      (sense attempt = .ok none ↔ Stopped attempt) ∧
        (∀ error, sense attempt = .error error ↔
          ¬Stopped attempt ∧ attempt.run.world.observe = .error error) ∧
        ∀ input, sense attempt = .ok (some input) → input.before = attempt) :=
  ⟨fun attempt => sense_exact attempt⟩

theorem attempt_tick : Regula.ExecutableContract @Host.Attempt.tick (fun tick =>
    ∀ {order config α β goal cap} (callbacks : Host.AgentCallbacks order α β)
      (context : Host.GoalContext) (attempt : Host.Attempt config α goal cap),
      Stopped attempt → tick callbacks context attempt = .ok (attempt, none)) :=
  ⟨fun callbacks context attempt stopped =>
    Host.Attempt.tick_finished callbacks context attempt
      (by simpa [Host.Attempt.finished, Stopped] using stopped)⟩

theorem attempt_finish : Regula.ExecutableContract @Host.Attempt.finish (fun finish =>
    ∀ {order config α β goal cap} (callbacks : Host.AgentCallbacks order α β)
      (context : Host.GoalContext) (attempt : Host.Attempt config α goal cap)
      (run : Host.RunState config α) (outcome : Host.GoalOutcome) (frame : Host.StepFrame β),
      finish callbacks context attempt = .ok (run, outcome, frame) →
        run = { attempt.run with agent := (callbacks.recordAttempt attempt.run.agent goal.family
            context.cycle attempt.steps.val.toUInt64 attempt.run.carried.events.done) } ∧
          outcome.position = run.world.body.position.position ∧
          frame.position = outcome.position) :=
  ⟨fun callbacks context attempt run outcome frame finished =>
    Host.Attempt.finish_position callbacks context attempt run outcome frame finished⟩

theorem attempt_close : Regula.ExecutableContract @Host.Attempt.close (fun close =>
    ∀ {order config α β goal cap} (callbacks : Host.AgentCallbacks order α β)
      (context : Host.GoalContext) (attempt : Host.Attempt config α goal cap),
      (∀ result, close callbacks context attempt = .ok result ↔
        attempt.finish callbacks context = .ok result) ∧
        ∀ refusal, close callbacks context attempt = .error refusal ↔
          refusal.learned = none ∧ attempt.finish callbacks context = .error refusal.error) :=
  ⟨fun callbacks context attempt => by
    unfold Host.Attempt.close
    cases attempt.finish callbacks context with
    | error error =>
      dsimp only
      constructor
      · intro result
        exact ⟨fun same => (nomatch same), fun same => (nomatch same)⟩
      · intro refusal
        constructor
        · intro same
          cases same
          exact ⟨rfl, rfl⟩
        · intro ⟨kept, same⟩
          cases refusal
          cases kept
          cases same
          rfl
    | ok result =>
      dsimp only
      constructor
      · intro other
        simp only [Except.ok.injEq]
      · intro refusal
        exact ⟨fun same => (nomatch same), fun ⟨_, same⟩ => (nomatch same)⟩⟩

theorem attempt_complete : Regula.ExecutableContract @Host.Attempt.complete (fun complete =>
    ∀ {order config α β goal cap} (callbacks : Host.AgentCallbacks order α β)
      (context : Host.GoalContext) (fuel : Nat) (attempt : Host.Attempt config α goal cap)
      (error : Host.WorldError) (learned : Host.OwnedStep config α goal cap),
      complete callbacks context fuel attempt = .error ⟨error, some learned⟩ →
        ∃ (passes : Nat) (reached : Host.Attempt config α goal cap)
          (input : Host.DecisionInput config α goal cap),
          passes < fuel ∧ Host.Attempt.Reaches callbacks passes attempt reached ∧
            reached.finished = false ∧ reached.sense = .ok (some input) ∧
            learned = input.selectOwned callbacks ∧
            (input.selectOwned callbacks).environment = .error error) :=
  ⟨fun callbacks context fuel attempt error learned refused =>
    Host.Attempt.complete_learned callbacks context fuel attempt error learned refused⟩

def waiting : Host.AgentCallbacks .learnThenAct Unit Unit :=
  ⟨Unit, fun _ _ _ => (.wait, ()), fun _ => (), fun _ _ _ => (), fun _ _ _ _ _ => (), fun _ => (),
    fun _ => ⟨.zero, .zero, .zero⟩⟩

private theorem ok_of_isOk {ε α : Type} {result : Except ε α} (accepted : result.isOk = true) :
    ∃ value, result = .ok value := by
  cases result with
  | error error => exact absurd accepted (by simp [Except.isOk, Except.toBool])
  | ok value => exact ⟨value, rfl⟩

private theorem fresh_waits : ((fresh 1).run.world.step .wait).isOk = true := by
  decide +kernel

theorem ansi_tick : Regula.ExecutableContract @Host.AnsiState.tick (fun tick =>
    ∀ {config α β} (state next : Host.AnsiState config α)
      (callbacks : Host.AgentCallbacks .learnThenAct α β) (index : Nat)
      (frame : Host.AnsiFrame config),
      tick state callbacks index = .ok (next, frame) → next.observation = state.observation) :=
  ⟨fun state next callbacks index frame ticked =>
    Host.AnsiState.tick_observation state next callbacks index frame ticked⟩

theorem ansi_tick_accepts : Regula.ExecutableContract @Host.AnsiState.tick (fun tick =>
    ∀ (observation : Host.Observation) (index : Nat),
      (tick (⟨(fresh 1).run.world, (), {}, observation, 0⟩ : Host.AnsiState wide Unit) waiting
        index).isOk = true) :=
  ⟨fun observation index => by
    obtain ⟨⟨world, result⟩, stepped⟩ := ok_of_isOk fresh_waits
    unfold Host.AnsiState.tick
    simp only [Host.AgentCallbacks.act, waiting, stepped, Except.mapError, bind, Except.bind]
    rfl⟩

theorem world_initial : Regula.ExecutableContract Host.World.initial (fun initial =>
    ∀ (config : Host.WorldConfig) (world : Host.World config), initial config = .ok world →
      world.time = 0 ∧ world.goal = none ∧ world.goalStart = 0 ∧
        world.body.energy = Host.Energy.new FeatureConstants.energyMax ∧
        world.body.facing = .north ∧ world.food.entries = #[] ∧ world.harvested.size = 0) :=
  ⟨fun config world initialized => Host.World.initial_fields config world initialized⟩

theorem world_observe : Regula.ExecutableContract @Host.World.observe (fun observe =>
    ∀ {config} (world : Host.World config) (observation : Host.Observation),
      observe world = .ok observation → observation.task = world.taskObservation) :=
  ⟨fun world observation observed => Host.World.observe_task world observation observed⟩

theorem prepared_commit : Regula.ExecutableContract @Host.PreparedStep.commit (fun commit =>
    ∀ {order config α β goal cap} (prepared : Host.PreparedStep config α β goal cap)
      (callbacks : Host.AgentCallbacks order α β),
      (∀ error, commit prepared callbacks = .error error ↔
        prepared.before.run.world.step prepared.action = .error error) ∧
        ∀ next, commit prepared callbacks = .ok next →
          ∃ result,
            prepared.before.run.world.step prepared.action = .ok (next.run.world, result) ∧
            next.run.carried = result.raw ∧ next.steps.val = prepared.before.steps.val + 1) :=
  ⟨fun prepared callbacks => by
    unfold Host.PreparedStep.commit Host.PreparedStep.environment
    split
    · rename_i error stepped
      refine ⟨fun other => ?_, fun _ accepted => (nomatch accepted)⟩
      rw [stepped]
      constructor
      · intro same
        cases same
        rfl
      · intro same
        cases same
        rfl
    · rename_i world result stepped
      refine ⟨fun other => ?_, fun next accepted => ?_⟩
      · constructor
        · intro same
          exact (nomatch same)
        · intro same
          rw [stepped] at same
          exact (nomatch same)
      · cases accepted
        exact ⟨result, stepped, rfl, rfl⟩⟩

private theorem baselineTick_exact {config : Host.WorldConfig} {cap : UInt64}
    (state : Host.BaselineAttempt config cap) :
    (state.result.done = true ∨ cap.toNat ≤ state.steps.val → state.tick = .ok state) ∧
      (state.result.done = false → state.steps.val < cap.toNat →
        (∀ error, state.tick = .error error ↔
          state.world.step (Host.baselineAction state.rng).1 = .error error) ∧
          ∀ next, state.tick = .ok next →
            state.world.step (Host.baselineAction state.rng).1 = .ok (next.world, next.result) ∧
              next.rng = (Host.baselineAction state.rng).2 ∧
              next.steps.val = state.steps.val + 1) := by
  constructor
  · intro stopped
    unfold Host.BaselineAttempt.tick
    by_cases done : state.result.done = true
    · simp [done]
    · have capped : cap.toNat ≤ state.steps.val := by
        rcases stopped with same | capped
        · exact absurd same done
        · exact capped
      have notBelow : ¬state.steps.val < cap.toNat := Nat.not_lt.mpr capped
      simp [done, notBelow]
  · intro running below
    unfold Host.BaselineAttempt.tick
    simp only [running, Bool.false_eq_true, ite_false, below, dite_true]
    split
    · rename_i error stepped
      refine ⟨fun other => ?_, fun _ accepted => (nomatch accepted)⟩
      rw [stepped]
      constructor
      · intro same
        cases same
        rfl
      · intro same
        cases same
        rfl
    · rename_i world result stepped
      refine ⟨fun other => ?_, fun next accepted => ?_⟩
      · constructor
        · intro same
          exact (nomatch same)
        · intro same
          rw [stepped] at same
          exact (nomatch same)
      · cases accepted
        exact ⟨stepped, rfl, rfl⟩

theorem baseline_tick : Regula.ExecutableContract @Host.BaselineAttempt.tick (fun tick =>
    ∀ {config cap} (state : Host.BaselineAttempt config cap),
      (state.result.done = true ∨ cap.toNat ≤ state.steps.val → tick state = .ok state) ∧
        (state.result.done = false → state.steps.val < cap.toNat →
          (∀ error, tick state = .error error ↔
            state.world.step (Host.baselineAction state.rng).1 = .error error) ∧
            ∀ next, tick state = .ok next →
              state.world.step (Host.baselineAction state.rng).1 = .ok (next.world, next.result) ∧
                next.rng = (Host.baselineAction state.rng).2 ∧
                next.steps.val = state.steps.val + 1)) :=
  ⟨fun state => baselineTick_exact state⟩

theorem Checkpoint_load_registered : Regula.RegisteredDecision @Checkpoint.load := ⟨⟩

theorem Checkpoint_admitSum_registered : Regula.RegisteredDecision @Checkpoint.admitSum := ⟨⟩

theorem Agreement_precision_registered : Regula.RegisteredDecision @Agreement.precision := ⟨⟩

theorem Portable_expSaturation_registered : Regula.RegisteredDecision @Portable.expSaturation := ⟨⟩

theorem Features_Interest_potential_registered :
    Regula.RegisteredDecision @Features.Interest.potential := ⟨⟩

theorem Host_Endurance_rankIndex_registered :
    Regula.RegisteredDecision @Host.Endurance.rankIndex := ⟨⟩

theorem Host_Position_translate_registered :
    Regula.RegisteredDecision @Host.Position.translate := ⟨⟩

theorem Host_TaskObservation_satisfied_registered :
    Regula.RegisteredDecision @Host.TaskObservation.satisfied := ⟨⟩

theorem Host_World_goalSatisfied_registered :
    Regula.RegisteredDecision @Host.World.goalSatisfied := ⟨⟩

theorem Host_World_advanceActions_registered :
    Regula.RegisteredDecision @Host.World.advanceActions := ⟨⟩

theorem Host_World_tileKind_registered : Regula.RegisteredDecision @Host.World.tileKind := ⟨⟩

theorem Host_World_enterable_registered : Regula.RegisteredDecision @Host.World.enterable := ⟨⟩

theorem Host_terrain_registered : Regula.RegisteredDecision @Host.terrain := ⟨⟩

theorem Host_walkableTile_registered : Regula.RegisteredDecision @Host.walkableTile := ⟨⟩

theorem Host_regionBlocked_registered : Regula.RegisteredDecision @Host.regionBlocked := ⟨⟩

theorem Host_replayCertified_registered : Regula.RegisteredDecision @Host.replayCertified := ⟨⟩

theorem Host_stanceCertified_registered : Regula.RegisteredDecision @Host.stanceCertified := ⟨⟩

theorem Host_ReplayCertificate_check_registered :
    Regula.RegisteredDecision @Host.ReplayCertificate.check := ⟨⟩

theorem Host_StanceCertificate_check_registered :
    Regula.RegisteredDecision @Host.StanceCertificate.check := ⟨⟩

theorem Host_BlockedCertificate_check_registered :
    Regula.RegisteredDecision @Host.BlockedCertificate.check := ⟨⟩

theorem Host_countKindNear_registered : Regula.RegisteredDecision @Host.countKindNear := ⟨⟩

theorem Host_considerSpawn_registered : Regula.RegisteredDecision @Host.considerSpawn := ⟨⟩

theorem Host_payAndAct_registered : Regula.RegisteredDecision @Host.payAndAct := ⟨⟩

theorem Host_performAction_registered : Regula.RegisteredDecision @Host.performAction := ⟨⟩

theorem Host_Released_environment_registered :
    Regula.RegisteredDecision @Host.Released.environment := ⟨⟩

theorem NumericState_clearAt_registered : Regula.RegisteredDecision @NumericState.clearAt := ⟨⟩

theorem Checkpoint_resume_registered : Regula.RegisteredDecision @Checkpoint.resume := ⟨⟩

theorem Host_valueNoise_registered : Regula.RegisteredDecision @Host.valueNoise := ⟨⟩

theorem Host_octaveLoop_registered : Regula.RegisteredDecision @Host.octaveLoop := ⟨⟩

theorem Host_fbm_registered : Regula.RegisteredDecision @Host.fbm := ⟨⟩

theorem Host_World_initial_registered : Regula.RegisteredDecision @Host.World.initial := ⟨⟩

theorem Host_World_observe_registered : Regula.RegisteredDecision @Host.World.observe := ⟨⟩

theorem Host_World_observeTile_registered : Regula.RegisteredDecision @Host.World.observeTile := ⟨⟩

theorem Host_World_step_registered : Regula.RegisteredDecision @Host.World.step := ⟨⟩

theorem Host_wanderPopulation_registered : Regula.RegisteredDecision @Host.wanderPopulation := ⟨⟩

theorem Host_foodTrials_registered : Regula.RegisteredDecision @Host.foodTrials := ⟨⟩

theorem Host_spawnFood_registered : Regula.RegisteredDecision @Host.spawnFood := ⟨⟩

theorem Host_selectSpawn_registered : Regula.RegisteredDecision @Host.selectSpawn := ⟨⟩

theorem Host_initializeDeer_registered : Regula.RegisteredDecision @Host.initializeDeer := ⟨⟩

end Acorn.Decisions
