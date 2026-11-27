import Acorn.Arithmetic
import Acorn.Constants
import Acorn.Portable

namespace Acorn

inductive Discount where
  | g90
  | g95
  | g99
  deriving DecidableEq

def Discount.gamma : Discount → Binary32
  | .g90 => ⟨Acorn.Constants.gamma90Bits⟩
  | .g95 => ⟨Acorn.Constants.gamma95Bits⟩
  | .g99 => ⟨Acorn.Constants.gamma99Bits⟩

def Discount.horizon (discount : Discount) : Binary32 :=
  let one : Binary32 := ⟨0x3f800000⟩
  one.div (one.sub discount.gamma)

inductive ValueRule where
  | discounted (discount : Discount)
  | differential
  deriving DecidableEq

def ValueRule.bound : ValueRule → Binary32
  | .discounted discount => discount.horizon
  | .differential => Discount.g99.horizon

def ValueRule.gamma : ValueRule → Binary32
  | .discounted discount => discount.gamma
  | .differential => ⟨0x3f800000⟩

def Discount.domain (discount : Discount) : Symmetric32 where
  range := {
    lower := discount.horizon.negate
    upper := discount.horizon
    lowerFinite := by cases discount <;> decide
    upperFinite := by cases discount <;> decide
    ordered := by cases discount <;> decide
  }
  symmetric := rfl
  zeroLegal := by cases discount <;> decide

def ValueRule.domain : ValueRule → Symmetric32
  | .discounted discount => discount.domain
  | .differential => Discount.g99.domain

structure Weight (rule : ValueRule) where
  bounded : Bounded32 rule.domain.range

def Weight.value {rule : ValueRule} (weight : Weight rule) : Binary32 := weight.bounded.value

theorem weight_legal {rule : ValueRule} (weight : Weight rule) :
    rule.domain.range.Contains weight.value := weight.bounded.legal

def ValueRule.domain90 : Symmetric32 := (ValueRule.discounted .g90).domain
def ValueRule.domain95 : Symmetric32 := (ValueRule.discounted .g95).domain
def ValueRule.domain99 : Symmetric32 := (ValueRule.discounted .g99).domain
def ValueRule.domainDifferential : Symmetric32 := ValueRule.differential.domain

def Weight.project : (rule : ValueRule) → Binary32 → Weight rule
  | .discounted .g90, raw => ⟨Bounded32.projectSymmetric ValueRule.domain90 raw⟩
  | .discounted .g95, raw => ⟨Bounded32.projectSymmetric ValueRule.domain95 raw⟩
  | .discounted .g99, raw => ⟨Bounded32.projectSymmetric ValueRule.domain99 raw⟩
  | .differential, raw => ⟨Bounded32.projectSymmetric ValueRule.domainDifferential raw⟩

theorem Weight.project_eq (rule : ValueRule) (raw : Binary32) :
    Weight.project rule raw = ⟨Bounded32.projectSymmetric rule.domain raw⟩ := by
  cases rule with
  | discounted discount => cases discount <;> rfl
  | differential => rfl

theorem Weight.project_zero (rule : ValueRule) : (Weight.project rule .zero).value = .zero := by
  rw [Weight.project_eq]
  exact rule.domain.symmetric_project_identity _ rule.domain.zeroLegal

def Weight.admit (rule : ValueRule) (raw : Binary32) : Option (Weight rule) :=
  (Bounded32.admit rule.domain.range raw).map Weight.mk

theorem weight_admit_exact (rule : ValueRule) (raw : Binary32) (stored : Weight rule)
    (h : Weight.admit rule raw = some stored) : stored.value = raw := by
  unfold Weight.admit at h
  cases hb : Bounded32.admit rule.domain.range raw with
  | none => simp [hb] at h
  | some bounded =>
    simp only [hb, Option.map_some, Option.some.injEq] at h
    subst stored
    exact (Bounded32.admit_exact _ _ _ hb).1

theorem weight_admit_refuses (rule : ValueRule) (raw : Binary32) :
    Weight.admit rule raw = none ↔ ¬rule.domain.range.Contains raw := by
  simp [Weight.admit, Bounded32.admit_refuses]

abbrev DifferentialValue := Weight .differential

def Discount.predictionRange (discount : Discount) : Interval32 where
  lower := .zero
  upper := discount.horizon
  lowerFinite := by decide
  upperFinite := discount.domain.range.upperFinite
  ordered := discount.domain.zeroLegal.2.2

abbrev Prediction (discount : Discount) := Bounded32 discount.predictionRange

def Prediction.project (discount : Discount) (raw : Binary32) : Prediction discount :=
  Bounded32.project discount.predictionRange raw

def Prediction.admit (discount : Discount) (raw : Binary32) : Option (Prediction discount) :=
  Bounded32.admit discount.predictionRange raw

inductive Role where
  | demon
  | control
  | optionSkill
  deriving DecidableEq

structure Config where
  role : Role
  rule : ValueRule
  deriving DecidableEq

def Config.lambda (config : Config) : Binary32 :=
  match config.role with
  | .demon => ⟨Acorn.Constants.gamma95Bits⟩
  | .control | .optionSkill => ⟨Acorn.Constants.gamma90Bits⟩

def Config.alphaInitial (config : Config) : Binary32 :=
  match config.role with
  | .demon | .control => ⟨Acorn.Constants.alphaInit5e5Bits⟩
  | .optionSkill => ⟨Acorn.Constants.alphaInit1e4Bits⟩

def Config.eta (config : Config) : Binary32 :=
  match config.role with
  | .demon | .control => ⟨Acorn.Constants.eta01Bits⟩
  | .optionSkill => ⟨Acorn.Constants.eta025Bits⟩

def Config.etaMin (_config : Config) : Binary32 := ⟨Acorn.Constants.etaMin1e10Bits⟩

def Config.epsilon (_config : Config) : Binary32 := ⟨Acorn.Constants.epsilon1e5Bits⟩

def Config.decay (_config : Config) : Binary32 := ⟨Acorn.Constants.decay0999Bits⟩

def Config.metaStep (config : Config) : Binary32 :=
  match config.role with
  | .demon | .control => ⟨Acorn.Constants.meta1e3Bits⟩
  | .optionSkill => ⟨Acorn.Constants.meta3e2Bits⟩

structure StepSizeRails (config : Config) where
  range : Interval32
  lowerIdentity : range.lower = Portable.ln config.etaMin
  upperIdentity : range.upper = Portable.ln config.eta

set_option maxRecDepth 8192 in
def StepSizeRails.ofConfig (config : Config) : StepSizeRails config where
  range := {
    lower := Portable.ln config.etaMin
    upper := Portable.ln config.eta
    lowerFinite := by rcases config with ⟨role, rule⟩; cases role <;> simp only [Config.etaMin] <;> decide
    upperFinite := by rcases config with ⟨role, rule⟩; cases role <;> simp only [Config.eta] <;> decide
    ordered := by rcases config with ⟨role, rule⟩; cases role <;> simp only [Config.etaMin, Config.eta] <;> decide
  }
  lowerIdentity := rfl
  upperIdentity := rfl

def StepSizeRails.admit (config : Config) : Option (StepSizeRails config) :=
  match h : Interval32.admit (Portable.ln config.etaMin) (Portable.ln config.eta) with
  | none => none
  | some range =>
    let identities := Interval32.interval_admit_exact _ _ range h
    some ⟨range, identities.1, identities.2⟩

theorem rails_admission_total (config : Config) : StepSizeRails.admit config ≠ none := by
  let rails := StepSizeRails.ofConfig config
  have hvalid : (Portable.ln config.etaMin).Finite ∧ (Portable.ln config.eta).Finite ∧
      (Portable.ln config.etaMin).key ≤ (Portable.ln config.eta).key :=
    ⟨rails.lowerIdentity ▸ rails.range.lowerFinite,
      rails.upperIdentity ▸ rails.range.upperFinite,
      rails.lowerIdentity ▸ rails.upperIdentity ▸ rails.range.ordered⟩
  unfold StepSizeRails.admit
  split
  · rename_i h
    exact False.elim ((Interval32.interval_admit_refuses _ _).mp h hvalid)
  · simp

abbrev LogStepSize {config : Config} (rails : StepSizeRails config) := Bounded32 rails.range

def LogStepSize.project {config : Config} (rails : StepSizeRails config) (raw : Binary32) :
    LogStepSize rails := Bounded32.project rails.range raw

def LogStepSize.admit {config : Config} (rails : StepSizeRails config) (raw : Binary32) :
    Option (LogStepSize rails) := Bounded32.admit rails.range raw

def LogStepSize.alpha {config : Config} {rails : StepSizeRails config}
    (stored : LogStepSize rails) : Binary32 := Portable.exp stored.value

def LogStepSize.alphaAfter {config : Config} {rails : StepSizeRails config}
    (previous : LogStepSize rails) (stored : Binary32) (next : LogStepSize rails) : Binary32 :=
  if next.value = previous.value then stored else next.alpha

theorem LogStepSize.alphaAfter_eq {config : Config} {rails : StepSizeRails config}
    (previous : LogStepSize rails) (stored : Binary32) (next : LogStepSize rails)
    (evaluated : stored = previous.alpha) : previous.alphaAfter stored next = next.alpha := by
  subst evaluated
  unfold LogStepSize.alphaAfter
  split
  · rename_i same
    exact congrArg Portable.exp same.symm
  · rfl

theorem LogStepSize.alphaAfter_self {config : Config} {rails : StepSizeRails config}
    (previous next : LogStepSize rails) : previous.alphaAfter previous.alpha next = next.alpha :=
  previous.alphaAfter_eq previous.alpha next rfl

def LogStepSize.Evaluated {config : Config} {rails : StepSizeRails config} {capacity : Nat}
    (beta : Vector (LogStepSize rails) capacity) (alpha : Vector Binary32 capacity) : Prop :=
  ∀ (index : Nat) (inside : index < capacity), alpha[index] = beta[index].alpha

theorem LogStepSize.Evaluated.set {config : Config} {rails : StepSizeRails config}
    {capacity : Nat} {beta : Vector (LogStepSize rails) capacity}
    {alpha : Vector Binary32 capacity} (evaluated : LogStepSize.Evaluated beta alpha)
    (index : Nat) (inside : index < capacity) (value : LogStepSize rails) (word : Binary32)
    (same : word = value.alpha) :
    LogStepSize.Evaluated (beta.set index value inside) (alpha.set index word inside) := by
  intro other otherInside
  by_cases here : index = other
  · subst here
    rw [Vector.getElem_set_self, Vector.getElem_set_self]
    exact same
  · rw [Vector.getElem_set_ne inside otherInside here,
      Vector.getElem_set_ne inside otherInside here]
    exact evaluated other otherInside

theorem LogStepSize.Evaluated.replicate {config : Config} {rails : StepSizeRails config}
    (capacity : Nat) (value : LogStepSize rails) :
    LogStepSize.Evaluated (Vector.replicate capacity value)
      (Vector.replicate capacity value.alpha) := by
  intro index inside
  rw [Vector.getElem_replicate, Vector.getElem_replicate]

theorem LogStepSize.Evaluated.map {config : Config} {rails : StepSizeRails config}
    {capacity : Nat} (beta : Vector (LogStepSize rails) capacity) :
    LogStepSize.Evaluated beta (beta.map fun stored => stored.alpha) := by
  intro index inside
  rw [Vector.getElem_map]

def StepSizeRails.initial {config : Config} (rails : StepSizeRails config) :
    LogStepSize rails := LogStepSize.project rails (Portable.ln config.alphaInitial)

def StepSizeRails.decay {config : Config} (_rails : StepSizeRails config) : Binary32 :=
  Portable.ln config.decay

structure Dimension where
  capacity : Nat
  positive : 0 < capacity
  powerOfTwo : ∃ exponent : Nat, capacity = 2 ^ exponent
  wordBound : capacity < 2 ^ 32

abbrev FeatIdx (dimension : Dimension) := Fin dimension.capacity

def FeatIdx.admit (dimension : Dimension) (word : UInt32) : Option (FeatIdx dimension) :=
  if h : word.toNat < dimension.capacity then some ⟨word.toNat, h⟩ else none

theorem feature_index_admit_exact (dimension : Dimension) (word : UInt32) (index : FeatIdx dimension)
    (h : FeatIdx.admit dimension word = some index) : index.val = word.toNat := by
  unfold FeatIdx.admit at h
  split at h
  · cases h
    rfl
  · contradiction

theorem feature_index_admit_refuses (dimension : Dimension) (word : UInt32) :
    FeatIdx.admit dimension word = none ↔ dimension.capacity ≤ word.toNat := by
  unfold FeatIdx.admit
  split <;> simp_all

def FeatIdx.fromHash (dimension : Dimension) (word : UInt64) : FeatIdx dimension :=
  let masked := word.toUInt32 &&& (dimension.capacity - 1).toUInt32
  ⟨masked.toNat, by
    have hsize : dimension.capacity - 1 < 2 ^ 32 := by
      have := dimension.wordBound
      omega
    change word.toUInt32.toNat &&& ((dimension.capacity - 1) % (2 ^ 32)) < dimension.capacity
    rw [Nat.mod_eq_of_lt hsize]
    have hmask : word.toUInt32.toNat &&& (dimension.capacity - 1) ≤ dimension.capacity - 1 :=
      Nat.and_le_right
    have := dimension.positive
    omega⟩

theorem feature_index_word_exact (dimension : Dimension) (index : FeatIdx dimension) :
    index.val.toUInt32.toNat = index.val := by
  change index.val % (2 ^ 32) = index.val
  exact Nat.mod_eq_of_lt (Nat.lt_trans index.isLt dimension.wordBound)

abbrev WeightArray (rule : ValueRule) (dimension : Dimension) :=
  Vector (Weight rule) dimension.capacity

def rewardRange : Interval32 where
  lower := .zero
  upper := ⟨0x3f800000⟩
  lowerFinite := by decide
  upperFinite := by decide
  ordered := by decide

abbrev RewardRate := Bounded32 rewardRange

def RewardRate.admit (raw : Binary32) : Option RewardRate := Bounded32.admit rewardRange raw

def RewardRate.project (raw : Binary32) : RewardRate := Bounded32.project rewardRange raw

structure TraceRegister where
  value : Binary32

structure MetaRegister where
  value : Binary32

structure TransientState (dimension : Dimension) where
  z : Vector TraceRegister dimension.capacity
  zDelta : Vector TraceRegister dimension.capacity
  zBar : Vector TraceRegister dimension.capacity
  lastAlpha : Vector TraceRegister dimension.capacity
  deltaWeight : Vector MetaRegister dimension.capacity
  h : Vector MetaRegister dimension.capacity
  hOld : Vector MetaRegister dimension.capacity
  hTemp : Vector MetaRegister dimension.capacity
  p : Vector MetaRegister dimension.capacity
  eligible : Array (FeatIdx dimension)
  vDelta : Binary32
  vOld : Binary32

def TransientState.zeroCosted (dimension : Dimension) : Costed (TransientState dimension) := do
  let trace ← Costed.replicate dimension.capacity (⟨.zero⟩ : TraceRegister)
  let gradient ← Costed.replicate dimension.capacity (⟨.zero⟩ : MetaRegister)
  Costed.op .zeroTransient
    { z := trace, zDelta := trace, zBar := trace, lastAlpha := trace, deltaWeight := gradient,
      h := gradient, hOld := gradient, hTemp := gradient, p := gradient, eligible := #[],
      vDelta := .zero, vOld := .zero }

def TransientState.zero (dimension : Dimension) : TransientState dimension :=
  (TransientState.zeroCosted dimension).val

theorem TransientState.zero_def (dimension : Dimension) :
    TransientState.zero dimension =
      { z := Vector.replicate _ ⟨.zero⟩
        zDelta := Vector.replicate _ ⟨.zero⟩
        zBar := Vector.replicate _ ⟨.zero⟩
        lastAlpha := Vector.replicate _ ⟨.zero⟩
        deltaWeight := Vector.replicate _ ⟨.zero⟩
        h := Vector.replicate _ ⟨.zero⟩
        hOld := Vector.replicate _ ⟨.zero⟩
        hTemp := Vector.replicate _ ⟨.zero⟩
        p := Vector.replicate _ ⟨.zero⟩
        eligible := #[]
        vDelta := .zero
        vOld := .zero } := rfl

structure NumericState (config : Config) (dimension : Dimension) where
  rails : StepSizeRails config
  weights : WeightArray config.rule dimension
  beta : Vector (LogStepSize rails) dimension.capacity
  alpha : Vector Binary32 dimension.capacity
  evaluated : LogStepSize.Evaluated beta alpha
  transient : TransientState dimension

def NumericState.initial (config : Config) (dimension : Dimension) : NumericState config dimension :=
  let rails := StepSizeRails.ofConfig config
  ⟨rails, Vector.replicate _ (Weight.project config.rule .zero),
    Vector.replicate _ rails.initial, Vector.replicate _ rails.initial.alpha,
    LogStepSize.Evaluated.replicate _ rails.initial, TransientState.zero dimension⟩

@[inline] def NumericState.stepSize {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension) : Binary32 :=
  state.alpha.get index

theorem NumericState.stepSize_eq {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension) :
    state.stepSize index = (state.beta.get index).alpha :=
  state.evaluated index.val index.isLt

def NumericState.writeWeight {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension) (raw : Binary32) :
    NumericState config dimension :=
  { state with weights := state.weights.set index.val (Weight.project config.rule raw) index.isLt }

def NumericState.writeBetaValue {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension)
    (value : LogStepSize state.rails) : NumericState config dimension :=
  { state with
    beta := state.beta.set index.val value index.isLt
    alpha := state.alpha.set index.val value.alpha index.isLt
    evaluated := state.evaluated.set index.val index.isLt value value.alpha rfl }

def NumericState.writeBeta {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension) (raw : Binary32) :
    NumericState config dimension :=
  state.writeBetaValue index (LogStepSize.project state.rails raw)

end Acorn
