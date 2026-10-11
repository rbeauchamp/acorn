/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Arithmetic
import Acorn.Constants
import Acorn.Portable

/-!
# Immutable numeric state domains

A value rule is a closed criterion, never an arbitrary caller-supplied bound.
Every weight is indexed by its rule, so replacing the criterion requires
re-admission of the stored words. The differential bound is a numerical budget
in the PAR-15 coordinate; it is not a bound on all true differential returns.
State projection and durable identity-or-refusal admission remain distinct.
-/

namespace Acorn

/-- The complete current discount domain. -/
inductive Discount where
  /-- Short prediction horizon. -/
  | g90
  /-- Medium prediction horizon. -/
  | g95
  /-- Long prediction horizon. -/
  | g99
  deriving DecidableEq

/-- Each discount selects its generated machine encoding. -/
def Discount.gamma : Discount → Binary32
  | .g90 => ⟨Acorn.Constants.gamma90Bits⟩
  | .g95 => ⟨Acorn.Constants.gamma95Bits⟩
  | .g99 => ⟨Acorn.Constants.gamma99Bits⟩

/-- The machine horizon is derived with the same two rounding boundaries as
the numeric owner; no caller can provide a wider replacement. -/
def Discount.horizon (discount : Discount) : Binary32 :=
  let one : Binary32 := ⟨0x3f800000⟩
  one.div (one.sub discount.gamma)

/-- The criterion and its bound are inseparable. -/
inductive ValueRule where
  /-- Discounted return with its selected horizon. -/
  | discounted (discount : Discount)
  /-- Differential approximation with the declared control numeric budget. -/
  | differential
  deriving DecidableEq

/-- Closed rule selection owns every stored weight bound. -/
def ValueRule.bound : ValueRule → Binary32
  | .discounted discount => discount.horizon
  | .differential => Discount.g99.horizon

/-- The bootstrap multiplier follows the criterion, independently of its bound. -/
def ValueRule.gamma : ValueRule → Binary32
  | .discounted discount => discount.gamma
  | .differential => ⟨0x3f800000⟩

/-- Finite ordered signed intervals are checked over the entire closed domain.
This small kernel reduction evaluates three primitive horizons, not an input
enumeration or a replay. Standard native Float replacements remain trusted. -/
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

/-- The rule determines the only interval under which its weights can exist. -/
def ValueRule.domain : ValueRule → Symmetric32
  | .discounted discount => discount.domain
  | .differential => Discount.g99.domain

/-- Weight storage carries its exact immutable criterion as a type index. -/
structure Weight (rule : ValueRule) where
  /-- The stored word and its closed receiver's legality witness. -/
  bounded : Bounded32 rule.domain.range

/-- Exact weight storage word, without a projection on observation. -/
def Weight.value {rule : ValueRule} (weight : Weight rule) : Binary32 := weight.bounded.value

/-- Legality belongs to storage under the nominal criterion. -/
theorem weight_legal {rule : ValueRule} (weight : Weight rule) :
    rule.domain.range.Contains weight.value := weight.bounded.legal

/-- Weight domain of the short discounted rule, evaluated once. -/
def ValueRule.domain90 : Symmetric32 := (ValueRule.discounted .g90).domain
/-- Weight domain of the medium discounted rule, evaluated once. -/
def ValueRule.domain95 : Symmetric32 := (ValueRule.discounted .g95).domain
/-- Weight domain of the long discounted rule, evaluated once. -/
def ValueRule.domain99 : Symmetric32 := (ValueRule.discounted .g99).domain
/-- Weight domain of the differential rule, evaluated once. -/
def ValueRule.domainDifferential : Symmetric32 := ValueRule.differential.domain

/-- All live weight writes pass through the closed criterion's projection. Each rule
reads its domain from a constant evaluated once, so a write evaluates no horizon and
builds no interval; `Weight.project_eq` equates this with the projection through
`rule.domain`. -/
def Weight.project : (rule : ValueRule) → Binary32 → Weight rule
  | .discounted .g90, raw => ⟨Bounded32.projectSymmetric ValueRule.domain90 raw⟩
  | .discounted .g95, raw => ⟨Bounded32.projectSymmetric ValueRule.domain95 raw⟩
  | .discounted .g99, raw => ⟨Bounded32.projectSymmetric ValueRule.domain99 raw⟩
  | .differential, raw => ⟨Bounded32.projectSymmetric ValueRule.domainDifferential raw⟩

/-- The projection of every rule and word is the projection through the rule's domain. -/
theorem Weight.project_eq (rule : ValueRule) (raw : Binary32) :
    Weight.project rule raw = ⟨Bounded32.projectSymmetric rule.domain raw⟩ := by
  cases rule with
  | discounted discount => cases discount <;> rfl
  | differential => rfl

/-- Projecting zero stores zero, under every rule. -/
theorem Weight.project_zero (rule : ValueRule) : (Weight.project rule .zero).value = .zero := by
  rw [Weight.project_eq]
  exact rule.domain.symmetric_project_identity _ rule.domain.zeroLegal

/-- Durable weights retain their original bits or are refused. -/
def Weight.admit (rule : ValueRule) (raw : Binary32) : Option (Weight rule) :=
  (Bounded32.admit rule.domain.range raw).map Weight.mk

/-- Durable weight admission preserves the exact word under its nominal rule. -/
theorem weight_admit_exact (rule : ValueRule) (raw : Binary32) (stored : Weight rule)
    (h : Weight.admit rule raw = some stored) : stored.value = raw := by
  unfold Weight.admit at h
  cases hb : Bounded32.admit rule.domain.range raw with
  | none => simp [hb] at h
  | some bounded =>
    simp only [hb, Option.map_some, Option.some.injEq] at h
    subst stored
    exact (Bounded32.admit_exact _ _ _ hb).1

/-- Weight admission refuses exactly the words outside the receiving rule. -/
theorem weight_admit_refuses (rule : ValueRule) (raw : Binary32) :
    Weight.admit rule raw = none ↔ ¬rule.domain.range.Contains raw := by
  simp [Weight.admit, Bounded32.admit_refuses]

/-- Differential values use exactly the declared differential coordinate. -/
abbrev DifferentialValue := Weight .differential

/-- Prediction storage uses its discount's finite nonnegative interval. -/
def Discount.predictionRange (discount : Discount) : Interval32 where
  lower := .zero
  upper := discount.horizon
  lowerFinite := by decide
  upperFinite := discount.domain.range.upperFinite
  ordered := discount.domain.zeroLegal.2.2

/-- A prediction is indexed by the discount owning its achieved-value range. -/
abbrev Prediction (discount : Discount) := Bounded32 discount.predictionRange

/-- Prediction projection preserves the exact nonnegative source branch order. -/
def Prediction.project (discount : Discount) (raw : Binary32) : Prediction discount :=
  Bounded32.project discount.predictionRange raw

/-- Durable prediction admission preserves the input word or refuses it. -/
def Prediction.admit (discount : Discount) (raw : Binary32) : Option (Prediction discount) :=
  Bounded32.admit discount.predictionRange raw

/-- The complete role domain supplying the current numerical configuration. -/
inductive Role where
  /-- Prediction learner. -/
  | demon
  /-- Primitive control learner. -/
  | control
  /-- Option-policy learner. -/
  | optionSkill
  deriving DecidableEq

/-- Configuration is only a role and criterion; all numeric fields derive from
them. No independent field can replace a budget after state admission. -/
structure Config where
  /-- Owner of role-dependent hyperparameters. -/
  role : Role
  /-- Owner of the bootstrap rule and weight coordinate. -/
  rule : ValueRule
  deriving DecidableEq

/-- Role-specific trace parameter, using generated source constants. -/
def Config.lambda (config : Config) : Binary32 :=
  match config.role with
  | .demon => ⟨Acorn.Constants.gamma95Bits⟩
  | .control | .optionSkill => ⟨Acorn.Constants.gamma90Bits⟩

/-- Role-specific initial step size. -/
def Config.alphaInitial (config : Config) : Binary32 :=
  match config.role with
  | .demon | .control => ⟨Acorn.Constants.alphaInit5e5Bits⟩
  | .optionSkill => ⟨Acorn.Constants.alphaInit1e4Bits⟩

/-- Role-specific step-size budget. -/
def Config.eta (config : Config) : Binary32 :=
  match config.role with
  | .demon | .control => ⟨Acorn.Constants.eta01Bits⟩
  | .optionSkill => ⟨Acorn.Constants.eta025Bits⟩

/-- The minimum rate is part of the closed configuration, not caller input. -/
def Config.etaMin (_config : Config) : Binary32 := ⟨Acorn.Constants.etaMin1e10Bits⟩

/-- Shared trace-pruning threshold. -/
def Config.epsilon (_config : Config) : Binary32 := ⟨Acorn.Constants.epsilon1e5Bits⟩

/-- Shared step-size decay, applied through portable logarithm. -/
def Config.decay (_config : Config) : Binary32 := ⟨Acorn.Constants.decay0999Bits⟩

/-- Role-dependent meta step size. -/
def Config.metaStep (config : Config) : Binary32 :=
  match config.role with
  | .demon | .control => ⟨Acorn.Constants.meta1e3Bits⟩
  | .optionSkill => ⟨Acorn.Constants.meta3e2Bits⟩

/-- An immutable pair of log-space rails derived from one configuration.
The equality fields bind every endpoint to the actual portable evaluation. -/
structure StepSizeRails (config : Config) where
  /-- Finite ordered receiver interval. -/
  range : Interval32
  /-- Lower endpoint owns the configuration's evaluated minimum. -/
  lowerIdentity : range.lower = Portable.ln config.etaMin
  /-- Upper endpoint owns its evaluated overshoot budget. -/
  upperIdentity : range.upper = Portable.ln config.eta

set_option maxRecDepth 8192 in
/-- Total rail construction exhausts the complete three-role domain in the
kernel. It evaluates only the finite closed configuration, not arbitrary
machine inputs, and uses the actual portable logarithm definitions. -/
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

/-- Rail admission checks the derived endpoints, never independently supplied
ones. Total construction is separately provided by `ofConfig`. -/
def StepSizeRails.admit (config : Config) : Option (StepSizeRails config) :=
  match h : Interval32.admit (Portable.ln config.etaMin) (Portable.ln config.eta) with
  | none => none
  | some range =>
    let identities := Interval32.interval_admit_exact _ _ range h
    some ⟨range, identities.1, identities.2⟩

/-- Every member of the closed configuration domain passes rail admission. -/
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

/-- A log step size cannot be installed under different rails without admission. -/
abbrev LogStepSize {config : Config} (rails : StepSizeRails config) := Bounded32 rails.range

/-- Every live log-step write saturates through its immutable receiver. -/
def LogStepSize.project {config : Config} (rails : StepSizeRails config) (raw : Binary32) :
    LogStepSize rails := Bounded32.project rails.range raw

/-- Durable log-step admission is identity or refusal. -/
def LogStepSize.admit {config : Config} (rails : StepSizeRails config) (raw : Binary32) :
    Option (LogStepSize rails) := Bounded32.admit rails.range raw

/-- Recovered alpha evaluates the actual portable recipe on the stored word. -/
def LogStepSize.alpha {config : Config} {rails : StepSizeRails config}
    (stored : LogStepSize rails) : Binary32 := Portable.exp stored.value

/-- The step size of `next`: the word `stored` when `next` holds the same word as
`previous`, whose step size `stored` is, and the portable evaluation otherwise.
An unchanged log step size therefore costs no evaluation. -/
def LogStepSize.alphaAfter {config : Config} {rails : StepSizeRails config}
    (previous : LogStepSize rails) (stored : Binary32) (next : LogStepSize rails) : Binary32 :=
  if next.value = previous.value then stored else next.alpha

/-- Reusing a step size for an unchanged word is evaluating it: the portable
exponential is a function of the stored word alone. This holds for every pair of
stored words, including both rails. -/
theorem LogStepSize.alphaAfter_eq {config : Config} {rails : StepSizeRails config}
    (previous : LogStepSize rails) (stored : Binary32) (next : LogStepSize rails)
    (evaluated : stored = previous.alpha) : previous.alphaAfter stored next = next.alpha := by
  subst evaluated
  unfold LogStepSize.alphaAfter
  split
  · rename_i same
    exact congrArg Portable.exp same.symm
  · rfl

/-- A step size reused beside its own log step size is the portable exponential of
the next one, whether or not the word changed. -/
theorem LogStepSize.alphaAfter_self {config : Config} {rails : StepSizeRails config}
    (previous next : LogStepSize rails) : previous.alphaAfter previous.alpha next = next.alpha :=
  previous.alphaAfter_eq previous.alpha next rfl

/-- Each stored step size is the portable exponential of the log step size stored
at the same index. A learner state carries this as a field, so a step size is read
without evaluation and no stored step size can differ from the one its log step
size evaluates to. -/
def LogStepSize.Evaluated {config : Config} {rails : StepSizeRails config} {capacity : Nat}
    (beta : Vector (LogStepSize rails) capacity) (alpha : Vector Binary32 capacity) : Prop :=
  ∀ (index : Nat) (inside : index < capacity), alpha[index] = beta[index].alpha

/-- Writing a log step size and its own step size at one index keeps every pair
evaluated; every other index keeps its pair. -/
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

/-- One log step size at every index beside its own step size is evaluated. -/
theorem LogStepSize.Evaluated.replicate {config : Config} {rails : StepSizeRails config}
    (capacity : Nat) (value : LogStepSize rails) :
    LogStepSize.Evaluated (Vector.replicate capacity value)
      (Vector.replicate capacity value.alpha) := by
  intro index inside
  rw [Vector.getElem_replicate, Vector.getElem_replicate]

/-- Evaluating every log step size gives evaluated step sizes. -/
theorem LogStepSize.Evaluated.map {config : Config} {rails : StepSizeRails config}
    {capacity : Nat} (beta : Vector (LogStepSize rails) capacity) :
    LogStepSize.Evaluated beta (beta.map fun stored => stored.alpha) := by
  intro index inside
  rw [Vector.getElem_map]

/-- The initial log step is projected through the same receiving interval. -/
def StepSizeRails.initial {config : Config} (rails : StepSizeRails config) :
    LogStepSize rails := LogStepSize.project rails (Portable.ln config.alphaInitial)

/-- The beta-space decrement is evaluated once from the immutable config. -/
def StepSizeRails.decay {config : Config} (_rails : StepSizeRails config) : Binary32 :=
  Portable.ln config.decay

/-- A dimension declaration prevents zero capacity and out-of-word indices. -/
structure Dimension where
  /-- Feature-space capacity. -/
  capacity : Nat
  /-- A nonempty feature space is required for index formation. -/
  positive : 0 < capacity
  /-- Hash masking is admitted only for a power-of-two feature space. -/
  powerOfTwo : ∃ exponent : Nat, capacity = 2 ^ exponent
  /-- Every admitted index has an exact UInt32 storage image. -/
  wordBound : capacity < 2 ^ 32

/-- An index cannot be used against a different dimension without re-admission. -/
abbrev FeatIdx (dimension : Dimension) := Fin dimension.capacity

/-- Durable feature-index admission is exact or refused before array access. -/
def FeatIdx.admit (dimension : Dimension) (word : UInt32) : Option (FeatIdx dimension) :=
  if h : word.toNat < dimension.capacity then some ⟨word.toNat, h⟩ else none

/-- Successful index admission preserves its original word value. -/
theorem feature_index_admit_exact (dimension : Dimension) (word : UInt32) (index : FeatIdx dimension)
    (h : FeatIdx.admit dimension word = some index) : index.val = word.toNat := by
  unfold FeatIdx.admit at h
  split at h
  · cases h
    rfl
  · contradiction

/-- Index admission refuses exactly the words at or beyond capacity. -/
theorem feature_index_admit_refuses (dimension : Dimension) (word : UInt32) :
    FeatIdx.admit dimension word = none ↔ dimension.capacity ≤ word.toNat := by
  unfold FeatIdx.admit
  split <;> simp_all

/-- Hash masking uses the receiving capacity itself. The universal bitwise
bound needs positivity; the separately stored power-of-two condition governs
coverage of the space, not this index-safety proof. -/
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

/-- An admitted feature index serializes to UInt32 without wrapping. -/
theorem feature_index_word_exact (dimension : Dimension) (index : FeatIdx dimension) :
    index.val.toUInt32.toNat = index.val := by
  change index.val % (2 ^ 32) = index.val
  exact Nat.mod_eq_of_lt (Nat.lt_trans index.isLt dimension.wordBound)

/-- Dimension-indexed storage makes array shape and element legality coexist. -/
abbrev WeightArray (rule : ValueRule) (dimension : Dimension) :=
  Vector (Weight rule) dimension.capacity

/-- The reward-rate interval is independent of the weight criterion. -/
def rewardRange : Interval32 where
  lower := .zero
  upper := ⟨0x3f800000⟩
  lowerFinite := by decide
  upperFinite := by decide
  ordered := by decide

/-- A host reward-rate value is finite and in [0,1] at storage. -/
abbrev RewardRate := Bounded32 rewardRange

/-- Durable reward-rate reconstruction is identity or refusal. -/
def RewardRate.admit (raw : Binary32) : Option RewardRate := Bounded32.admit rewardRange raw

/-- Reward-rate updates admit every raw result through the owning interval.
This is a storage guarantee, not a convergence theorem for an average. -/
def RewardRate.project (raw : Binary32) : RewardRate := Bounded32.project rewardRange raw

/-- Transient eligibility traces admit every binary32 encoding. Arbitrary raw
public update arguments do not establish a finite-value or magnitude invariant.
This representation makes that separate contract explicit. -/
structure TraceRegister where
  /-- Exact process-local trace word, including exceptional encodings. -/
  value : Binary32

/-- Meta-gradients have their own raw-word domain. Weight projection does not
bound these registers; a stronger claim requires the full update owner. -/
structure MetaRegister where
  /-- Exact process-local meta-gradient word. -/
  value : Binary32

/-- Each family preserves dimension even though its numeric domain is raw. -/
structure TransientState (dimension : Dimension) where
  /-- Eligibility trace z. -/
  z : Vector TraceRegister dimension.capacity
  /-- Trace increment. -/
  zDelta : Vector TraceRegister dimension.capacity
  /-- Dutch trace. -/
  zBar : Vector TraceRegister dimension.capacity
  /-- Last trace increment used by pruning. -/
  lastAlpha : Vector TraceRegister dimension.capacity
  /-- Per-weight update, kept separate from projected weight storage. -/
  deltaWeight : Vector MetaRegister dimension.capacity
  /-- Dutch-trace auxiliary. -/
  h : Vector MetaRegister dimension.capacity
  /-- Previous auxiliary. -/
  hOld : Vector MetaRegister dimension.capacity
  /-- Temporary auxiliary. -/
  hTemp : Vector MetaRegister dimension.capacity
  /-- Meta trace. -/
  p : Vector MetaRegister dimension.capacity
  /-- Each eligible index is valid; arbitrary independent loop calls do not
  justify a uniqueness or length-at-most-capacity claim. -/
  eligible : Array (FeatIdx dimension)
  /-- Ordered previous update accumulator. -/
  vDelta : Binary32
  /-- Previous prediction anchor. -/
  vOld : Binary32

/-- Fresh process-local registers with their work: one zero vector of each register type, which
every register vector of that type shares. The compiled code of one build was observed to build
one array, which all nine register vectors share once the register types are erased; the charge
of two vectors is a sound over-charge that the distinct register types force. -/
def TransientState.zeroCosted (dimension : Dimension) : Costed (TransientState dimension) := do
  let trace ← Costed.replicate dimension.capacity (⟨.zero⟩ : TraceRegister)
  let gradient ← Costed.replicate dimension.capacity (⟨.zero⟩ : MetaRegister)
  Costed.op .zeroTransient
    { z := trace, zDelta := trace, zBar := trace, lastAlpha := trace, deltaWeight := gradient,
      h := gradient, hOld := gradient, hTemp := gradient, p := gradient, eligible := #[],
      vDelta := .zero, vOld := .zero }

/-- Fresh process-local registers have exact zero words and no eligible entries. -/
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

/-- Numeric storage binds all knowledge to one configuration and dimension.
The complete learner transition is owned by the subsequent learner module. -/
structure NumericState (config : Config) (dimension : Dimension) where
  /-- Immutable beta-space rails derived from this configuration. -/
  rails : StepSizeRails config
  /-- Criterion-indexed weight storage. -/
  weights : WeightArray config.rule dimension
  /-- Log-step-size storage indexed by those same rails. -/
  beta : Vector (LogStepSize rails) dimension.capacity
  /-- The step size of each stored log step size, so a read evaluates nothing.
  It is a function of `beta` and holds no knowledge of its own. -/
  alpha : Vector Binary32 dimension.capacity
  /-- Every stored step size is the portable exponential of its log step size. -/
  evaluated : LogStepSize.Evaluated beta alpha
  /-- Dimension-preserving raw process-local state. -/
  transient : TransientState dimension

/-- Initialization calls the actual rail and state constructors. All array
elements carry the receiver's invariant before any learning loop is available. -/
def NumericState.initial (config : Config) (dimension : Dimension) : NumericState config dimension :=
  let rails := StepSizeRails.ofConfig config
  ⟨rails, Vector.replicate _ (Weight.project config.rule .zero),
    Vector.replicate _ rails.initial, Vector.replicate _ rails.initial.alpha,
    LogStepSize.Evaluated.replicate _ rails.initial, TransientState.zero dimension⟩

/-- The stored step size of one feature, read without evaluation. It is marked
`@[inline]` so that the compiled read is a field access, not a call that takes
the whole state; that is a performance choice and changes no value. -/
@[inline] def NumericState.stepSize {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension) : Binary32 :=
  state.alpha.get index

/-- A stored step size is the portable exponential of the stored log step size,
for every state of the type and every index. -/
theorem NumericState.stepSize_eq {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension) :
    state.stepSize index = (state.beta.get index).alpha :=
  state.evaluated index.val index.isLt

/-- A raw weight write cannot replace the configuration or bypass its projection. -/
def NumericState.writeWeight {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension) (raw : Binary32) :
    NumericState config dimension :=
  { state with weights := state.weights.set index.val (Weight.project config.rule raw) index.isLt }

/-- Install an already-legal log step size without a further projection, beside
its portable exponential: the listed write of one log step size. -/
def NumericState.writeBetaValue {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension)
    (value : LogStepSize state.rails) : NumericState config dimension :=
  { state with
    beta := state.beta.set index.val value index.isLt
    alpha := state.alpha.set index.val value.alpha index.isLt
    evaluated := state.evaluated.set index.val index.isLt value value.alpha rfl }

/-- A raw log-step write cannot switch rails or bypass saturation. -/
def NumericState.writeBeta {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension) (raw : Binary32) :
    NumericState config dimension :=
  state.writeBetaValue index (LogStepSize.project state.rails raw)

end Acorn
