import Acorn.Rng
import Acorn.State

namespace Acorn

namespace Binary32

def numericallyEqual (left right : Binary32) : Bool :=
  let lm := left.bits &&& 0x7fffffff
  let rm := right.bits &&& 0x7fffffff
  !left.isNaN && !right.isNaN &&
    ((lm == rm) && (left.negative == right.negative || lm == 0))

theorem numericallyEqual_eq_key (left right : Binary32) :
    left.numericallyEqual right = (!left.isNaN && !right.isNaN && decide (left.key = right.key)) := by
  unfold numericallyEqual
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  simp only [key_eq_negative]
  split <;> split <;> simp_all [magnitude, ← UInt32.toNat_inj] <;> omega

def lessOrEqual (left right : Binary32) : Bool :=
  !left.isNaN && !right.isNaN && !right.less left

theorem lessOrEqual_eq_key (left right : Binary32) :
    left.lessOrEqual right = (!left.isNaN && !right.isNaN && decide (left.key ≤ right.key)) := by
  by_cases hl : left.isNaN = true
  · simp [lessOrEqual, hl]
  by_cases hr : right.isNaN = true
  · simp [lessOrEqual, hr]
  have hlf : left.isNaN = false := Bool.eq_false_iff.mpr hl
  have hrf : right.isNaN = false := Bool.eq_false_iff.mpr hr
  by_cases h : left.key ≤ right.key
  · have hn : ¬right.key < left.key := by omega
    simp [lessOrEqual, less_eq_key, hlf, hrf, h, hn]
  · have hy : right.key < left.key := by omega
    simp [lessOrEqual, less_eq_key, hlf, hrf, h, hy]

def LessOrEqual (left right : Binary32) : Prop :=
  ¬left.IsNaN ∧ ¬right.IsNaN ∧ left.key ≤ right.key

theorem lessOrEqual_iff (left right : Binary32) :
    left.lessOrEqual right = true ↔ left.LessOrEqual right := by
  rw [lessOrEqual_eq_key]
  simp only [LessOrEqual, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, ← isNaN_iff,
    Bool.not_eq_true, and_assoc]

instance (left right : Binary32) : Decidable (left.LessOrEqual right) :=
  decidable_of_iff _ (lessOrEqual_iff left right)

def isZero (value : Binary32) : Bool := value.bits &&& 0x7fffffff == 0

theorem isZero_eq_key (value : Binary32) : value.isZero = decide (value.key = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [isZero, beq_iff_eq, decide_eq_true_eq, ← UInt32.toNat_inj]
  simp only [key_eq_negative]
  split <;> simp_all [magnitude] <;> omega

def abs (value : Binary32) : Binary32 := ⟨value.bits &&& 0x7fffffff⟩

def one : Binary32 := ⟨0x3f800000⟩

end Binary32

def SwiftTd.swapRemove {α : Type} (items : Array α) (pos : Nat) (inRange : pos < items.size) :
    Array α :=
  (items.set pos items[items.size - 1]).pop

structure SwiftTd.ActiveSet (dimension : Dimension) where
  indices : List (FeatIdx dimension)
  nodup : indices.Nodup

namespace SwiftTd

def ActiveSet.empty (dimension : Dimension) : ActiveSet dimension := ⟨[], List.nodup_nil⟩

variable {config : Config} {dimension : Dimension}

def exploreRange : Interval32 where
  lower := .zero
  upper := Binary32.one
  lowerFinite := by decide
  upperFinite := by decide
  ordered := by decide

abbrev ExploreRate := Bounded32 exploreRange

def ExploreRate.never : ExploreRate := Bounded32.project exploreRange .zero

def ExploreRate.project (raw : Binary32) : ExploreRate := Bounded32.project exploreRange raw

inductive ConsumerRate where
  | ownLearner
  | imposed (rate : ExploreRate)

def ConsumerRate.resolve (rate : ConsumerRate) (own : Unit → ExploreRate) : ExploreRate :=
  match rate with
  | .ownLearner => own ()
  | .imposed imposedRate => imposedRate

structure TdStep where
  value : Binary32
  error : Binary32

end SwiftTd

namespace NumericState

open SwiftTd (ActiveSet swapRemove TdStep)

variable {config : Config} {dimension : Dimension}

def writeZ (state : NumericState config dimension) (idx : FeatIdx dimension) (word : Binary32) :
    NumericState config dimension :=
  { state with transient := { state.transient with
      z := state.transient.z.set idx.val ⟨word⟩ idx.isLt } }

def writeZDelta (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      zDelta := state.transient.zDelta.set idx.val ⟨word⟩ idx.isLt } }

def writeZBar (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      zBar := state.transient.zBar.set idx.val ⟨word⟩ idx.isLt } }

def writeLastAlpha (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      lastAlpha := state.transient.lastAlpha.set idx.val ⟨word⟩ idx.isLt } }

def writeDeltaWeight (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      deltaWeight := state.transient.deltaWeight.set idx.val ⟨word⟩ idx.isLt } }

def writeH (state : NumericState config dimension) (idx : FeatIdx dimension) (word : Binary32) :
    NumericState config dimension :=
  { state with transient := { state.transient with
      h := state.transient.h.set idx.val ⟨word⟩ idx.isLt } }

def writeHOld (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      hOld := state.transient.hOld.set idx.val ⟨word⟩ idx.isLt } }

def writeHTemp (state : NumericState config dimension) (idx : FeatIdx dimension)
    (word : Binary32) : NumericState config dimension :=
  { state with transient := { state.transient with
      hTemp := state.transient.hTemp.set idx.val ⟨word⟩ idx.isLt } }

def writeP (state : NumericState config dimension) (idx : FeatIdx dimension) (word : Binary32) :
    NumericState config dimension :=
  { state with transient := { state.transient with
      p := state.transient.p.set idx.val ⟨word⟩ idx.isLt } }

theorem anchor_stepSize (state : NumericState config dimension) (idx : FeatIdx dimension)
    (clipped : Bool) :
    (if clipped then state.rails.initial.alpha else state.stepSize idx) =
      (if clipped then state.rails.initial else state.beta.get idx).alpha := by
  cases clipped
  · exact state.stepSize_eq idx
  · rfl

def clearFeatureRegisters (state : NumericState config dimension) (idx : FeatIdx dimension) :
    NumericState config dimension :=
  let state := state.writeZ idx .zero
  let state := state.writeP idx .zero
  let state := state.writeZBar idx .zero
  let state := state.writeDeltaWeight idx .zero
  let state := state.writeZDelta idx .zero
  let state := state.writeH idx .zero
  let state := state.writeHOld idx .zero
  let state := state.writeHTemp idx .zero
  state.writeLastAlpha idx .zero

def removeEligibleAt (state : NumericState config dimension) (pos : Nat)
    (inRange : pos < state.transient.eligible.size) : NumericState config dimension :=
  { state with transient := { state.transient with
      eligible := swapRemove state.transient.eligible pos inRange } }

def clearTransientCosted (state : NumericState config dimension) :
    Costed (NumericState config dimension) := do
  let zero ← TransientState.zeroCosted dimension
  Costed.pure { state with transient := zero }

def clearTransient (state : NumericState config dimension) : NumericState config dimension :=
  state.clearTransientCosted.val

theorem clearTransient_def (state : NumericState config dimension) :
    state.clearTransient = { state with transient := TransientState.zero dimension } := rfl

def releaseEligibleCosted (state : NumericState config dimension) :
    Costed (NumericState config dimension) := do
  let cleared ← Costed.foldlArray
    (fun next idx => Costed.op .clearRegisters (next.clearFeatureRegisters idx)) state
    state.transient.eligible
  Costed.op .releaseClose { cleared with transient := { cleared.transient with eligible := #[] } }

def releaseEligible (state : NumericState config dimension) : NumericState config dimension :=
  state.releaseEligibleCosted.val

theorem releaseEligible_def (state : NumericState config dimension) :
    state.releaseEligible =
      let cleared := state.transient.eligible.foldl
        (fun next idx => next.clearFeatureRegisters idx) state
      { cleared with transient := { cleared.transient with eligible := #[] } } := rfl

def linearPredictionCosted (state : NumericState config dimension)
    (features : ActiveSet dimension) : Costed Binary32 :=
  Binary32.sumMapCosted .sumTerm .zero features.indices fun idx =>
    Costed.pure (state.weights.get idx).value

def linearPrediction (state : NumericState config dimension) (features : ActiveSet dimension) :
    Binary32 :=
  (state.linearPredictionCosted features).val

theorem linearPrediction_def (state : NumericState config dimension)
    (features : ActiveSet dimension) :
    state.linearPrediction features =
      Binary32.sumMap .zero features.indices (fun idx => (state.weights.get idx).value) := rfl

theorem linearPrediction_eq_sumFrom (state : NumericState config dimension)
    (features : ActiveSet dimension) :
    state.linearPrediction features = Binary32.sumFrom .zero
      (features.indices.map fun idx => (state.weights.get idx).value) := by
  simp only [linearPrediction_def, Binary32.sumMap_eq]

def predictCosted (state : NumericState config dimension) (features : ActiveSet dimension) :
    Costed Binary32 :=
  state.linearPredictionCosted features

def predict (state : NumericState config dimension) (features : ActiveSet dimension) : Binary32 :=
  (state.predictCosted features).val

theorem predict_def (state : NumericState config dimension) (features : ActiveSet dimension) :
    state.predict features = state.linearPrediction features := rfl

def firstLoopElement (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta traceDecay : Binary32) : NumericState config dimension × Bool :=
  let dw := (delta.mul (state.transient.z.get idx).value).sub
    ((state.transient.zDelta.get idx).value.mul vDelta)
  let raw := (state.weights.get idx).value.add dw
  let weight := Weight.project config.rule raw
  let clipped := !(weight.value.numericallyEqual raw)
  let beta := if clipped then state.rails.initial else state.beta.get idx
  let alpha := if clipped then state.rails.initial.alpha else state.stepSize idx
  let p := if clipped then Binary32.zero else (state.transient.p.get idx).value
  let zBar := if clipped then Binary32.zero else (state.transient.zBar.get idx).value
  let h := if clipped then Binary32.zero else (state.transient.h.get idx).value
  let hTemp := if clipped then Binary32.zero else (state.transient.hTemp.get idx).value
  let stepped := beta.value.add
    (((config.metaStep.div alpha).mul (delta.sub vDelta)).mul p)
  let adapted := LogStepSize.project state.rails stepped
  let nextH := (hTemp.add (delta.mul zBar)).sub
    ((state.transient.zDelta.get idx).value.mul vDelta)
  let z := (state.transient.z.get idx).value.mul traceDecay
  let next : NumericState config dimension := {
    state with
    weights := state.weights.set idx.val weight idx.isLt
    beta := state.beta.set idx.val adapted idx.isLt
    alpha := state.alpha.set idx.val (beta.alphaAfter alpha adapted) idx.isLt
    evaluated := state.evaluated.set idx.val idx.isLt adapted (beta.alphaAfter alpha adapted)
      (beta.alphaAfter_eq alpha adapted (state.anchor_stepSize idx clipped))
    transient := {
      state.transient with
      z := state.transient.z.set idx.val ⟨z⟩ idx.isLt
      zDelta := state.transient.zDelta.set idx.val ⟨.zero⟩ idx.isLt
      zBar := state.transient.zBar.set idx.val ⟨zBar.mul traceDecay⟩ idx.isLt
      p := state.transient.p.set idx.val ⟨p.mul traceDecay⟩ idx.isLt
      hOld := state.transient.hOld.set idx.val ⟨h⟩ idx.isLt
      h := state.transient.h.set idx.val ⟨hTemp⟩ idx.isLt
      hTemp := state.transient.hTemp.set idx.val ⟨nextH⟩ idx.isLt
      deltaWeight := state.transient.deltaWeight.set idx.val
        ⟨if clipped then .zero else dw⟩ idx.isLt } }
  (next, z.lessOrEqual ((state.transient.lastAlpha.get idx).value.mul config.epsilon))

theorem firstLoopElement_eq (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta traceDecay : Binary32) :
    state.firstLoopElement idx delta vDelta traceDecay =
      let dw := (delta.mul (state.transient.z.get idx).value).sub
        ((state.transient.zDelta.get idx).value.mul vDelta)
      let raw := (state.weights.get idx).value.add dw
      let weight := Weight.project config.rule raw
      let clipped := !(weight.value.numericallyEqual raw)
      let beta := if clipped then state.rails.initial else state.beta.get idx
      let p := if clipped then Binary32.zero else (state.transient.p.get idx).value
      let zBar := if clipped then Binary32.zero else (state.transient.zBar.get idx).value
      let h := if clipped then Binary32.zero else (state.transient.h.get idx).value
      let hTemp := if clipped then Binary32.zero else (state.transient.hTemp.get idx).value
      let stepped := beta.value.add
        (((config.metaStep.div beta.alpha).mul (delta.sub vDelta)).mul p)
      let nextH := (hTemp.add (delta.mul zBar)).sub
        ((state.transient.zDelta.get idx).value.mul vDelta)
      let z := (state.transient.z.get idx).value.mul traceDecay
      let next : NumericState config dimension := {
        state with
        weights := state.weights.set idx.val weight idx.isLt
        transient := {
          state.transient with
          z := state.transient.z.set idx.val ⟨z⟩ idx.isLt
          zDelta := state.transient.zDelta.set idx.val ⟨.zero⟩ idx.isLt
          zBar := state.transient.zBar.set idx.val ⟨zBar.mul traceDecay⟩ idx.isLt
          p := state.transient.p.set idx.val ⟨p.mul traceDecay⟩ idx.isLt
          hOld := state.transient.hOld.set idx.val ⟨h⟩ idx.isLt
          h := state.transient.h.set idx.val ⟨hTemp⟩ idx.isLt
          hTemp := state.transient.hTemp.set idx.val ⟨nextH⟩ idx.isLt
          deltaWeight := state.transient.deltaWeight.set idx.val
            ⟨if clipped then .zero else dw⟩ idx.isLt } }
      (next.writeBetaValue idx (LogStepSize.project state.rails stepped),
        z.lessOrEqual ((state.transient.lastAlpha.get idx).value.mul config.epsilon)) := by
  simp only [firstLoopElement, anchor_stepSize, LogStepSize.alphaAfter_self, writeBetaValue]

def learnFirstLoopGoCosted (config : Config) (delta vDelta traceDecay : Binary32) :
    NumericState config dimension → Array (FeatIdx dimension) → Nat →
      Costed (NumericState config dimension)
  | state, work, pos =>
    if inRange : pos < work.size then
      let idx := work[pos]
      let (state, prune) := state.firstLoopElement idx delta vDelta traceDecay
      if prune then
        Costed.charge .visit <| Costed.charge .firstElement <| Costed.charge .prune <|
          learnFirstLoopGoCosted config delta vDelta traceDecay (state.clearFeatureRegisters idx)
            (swapRemove work pos inRange) pos
      else
        Costed.charge .visit <| Costed.charge .firstElement <|
          learnFirstLoopGoCosted config delta vDelta traceDecay state work (pos + 1)
    else
      Costed.charge .visit <|
        Costed.op .firstClose { state with transient := { state.transient with eligible := work } }
  termination_by _state work pos => work.size - pos
  decreasing_by
    · simp only [swapRemove, Array.size_pop, Array.size_set]
      omega
    · omega

def learnFirstLoopGo (config : Config) (delta vDelta traceDecay : Binary32)
    (state : NumericState config dimension) (work : Array (FeatIdx dimension)) (pos : Nat) :
    NumericState config dimension :=
  (learnFirstLoopGoCosted config delta vDelta traceDecay state work pos).val

theorem learnFirstLoopGo_def (config : Config) (delta vDelta traceDecay : Binary32)
    (state : NumericState config dimension) (work : Array (FeatIdx dimension)) (pos : Nat) :
    learnFirstLoopGo config delta vDelta traceDecay state work pos =
      if inRange : pos < work.size then
        let idx := work[pos]
        let (state, prune) := state.firstLoopElement idx delta vDelta traceDecay
        if prune then
          learnFirstLoopGo config delta vDelta traceDecay (state.clearFeatureRegisters idx)
            (swapRemove work pos inRange) pos
        else learnFirstLoopGo config delta vDelta traceDecay state work (pos + 1)
      else { state with transient := { state.transient with eligible := work } } := by
  unfold learnFirstLoopGo
  rw [learnFirstLoopGoCosted]
  split
  · dsimp only
    split <;> rfl
  · rfl

def learnFirstLoopCosted (config : Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) : Costed (NumericState config dimension) :=
  let work := state.transient.eligible
  let state := { state with transient := { state.transient with eligible := #[] } }
  Costed.charge .firstOpen (learnFirstLoopGoCosted config delta vDelta traceDecay state work 0)

def learnFirstLoop (config : Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) : NumericState config dimension :=
  (state.learnFirstLoopCosted config delta vDelta traceDecay).val

theorem learnFirstLoop_def (config : Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) :
    state.learnFirstLoop config delta vDelta traceDecay =
      let work := state.transient.eligible
      let state := { state with transient := { state.transient with eligible := #[] } }
      learnFirstLoopGo config delta vDelta traceDecay state work 0 := rfl

def secondLoopElementAt (overshoot : Bool) (scale oneSubT alpha : Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) (idx : FeatIdx dimension) :
    NumericState config dimension × Binary32 :=
  let eligible := if (state.transient.z.get idx).value.isZero then
    state.transient.eligible.push idx else state.transient.eligible
  let vDelta := vDelta.add (state.transient.deltaWeight.get idx).value
  let zd := scale.mul alpha
  let z := (state.transient.z.get idx).value.add (zd.mul oneSubT)
  let p := (state.transient.p.get idx).value.add (state.transient.h.get idx).value
  let zBar := (state.transient.zBar.get idx).value.add
    (zd.mul (oneSubT.sub (state.transient.zBar.get idx).value))
  let hTemp := (((state.transient.hTemp.get idx).value.sub
    ((state.transient.hOld.get idx).value.mul (z.sub zd))).sub
      ((state.transient.h.get idx).value.mul zd))
  let h := if overshoot then state.transient.h.set idx.val ⟨.zero⟩ idx.isLt else state.transient.h
  let next : NumericState config dimension := {
    state with
    transient := {
      state.transient with
      eligible := eligible
      z := state.transient.z.set idx.val ⟨z⟩ idx.isLt
      zDelta := state.transient.zDelta.set idx.val ⟨zd⟩ idx.isLt
      lastAlpha := state.transient.lastAlpha.set idx.val ⟨zd⟩ idx.isLt
      p := state.transient.p.set idx.val ⟨p⟩ idx.isLt
      zBar := state.transient.zBar.set idx.val ⟨if overshoot then .zero else zBar⟩ idx.isLt
      hTemp := state.transient.hTemp.set idx.val ⟨if overshoot then .zero else hTemp⟩ idx.isLt
      h := h } }
  (match overshoot with
    | true => next.writeBetaValue idx
        (LogStepSize.project next.rails ((next.beta.get idx).value.add next.rails.decay))
    | false => next, vDelta)

def secondLoopElement (config : Config) (overshoot : Bool) (e t : Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) (idx : FeatIdx dimension) :
    NumericState config dimension × Binary32 :=
  secondLoopElementAt overshoot (config.eta.div e) (Binary32.one.sub t)
    (state.beta.get idx).alpha state vDelta idx

theorem secondLoopElementAt_alpha (overshoot : Bool) (scale oneSubT alpha : Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) (idx other : FeatIdx dimension)
    (different : idx ≠ other) :
    ((secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx).1.beta.get other).alpha =
      (state.beta.get other).alpha := by
  have distinct : idx.val ≠ other.val := fun same => different (Fin.ext same)
  have read : ∀ {α : Type} (values : Vector α dimension.capacity),
      values.get other = values[other.val] := fun _ => rfl
  unfold LogStepSize.alpha
  congr 1
  cases overshoot
  · rfl
  · simp only [secondLoopElementAt, writeBetaValue, read,
      Vector.getElem_set, distinct, ite_false]

theorem stepSizes_eq (state : NumericState config dimension)
    (indices : List (FeatIdx dimension)) :
    indices.map state.stepSize = indices.map fun idx => (state.beta.get idx).alpha :=
  List.map_congr_left fun idx _ => state.stepSize_eq idx

def learnSecondLoopGoCosted (overshoot : Bool) (scale oneSubT : Binary32) :
    List (FeatIdx dimension) → List Binary32 → NumericState config dimension → Binary32 →
      Costed (NumericState config dimension × Binary32)
  | idx :: indices, alpha :: alphas, state, vDelta =>
    let next := secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx
    Costed.charge .visit <| Costed.charge .secondElement <|
      learnSecondLoopGoCosted overshoot scale oneSubT indices alphas next.1 next.2
  | _, _, state, vDelta => Costed.op .visit (state, vDelta)

def learnSecondLoopGo (overshoot : Bool) (scale oneSubT : Binary32)
    (indices : List (FeatIdx dimension)) (alphas : List Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) :
    NumericState config dimension × Binary32 :=
  (learnSecondLoopGoCosted overshoot scale oneSubT indices alphas state vDelta).val

theorem learnSecondLoopGo_def (overshoot : Bool) (scale oneSubT : Binary32)
    (indices : List (FeatIdx dimension)) (alphas : List Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) :
    learnSecondLoopGo overshoot scale oneSubT indices alphas state vDelta =
      match indices, alphas, state, vDelta with
      | idx :: indices, alpha :: alphas, state, vDelta =>
        let next := secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx
        learnSecondLoopGo overshoot scale oneSubT indices alphas next.1 next.2
      | _, _, state, vDelta => (state, vDelta) := by
  cases indices <;> cases alphas <;> rfl

theorem learnSecondLoopGo_eq_foldl (config : Config) (overshoot : Bool) (e t : Binary32)
    (indices : List (FeatIdx dimension)) (unique : indices.Nodup)
    (state : NumericState config dimension) (vDelta : Binary32) :
    learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) indices
        (indices.map fun idx => (state.beta.get idx).alpha) state vDelta =
      indices.foldl
        (fun (state, vDelta) idx => secondLoopElement config overshoot e t state vDelta idx)
        (state, vDelta) := by
  induction indices generalizing state vDelta with
  | nil => rfl
  | cons idx rest ih =>
    have fresh := (List.nodup_cons.mp unique).1
    have restUnique := (List.nodup_cons.mp unique).2
    let next := secondLoopElement config overshoot e t state vDelta idx
    have same : (rest.map fun other => (state.beta.get other).alpha) =
        rest.map fun other => (next.1.beta.get other).alpha := by
      apply List.map_congr_left
      intro other member
      exact (secondLoopElementAt_alpha overshoot _ _ _ state vDelta idx other
        (fun equal => fresh (equal ▸ member))).symm
    calc learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) (idx :: rest)
          ((idx :: rest).map fun other => (state.beta.get other).alpha) state vDelta
        = learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) rest
            (rest.map fun other => (state.beta.get other).alpha) next.1 next.2 := rfl
      _ = learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) rest
            (rest.map fun other => (next.1.beta.get other).alpha) next.1 next.2 := by rw [same]
      _ = rest.foldl
            (fun (state, vDelta) idx => secondLoopElement config overshoot e t state vDelta idx)
            (next.1, next.2) := ih restUnique next.1 next.2
      _ = (idx :: rest).foldl
            (fun (state, vDelta) idx => secondLoopElement config overshoot e t state vDelta idx)
            (state, vDelta) := rfl

def learnSecondLoopCosted (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    Costed (NumericState config dimension × Binary32) := do
  let alphas ← Costed.map (fun idx => Costed.op .read (state.stepSize idx)) features.indices
  let rate ← Binary32.sumFromCosted .zero alphas
  let overshoot := config.eta.less rate
  let e := if overshoot then rate else config.eta
  let t ← Binary32.sumMapCosted .sumTerm .zero features.indices
    (fun idx => Costed.pure (state.transient.z.get idx).value)
  Costed.charge .secondOpen <| learnSecondLoopGoCosted overshoot (config.eta.div e)
    (Binary32.one.sub t) features.indices alphas state vDelta

def learnSecondLoop (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    NumericState config dimension × Binary32 :=
  (state.learnSecondLoopCosted config features vDelta).val

theorem learnSecondLoop_def (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    state.learnSecondLoop config features vDelta =
      let alphas := features.indices.map state.stepSize
      let rate := Binary32.sumFrom .zero alphas
      let overshoot := config.eta.less rate
      let e := if overshoot then rate else config.eta
      let t := Binary32.sumMap .zero features.indices
        (fun idx => (state.transient.z.get idx).value)
      learnSecondLoopGo overshoot (config.eta.div e) (Binary32.one.sub t) features.indices alphas
        state vDelta := rfl

theorem learnSecondLoop_eq_sumFrom (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    learnSecondLoop config state features vDelta =
      let rate := Binary32.sumFrom .zero
        (features.indices.map fun idx => (state.beta.get idx).alpha)
      let overshoot := config.eta.less rate
      let e := if overshoot then rate else config.eta
      let t := Binary32.sumFrom .zero
        (features.indices.map fun idx => (state.transient.z.get idx).value)
      features.indices.foldl
        (fun (state, vDelta) idx => secondLoopElement config overshoot e t state vDelta idx)
        (state, vDelta) := by
  simp only [learnSecondLoop_def, Binary32.sumMap_eq, stepSizes_eq]
  exact learnSecondLoopGo_eq_foldl config _ _ _ features.indices features.nodup state vDelta

def stepCosted (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (reward : Binary32) :
    Costed (NumericState config dimension × TdStep) := do
  let v ← state.linearPredictionCosted features
  let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
  let state ← state.learnFirstLoopCosted config delta state.transient.vDelta
    (config.rule.gamma.mul config.lambda)
  let (state, vd) ← state.learnSecondLoopCosted config features .zero
  Costed.op .stepClose
    ({ state with transient := { state.transient with vDelta := vd, vOld := v } }, ⟨v, delta⟩)

def step (config : Config) (state : NumericState config dimension) (features : ActiveSet dimension)
    (reward : Binary32) : NumericState config dimension × TdStep :=
  (state.stepCosted config features reward).val

theorem step_def (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (reward : Binary32) :
    state.step config features reward =
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      let state := state.learnFirstLoop config delta state.transient.vDelta
        (config.rule.gamma.mul config.lambda)
      let (state, vd) := state.learnSecondLoop config features .zero
      let state := { state with transient := { state.transient with vDelta := vd, vOld := v } }
      (state, ⟨v, delta⟩) := rfl

def beginTrajectoryCosted (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) : Costed (NumericState config dimension) := do
  let state ← state.clearTransientCosted
  let v ← state.predictCosted features
  let (state, vd) ← state.learnSecondLoopCosted config features .zero
  Costed.op .beginClose { state with transient := { state.transient with vOld := v, vDelta := vd } }

def beginTrajectory (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) : NumericState config dimension :=
  (state.beginTrajectoryCosted config features).val

theorem beginTrajectory_def (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) :
    state.beginTrajectory config features =
      let state := state.clearTransient
      let v := state.predict features
      let (state, vd) := state.learnSecondLoop config features .zero
      { state with transient := { state.transient with vOld := v, vDelta := vd } } := rfl

def terminalStepCosted (config : Config) (state : NumericState config dimension)
    (target : Binary32) : Costed (NumericState config dimension × Binary32) := do
  let delta := target.sub state.transient.vOld
  let state ← state.learnFirstLoopCosted config delta state.transient.vDelta
    (config.rule.gamma.mul config.lambda)
  let cleared ← state.clearTransientCosted
  Costed.op .terminalClose (cleared, delta)

def terminalStep (config : Config) (state : NumericState config dimension) (target : Binary32) :
    NumericState config dimension × Binary32 :=
  (state.terminalStepCosted config target).val

theorem terminalStep_def (config : Config) (state : NumericState config dimension)
    (target : Binary32) :
    state.terminalStep config target =
      let delta := target.sub state.transient.vOld
      let state := state.learnFirstLoop config delta state.transient.vDelta
        (config.rule.gamma.mul config.lambda)
      (state.clearTransient, delta) := rfl

def planWeightsGoCosted (scale delta : Binary32) :
    List (FeatIdx dimension) → List Binary32 → NumericState config dimension →
      Costed (NumericState config dimension)
  | idx :: indices, alpha :: alphas, state =>
    Costed.charge .visit <| Costed.charge .planElement <| planWeightsGoCosted scale delta indices
      alphas
      (state.writeWeight idx ((state.weights.get idx).value.add ((scale.mul alpha).mul delta)))
  | _, _, state => Costed.op .visit state

def planWeightsGo (scale delta : Binary32) (indices : List (FeatIdx dimension))
    (alphas : List Binary32) (state : NumericState config dimension) :
    NumericState config dimension :=
  (planWeightsGoCosted scale delta indices alphas state).val

theorem planWeightsGo_def (scale delta : Binary32) (indices : List (FeatIdx dimension))
    (alphas : List Binary32) (state : NumericState config dimension) :
    planWeightsGo scale delta indices alphas state =
      match indices, alphas, state with
      | idx :: indices, alpha :: alphas, state =>
        planWeightsGo scale delta indices alphas
          (state.writeWeight idx ((state.weights.get idx).value.add ((scale.mul alpha).mul delta)))
      | _, _, state => state := by
  cases indices <;> cases alphas <;> rfl

theorem planWeightsGo_eq_foldl (scale delta : Binary32) (indices : List (FeatIdx dimension))
    (state : NumericState config dimension) :
    planWeightsGo scale delta indices (indices.map fun idx => (state.beta.get idx).alpha) state =
      indices.foldl (fun state idx =>
        let stepSize := (scale.mul (state.beta.get idx).alpha).mul delta
        state.writeWeight idx ((state.weights.get idx).value.add stepSize)) state := by
  induction indices generalizing state with
  | nil => rfl
  | cons idx rest ih =>
    exact ih (state.writeWeight idx
      ((state.weights.get idx).value.add ((scale.mul (state.beta.get idx).alpha).mul delta)))

def planStepCosted (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    Costed (NumericState config dimension × Binary32) := do
  let v ← state.predictCosted features
  let delta := target.sub v
  if !decide delta.Finite || delta.numericallyEqual .zero then Costed.op .planOpen (state, .zero)
  else
    let alphas ← Costed.map (fun idx => Costed.op .read (state.stepSize idx)) features.indices
    let rate ← Binary32.sumFromCosted .zero alphas
    let e := if config.eta.less rate then rate else config.eta
    let next ← planWeightsGoCosted (config.eta.div e) delta features.indices alphas state
    Costed.op .planOpen (next, delta)

def planStep (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    NumericState config dimension × Binary32 :=
  (state.planStepCosted config features target).val

theorem planStep_def (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    state.planStep config features target =
      let v := state.predict features
      let delta := target.sub v
      if !decide delta.Finite || delta.numericallyEqual .zero then (state, .zero)
      else
        let alphas := features.indices.map state.stepSize
        let rate := Binary32.sumFrom .zero alphas
        let e := if config.eta.less rate then rate else config.eta
        (planWeightsGo (config.eta.div e) delta features.indices alphas state, delta) := by
  unfold planStep planStepCosted predict
  rw [Costed.bind_val]
  dsimp only
  split <;> rfl

theorem planStep_eq_foldl (config : Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    state.planStep config features target =
      let v := state.predict features
      let delta := target.sub v
      if !decide delta.Finite || delta.numericallyEqual .zero then (state, .zero)
      else
        let rate := Binary32.sumFrom .zero
          (features.indices.map fun idx => (state.beta.get idx).alpha)
        let e := if config.eta.less rate then rate else config.eta
        let scale := config.eta.div e
        let state := features.indices.foldl (fun state idx =>
          let stepSize := (scale.mul (state.beta.get idx).alpha).mul delta
          state.writeWeight idx ((state.weights.get idx).value.add stepSize)) state
        (state, delta) := by
  simp only [planStep_def, stepSizes_eq, planWeightsGo_eq_foldl]

def retireIndexCosted (state : NumericState config dimension) (idx : FeatIdx dimension) :
    Costed (NumericState config dimension) :=
  Costed.bind (Costed.findIdx? state.transient.eligible
    fun entry => Costed.op .compare (entry == idx)) fun found =>
    Costed.op .retire <|
      let state := match same : found.val with
        | some pos => state.removeEligibleAt pos
          (Array.findIdx?_eq_some_iff_getElem.mp (found.property.trans same)).1
        | none => state
      let state := state.clearFeatureRegisters idx
      let state := state.writeWeight idx .zero
      state.writeBetaValue idx state.rails.initial

def retireIndex (state : NumericState config dimension) (idx : FeatIdx dimension) :
    NumericState config dimension :=
  (state.retireIndexCosted idx).val

theorem retireIndex_def (state : NumericState config dimension) (idx : FeatIdx dimension) :
    state.retireIndex idx =
      let state := match found : state.transient.eligible.findIdx? (· == idx) with
        | some pos =>
          state.removeEligibleAt pos (Array.findIdx?_eq_some_iff_getElem.mp found).1
        | none => state
      let state := state.clearFeatureRegisters idx
      let state := state.writeWeight idx .zero
      state.writeBetaValue idx state.rails.initial := rfl

def meanAlpha (state : NumericState config dimension) : Binary32 :=
  (Binary32.sumFrom .zero (state.beta.toList.map (·.alpha))).div
    (Binary32.ofUInt64 dimension.capacity.toUInt64)

def activeAlpha (state : NumericState config dimension) : Binary32 :=
  if state.transient.eligible.isEmpty then .zero
  else
    (Binary32.sumFrom .zero
      (state.transient.eligible.toList.map fun idx => (state.beta.get idx).alpha)).div
      (Binary32.ofUInt64 state.transient.eligible.size.toUInt64)

def normalizedStepSizeSumCosted (state : NumericState config dimension) :
    Costed (Binary32 × Nat) :=
  if state.transient.eligible.isEmpty then Costed.op .normalizedOpen (.zero, 0)
  else do
    let lo := state.rails.range.lower
    let span := state.rails.range.upper.sub lo
    let initial := Binary32.zero
    let entries ← Costed.arrayToList state.transient.eligible
    let terms ← Costed.map (fun idx => Costed.op .normalizedTerm
      (((state.beta.get idx).value.sub lo).div span)) entries
    let total ← Binary32.sumFromCosted initial terms
    Costed.op .normalizedOpen (total, state.transient.eligible.size)

def normalizedStepSizeSum (state : NumericState config dimension) : Binary32 × Nat :=
  state.normalizedStepSizeSumCosted.val

theorem normalizedStepSizeSum_def (state : NumericState config dimension) :
    state.normalizedStepSizeSum =
      if state.transient.eligible.isEmpty then (.zero, 0)
      else
        let lo := state.rails.range.lower
        let span := state.rails.range.upper.sub lo
        (Binary32.sumFrom .zero (state.transient.eligible.toList.map fun idx =>
          ((state.beta.get idx).value.sub lo).div span), state.transient.eligible.size) := by
  unfold normalizedStepSizeSum normalizedStepSizeSumCosted
  split <;> rfl

def initialNormalizedStepSize (config : Config) (state : NumericState config dimension) :
    Binary32 :=
  let lo := state.rails.range.lower
  let span := state.rails.range.upper.sub lo
  ((Portable.ln config.alphaInitial).sub lo).div span

def eligibleCount (state : NumericState config dimension) : Nat := state.transient.eligible.size

def checksumMultiplier : UInt64 := 0x00000100000001b3

def checksumRotate (word : UInt64) : UInt64 := (word <<< 13) ||| (word >>> 51)

def stateChecksum (state : NumericState config dimension) : UInt64 :=
  (state.weights.zip state.beta).foldl (fun hash (weight, beta) =>
    checksumRotate (((hash ^^^ weight.value.bits.toUInt64) * checksumMultiplier) ^^^
      beta.value.bits.toUInt64)) Acorn.Rng.fnvOffset

end NumericState

namespace SwiftTd

variable {config : Config} {dimension : Dimension}

inductive Entry (dimension : Dimension) where
  | first (delta vDelta decay : Binary32)
  | second (features : ActiveSet dimension) (vDelta : Binary32)
  | step (features : ActiveSet dimension) (reward : Binary32)
  | beginTrajectory (features : ActiveSet dimension)
  | terminal (target : Binary32)
  | plan (features : ActiveSet dimension) (target : Binary32)
  | retire (idx : FeatIdx dimension)
  | clear
  | release

def Entry.applyCosted (entry : Entry dimension) (state : NumericState config dimension) :
    Costed (NumericState config dimension) :=
  match entry with
  | .first delta vDelta decay => state.learnFirstLoopCosted config delta vDelta decay
  | .second features vDelta => do
    let result ← state.learnSecondLoopCosted config features vDelta
    Costed.pure result.1
  | .step features reward => do
    let result ← state.stepCosted config features reward
    Costed.pure result.1
  | .beginTrajectory features => state.beginTrajectoryCosted config features
  | .terminal target => do
    let result ← state.terminalStepCosted config target
    Costed.pure result.1
  | .plan features target => do
    let result ← state.planStepCosted config features target
    Costed.pure result.1
  | .retire idx => state.retireIndexCosted idx
  | .clear => state.clearTransientCosted
  | .release => state.releaseEligibleCosted

def Entry.apply (entry : Entry dimension) (state : NumericState config dimension) :
    NumericState config dimension :=
  (entry.applyCosted state).val

theorem Entry.apply_def (entry : Entry dimension) (state : NumericState config dimension) :
    entry.apply state =
      match entry with
      | .first delta vDelta decay => state.learnFirstLoop config delta vDelta decay
      | .second features vDelta => (state.learnSecondLoop config features vDelta).1
      | .step features reward => (state.step config features reward).1
      | .beginTrajectory features => state.beginTrajectory config features
      | .terminal target => (state.terminalStep config target).1
      | .plan features target => (state.planStep config features target).1
      | .retire idx => state.retireIndex idx
      | .clear => state.clearTransient
      | .release => state.releaseEligible := by
  cases entry <;> rfl

theorem Entry.apply_plan (features : ActiveSet dimension) (target : Binary32)
    (state : NumericState config dimension) :
    (Entry.plan features target).apply state = (state.planStep config features target).1 := rfl

def nextReady (entry : Entry dimension) (before : Bool) : Bool :=
  match entry with
  | .first .. | .terminal .. | .clear | .release => true
  | .second .. | .step .. | .beginTrajectory .. => false
  | .plan .. | .retire .. => before

@[reducible] def Permitted (entry : Entry dimension) (ready : Bool) : Prop :=
  match entry with
  | .second .. => ready = true
  | _ => True

inductive Admitted (config : Config) (dimension : Dimension) : NumericState config dimension → Prop
  | initial : Admitted config dimension (NumericState.initial config dimension)
  | transition {state : NumericState config dimension} (entry : Entry dimension)
      (before : Admitted config dimension state) : Admitted config dimension (entry.apply state)

abbrev Learner (config : Config) (dimension : Dimension) :=
  { state : NumericState config dimension // Admitted config dimension state }

def Learner.initial (config : Config) (dimension : Dimension) : Learner config dimension :=
  ⟨NumericState.initial config dimension, .initial⟩

def Learner.apply (learner : Learner config dimension) (entry : Entry dimension) :
    Learner config dimension := ⟨entry.apply learner.val, .transition entry learner.property⟩

end SwiftTd

end Acorn
