import Acorn.FeatureConstants
import Acorn.SwiftTd
import AcornVerif.CurrentCreditHorizon
import AcornVerif.CurrentLearnerStep
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace AcornVerif.CurrentMetaGradient

open Acorn Acorn.SwiftTd
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentPrediction
open AcornVerif.CurrentLearner AcornVerif.CurrentLearnerStep AcornVerif.CurrentCreditHorizon
open AcornVerif.CurrentBackupBounds AcornVerif.CurrentPreReward

def ulpHalf (limit : Int) : ℚ :=
  (2 : ℚ) ^ (max (limit - 24) (-149)) / 2

def wordNear (word : Binary32) (center radius : ℚ) : Prop :=
  word.Finite ∧ |numerical32 word - center| ≤ radius

theorem ulpHalf_nonneg (limit : Int) : 0 ≤ ulpHalf limit := by
  unfold ulpHalf
  positivity

theorem wordNear_add {a b : Binary32} {ca cb ra rb : ℚ} {limit : Int}
    (ha : wordNear a ca ra) (hb : wordNear b cb rb) (hLim : limit ≤ 33)
    (hCap : |ca + cb| + ra + rb < (2 : ℚ) ^ limit) :
    wordNear (a.add b) (ca + cb) (ra + rb + ulpHalf limit) := by
  have hSum : |numerical32 a + numerical32 b| < (2 : ℚ) ^ limit := by
    have h1 : numerical32 a + numerical32 b =
        (ca + cb) + ((numerical32 a - ca) + (numerical32 b - cb)) := by ring
    have hTri1 := abs_add_le (ca + cb) ((numerical32 a - ca) + (numerical32 b - cb))
    have hTri2 := abs_add_le (numerical32 a - ca) (numerical32 b - cb)
    rw [← h1] at hTri1
    linarith [ha.2, hb.2]
  have hOp := binary32_add_finite_strict_error a b ha.1 hb.1 limit hLim hSum
  refine ⟨hOp.1, ?_⟩
  have h1 : numerical32 (a.add b) - (ca + cb) =
      (numerical32 (a.add b) - (numerical32 a + numerical32 b)) +
      ((numerical32 a - ca) + (numerical32 b - cb)) := by ring
  have hTri1 := abs_add_le (numerical32 (a.add b) - (numerical32 a + numerical32 b))
    ((numerical32 a - ca) + (numerical32 b - cb))
  have hTri2 := abs_add_le (numerical32 a - ca) (numerical32 b - cb)
  rw [← h1] at hTri1
  unfold ulpHalf
  linarith [hOp.2, ha.2, hb.2]

theorem wordNear_sub {a b : Binary32} {ca cb ra rb : ℚ} {limit : Int}
    (ha : wordNear a ca ra) (hb : wordNear b cb rb) (hLim : limit ≤ 33)
    (hCap : |ca - cb| + ra + rb < (2 : ℚ) ^ limit) :
    wordNear (a.sub b) (ca - cb) (ra + rb + ulpHalf limit) := by
  have hSub : |numerical32 a - numerical32 b| < (2 : ℚ) ^ limit := by
    have h1 : numerical32 a - numerical32 b =
        (ca - cb) + ((numerical32 a - ca) - (numerical32 b - cb)) := by ring
    have hTri1 := abs_add_le (ca - cb) ((numerical32 a - ca) - (numerical32 b - cb))
    have hTri2 := abs_sub (numerical32 a - ca) (numerical32 b - cb)
    rw [← h1] at hTri1
    linarith [ha.2, hb.2]
  have hOp := binary32_sub_strict_error a b ha.1 hb.1 limit hLim hSub
  refine ⟨hOp.1, ?_⟩
  have h1 : numerical32 (a.sub b) - (ca - cb) =
      (numerical32 (a.sub b) - (numerical32 a - numerical32 b)) +
      ((numerical32 a - ca) - (numerical32 b - cb)) := by ring
  have hTri1 := abs_add_le (numerical32 (a.sub b) - (numerical32 a - numerical32 b))
    ((numerical32 a - ca) - (numerical32 b - cb))
  have hTri2 := abs_sub (numerical32 a - ca) (numerical32 b - cb)
  rw [← h1] at hTri1
  unfold ulpHalf
  linarith [hOp.2, ha.2, hb.2]

theorem wordNear_mul {a b : Binary32} {ca cb ra rb : ℚ} {limit : Int}
    (ha : wordNear a ca ra) (hb : wordNear b cb rb) (hLim : limit ≤ 33)
    (hCap : (|ca| + ra) * (|cb| + rb) < (2 : ℚ) ^ limit) :
    wordNear (a.mul b) (ca * cb) (|ca| * rb + |cb| * ra + ra * rb + ulpHalf limit) := by
  have haAbs : |numerical32 a| ≤ |ca| + ra := by
    have h1 : numerical32 a = ca + (numerical32 a - ca) := by ring
    have h2 := abs_add_le ca (numerical32 a - ca)
    rw [← h1] at h2
    linarith [ha.2]
  have hbAbs : |numerical32 b| ≤ |cb| + rb := by
    have h1 : numerical32 b = cb + (numerical32 b - cb) := by ring
    have h2 := abs_add_le cb (numerical32 b - cb)
    rw [← h1] at h2
    linarith [hb.2]
  have hProd : |numerical32 a * numerical32 b| < (2 : ℚ) ^ limit := by
    rw [abs_mul]
    have hLe : |numerical32 a| * |numerical32 b| ≤ (|ca| + ra) * (|cb| + rb) :=
      mul_le_mul haAbs hbAbs (abs_nonneg _)
        (by linarith [abs_nonneg ca, ha.2, abs_nonneg (numerical32 a - ca)])
    linarith
  have hOp := binary32_mul_strict_error a b ha.1 hb.1 limit hLim hProd
  refine ⟨hOp.1, ?_⟩
  have hDiff : numerical32 a * numerical32 b - ca * cb =
      ca * (numerical32 b - cb) + cb * (numerical32 a - ca) +
      (numerical32 a - ca) * (numerical32 b - cb) := by ring
  have hErr1 : |numerical32 a * numerical32 b - ca * cb| ≤
      |ca| * rb + |cb| * ra + ra * rb := by
    rw [hDiff]
    have hTri1 := abs_add_le (ca * (numerical32 b - cb) + cb * (numerical32 a - ca))
      ((numerical32 a - ca) * (numerical32 b - cb))
    have hTri2 := abs_add_le (ca * (numerical32 b - cb)) (cb * (numerical32 a - ca))
    rw [abs_mul] at hTri1
    rw [abs_mul, abs_mul] at hTri2
    have hm1 : |ca| * |numerical32 b - cb| ≤ |ca| * rb :=
      mul_le_mul_of_nonneg_left hb.2 (abs_nonneg ca)
    have hm2 : |cb| * |numerical32 a - ca| ≤ |cb| * ra :=
      mul_le_mul_of_nonneg_left ha.2 (abs_nonneg cb)
    have hm3 : |numerical32 a - ca| * |numerical32 b - cb| ≤ ra * rb :=
      mul_le_mul ha.2 hb.2 (abs_nonneg _) (le_trans (abs_nonneg _) ha.2)
    linarith
  have h1 : numerical32 (a.mul b) - ca * cb =
      (numerical32 (a.mul b) - numerical32 a * numerical32 b) +
      (numerical32 a * numerical32 b - ca * cb) := by ring
  have h2 := abs_add_le (numerical32 (a.mul b) - numerical32 a * numerical32 b)
    (numerical32 a * numerical32 b - ca * cb)
  rw [← h1] at h2
  unfold ulpHalf
  linarith [hOp.2]

theorem logStep_project_le_of_neg_delta {config : Config} {rails : StepSizeRails config}
    (stored : LogStepSize rails) {metaDelta : Binary32}
    (hFin : metaDelta.Finite) (hNeg : numerical32 metaDelta ≤ 0)
    (hBd : |numerical32 stored.value + numerical32 metaDelta| ≤ 8589934592) :
    numerical32 (LogStepSize.project rails (stored.value.add metaDelta)).value ≤
      numerical32 stored.value := by
  have hAdd := binary32_rounded_add stored.value metaDelta stored.legal.1 hFin hBd
  have hLe : numerical32 (stored.value.add metaDelta) ≤ numerical32 stored.value :=
    hAdd.2.mono (binary32_rounded_exact stored.value stored.legal.1) (by linarith)
  have hKeyLe : (stored.value.add metaDelta).key ≤ stored.value.key :=
    (numerical32_order _ _ hAdd.1 stored.legal.1).mp hLe
  have hProjFin : (LogStepSize.project rails (stored.value.add metaDelta)).value.Finite :=
    (LogStepSize.project rails (stored.value.add metaDelta)).legal.1
  apply (numerical32_order _ _ hProjFin stored.legal.1).mpr
  change (rails.range.saturate (stored.value.add metaDelta)).key ≤ stored.value.key
  unfold Interval32.saturate
  rw [Binary32.saturate_eq_less]
  have hNotNaN : (stored.value.add metaDelta).isNaN = false :=
    Binary32.finite_not_nan _ hAdd.1
  simp only [Binary32.less_eq_key, hNotNaN,
    Binary32.finite_not_nan _ rails.range.lowerFinite,
    Binary32.finite_not_nan _ rails.range.upperFinite,
    Bool.not_false, Bool.true_and, Bool.false_or]
  split
  · exact stored.legal.2.1
  · split
    · rename_i hHi
      simp only [decide_eq_true_eq] at hHi
      have := stored.legal.2.2
      omega
    · exact hKeyLe

theorem logStep_project_lt_of_neg_delta {config : Config} {rails : StepSizeRails config}
    (stored : LogStepSize rails) {metaDelta : Binary32} {limit : Int}
    (hAbove : rails.range.lower.key < stored.value.key)
    (hFin : metaDelta.Finite) (hLim : limit ≤ 33)
    (hCap : |numerical32 stored.value + numerical32 metaDelta| < (2 : ℚ) ^ limit)
    (hClear : numerical32 metaDelta + ulpHalf limit < 0) :
    numerical32 (LogStepSize.project rails (stored.value.add metaDelta)).value <
      numerical32 stored.value := by
  have hAdd := binary32_add_finite_strict_error stored.value metaDelta
    stored.legal.1 hFin limit hLim hCap
  have hUp := (abs_le.mp hAdd.2).2
  have hLt : numerical32 (stored.value.add metaDelta) < numerical32 stored.value := by
    unfold ulpHalf at hClear
    linarith
  have hKeyLt : (stored.value.add metaDelta).key < stored.value.key :=
    (numerical32_strict_order _ _ hAdd.1 stored.legal.1).mp hLt
  have hProjFin : (LogStepSize.project rails (stored.value.add metaDelta)).value.Finite :=
    (LogStepSize.project rails (stored.value.add metaDelta)).legal.1
  apply (numerical32_strict_order _ _ hProjFin stored.legal.1).mpr
  change (rails.range.saturate (stored.value.add metaDelta)).key < stored.value.key
  unfold Interval32.saturate
  rw [Binary32.saturate_eq_less]
  have hNotNaN : (stored.value.add metaDelta).isNaN = false :=
    Binary32.finite_not_nan _ hAdd.1
  simp only [Binary32.less_eq_key, hNotNaN,
    Binary32.finite_not_nan _ rails.range.lowerFinite,
    Binary32.finite_not_nan _ rails.range.upperFinite,
    Bool.not_false, Bool.true_and, Bool.false_or]
  split
  · exact hAbove
  · split
    · rename_i hHi
      simp only [decide_eq_true_eq] at hHi
      have := stored.legal.2.2
      omega
    · exact hKeyLt

private theorem registers_get_fields {config : Config} {dimension : Dimension}
    {s1 s2 : NumericState config dimension} {idx : FeatIdx dimension}
    (hEq : registers s1 idx = registers s2 idx) :
    (s1.transient.z.get idx).value = (s2.transient.z.get idx).value ∧
    (s1.transient.zDelta.get idx).value = (s2.transient.zDelta.get idx).value ∧
    (s1.transient.zBar.get idx).value = (s2.transient.zBar.get idx).value ∧
    (s1.transient.lastAlpha.get idx).value = (s2.transient.lastAlpha.get idx).value ∧
    (s1.transient.deltaWeight.get idx).value = (s2.transient.deltaWeight.get idx).value ∧
    (s1.transient.h.get idx).value = (s2.transient.h.get idx).value ∧
    (s1.transient.hOld.get idx).value = (s2.transient.hOld.get idx).value ∧
    (s1.transient.hTemp.get idx).value = (s2.transient.hTemp.get idx).value ∧
    (s1.transient.p.get idx).value = (s2.transient.p.get idx).value := by
  exact ⟨congrArg (·[0]) hEq, congrArg (·[1]) hEq, congrArg (·[2]) hEq,
    congrArg (·[3]) hEq, congrArg (·[4]) hEq, congrArg (·[5]) hEq,
    congrArg (·[6]) hEq, congrArg (·[7]) hEq, congrArg (·[8]) hEq⟩

theorem step_active_meta_registers {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (features : ActiveSet dimension)
    (reward : Binary32) (idx : FeatIdx dimension)
    (hUnique : state.transient.eligible.toList.Nodup)
    (hElig : idx ∈ state.transient.eligible)
    (hAct : idx ∈ features.indices)
    (hUnclipped :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      let dw := (delta.mul (state.transient.z.get idx).value).sub
        ((state.transient.zDelta.get idx).value.mul state.transient.vDelta)
      let raw := (state.weights.get idx).value.add dw
      (Weight.project config.rule raw).value.numericallyEqual raw = true)
    (hKept :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      (state.firstLoopElement idx delta state.transient.vDelta
        (config.rule.gamma.mul config.lambda)).2 = false)
    (hNoOvr :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      let mid := state.learnFirstLoop config delta state.transient.vDelta
        (config.rule.gamma.mul config.lambda)
      let rate := Binary32.sumFrom .zero (features.indices.map fun j => (mid.beta.get j).alpha)
      config.eta.less rate = false) :
    let v := state.linearPrediction features
    let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
    let vDelta := state.transient.vDelta
    let decay := config.rule.gamma.mul config.lambda
    let mid := state.learnFirstLoop config delta vDelta decay
    let tSum := Binary32.sumFrom .zero
      (features.indices.map fun j => (mid.transient.z.get j).value)
    let metaDelta := ((config.metaStep.div (state.stepSize idx)).mul
      (delta.sub vDelta)).mul (state.transient.p.get idx).value
    let nextH := ((state.transient.hTemp.get idx).value.add
      (delta.mul (state.transient.zBar.get idx).value)).sub
      ((state.transient.zDelta.get idx).value.mul vDelta)
    let zd := (config.eta.div config.eta).mul (mid.beta.get idx).alpha
    let zNext := ((state.transient.z.get idx).value.mul decay).add
      (zd.mul (Binary32.one.sub tSum))
    let out := (state.step config features reward).1
    (out.beta.get idx).value =
      (LogStepSize.project state.rails ((state.beta.get idx).value.add metaDelta)).value ∧
    (out.transient.hOld.get idx).value = (state.transient.h.get idx).value ∧
    (out.transient.h.get idx).value = nextH ∧
    (out.transient.p.get idx).value =
      ((state.transient.p.get idx).value.mul decay).add nextH ∧
    (out.transient.hTemp.get idx).value =
      (nextH.sub ((state.transient.h.get idx).value.mul (zNext.sub zd))).sub (nextH.mul zd) ∧
    (out.transient.z.get idx).value = zNext ∧
    (out.transient.zDelta.get idx).value = zd := by
  dsimp only at hUnclipped hKept hNoOvr ⊢
  set v := state.linearPrediction features
  set delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
  set vDelta := state.transient.vDelta
  set decay := config.rule.gamma.mul config.lambda
  set mid := state.learnFirstLoop config delta vDelta decay
  simp only [vector_get] at hUnclipped
  have hFirst := firstLoop_pointwise state hUnique delta vDelta decay
  have hMidSlot := hFirst.2.2.2.2.2.2 idx hElig
  have hSecond := secondLoop_pointwise mid features .zero
  have hOutSlot := hSecond.2.2.2.2.2.2 idx hAct
  have hMidBeta : (mid.beta.get idx).value =
      (LogStepSize.project state.rails ((state.beta.get idx).value.add
        (((config.metaStep.div (state.stepSize idx)).mul (delta.sub vDelta)).mul
          (state.transient.p.get idx).value))).value := by
    have h1 := hMidSlot.2.1
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self,
      hUnclipped, Bool.not_true, Bool.false_eq_true, ite_false] at h1
    simpa only [vector_get] using h1
  have hMidRegsEq : registers mid idx =
      registers (state.firstLoopElement idx delta vDelta decay).1 idx := by
    have h1 := hMidSlot.2.2
    rw [hKept] at h1
    simpa only [Bool.false_eq_true, ite_false] using h1
  have hMidRegs := registers_get_fields hMidRegsEq
  have hMidZ : (mid.transient.z.get idx).value = (state.transient.z.get idx).value.mul decay := by
    rw [hMidRegs.1]
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self]
  have hMidH : (mid.transient.h.get idx).value =
      ((state.transient.hTemp.get idx).value.add
        (delta.mul (state.transient.zBar.get idx).value)).sub
        ((state.transient.zDelta.get idx).value.mul vDelta) := by
    rw [hMidRegs.2.2.2.2.2.1]
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self,
      hUnclipped, Bool.not_true, Bool.false_eq_true, ite_false]
  have hMidHOld : (mid.transient.hOld.get idx).value = (state.transient.h.get idx).value := by
    rw [hMidRegs.2.2.2.2.2.2.1]
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self,
      hUnclipped, Bool.not_true, Bool.false_eq_true, ite_false]
  have hMidP : (mid.transient.p.get idx).value = (state.transient.p.get idx).value.mul decay := by
    rw [hMidRegs.2.2.2.2.2.2.2.2]
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self,
      hUnclipped, Bool.not_true, Bool.false_eq_true, ite_false]
  have hOutBeta : ((mid.learnSecondLoop config features .zero).1.beta.get idx).value =
      (mid.beta.get idx).value := by
    have h1 := hOutSlot.2.1
    rw [hNoOvr] at h1
    simpa only [Bool.false_eq_true, ite_false,
      NumericState.secondLoopElement, NumericState.secondLoopElementAt] using h1
  have hOutRegs := registers_get_fields hOutSlot.2.2
  simp only [NumericState.step_def]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hOutBeta.trans hMidBeta
  · change ((mid.learnSecondLoop config features .zero).1.transient.hOld.get idx).value = _
    rw [hOutRegs.2.2.2.2.2.2.1, hNoOvr]
    simpa only [Bool.false_eq_true, ite_false,
      NumericState.secondLoopElement, NumericState.secondLoopElementAt] using hMidHOld
  · change ((mid.learnSecondLoop config features .zero).1.transient.h.get idx).value = _
    rw [hOutRegs.2.2.2.2.2.1, hNoOvr]
    simpa only [Bool.false_eq_true, ite_false,
      NumericState.secondLoopElement, NumericState.secondLoopElementAt] using hMidH
  · change ((mid.learnSecondLoop config features .zero).1.transient.p.get idx).value = _
    rw [hOutRegs.2.2.2.2.2.2.2.2, hNoOvr]
    simp only [Bool.false_eq_true, ite_false,
      NumericState.secondLoopElement, NumericState.secondLoopElementAt,
      vector_get, Vector.getElem_set_self]
    simp only [vector_get] at hMidP hMidH
    rw [hMidP, hMidH]
  · change ((mid.learnSecondLoop config features .zero).1.transient.hTemp.get idx).value = _
    rw [hOutRegs.2.2.2.2.2.2.2.1, hNoOvr]
    simp only [Bool.false_eq_true, ite_false,
      NumericState.secondLoopElement, NumericState.secondLoopElementAt,
      vector_get, Vector.getElem_set_self]
    simp only [vector_get] at hMidZ hMidHOld hMidH
    rw [hMidZ, hMidHOld, hMidH]
  · change ((mid.learnSecondLoop config features .zero).1.transient.z.get idx).value = _
    rw [hOutRegs.1, hNoOvr]
    simp only [Bool.false_eq_true, ite_false,
      NumericState.secondLoopElement, NumericState.secondLoopElementAt,
      vector_get, Vector.getElem_set_self]
    simp only [vector_get] at hMidZ
    rw [hMidZ]
  · change ((mid.learnSecondLoop config features .zero).1.transient.zDelta.get idx).value = _
    rw [hOutRegs.2.1, hNoOvr]
    simp only [Bool.false_eq_true, ite_false,
      NumericState.secondLoopElement, NumericState.secondLoopElementAt,
      vector_get, Vector.getElem_set_self]

theorem step_inactive_meta_registers {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (features : ActiveSet dimension)
    (reward : Binary32) (idx : FeatIdx dimension)
    (hUnique : state.transient.eligible.toList.Nodup)
    (hElig : idx ∈ state.transient.eligible)
    (hInact : idx ∉ features.indices)
    (hUnclipped :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      let dw := (delta.mul (state.transient.z.get idx).value).sub
        ((state.transient.zDelta.get idx).value.mul state.transient.vDelta)
      let raw := (state.weights.get idx).value.add dw
      (Weight.project config.rule raw).value.numericallyEqual raw = true)
    (hKept :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      (state.firstLoopElement idx delta state.transient.vDelta
        (config.rule.gamma.mul config.lambda)).2 = false) :
    let v := state.linearPrediction features
    let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
    let vDelta := state.transient.vDelta
    let decay := config.rule.gamma.mul config.lambda
    let metaDelta := ((config.metaStep.div (state.stepSize idx)).mul
      (delta.sub vDelta)).mul (state.transient.p.get idx).value
    let nextH := ((state.transient.hTemp.get idx).value.add
      (delta.mul (state.transient.zBar.get idx).value)).sub
      ((state.transient.zDelta.get idx).value.mul vDelta)
    let out := (state.step config features reward).1
    (out.beta.get idx).value =
      (LogStepSize.project state.rails ((state.beta.get idx).value.add metaDelta)).value ∧
    (out.transient.hOld.get idx).value = (state.transient.h.get idx).value ∧
    (out.transient.h.get idx).value = nextH ∧
    (out.transient.hTemp.get idx).value = nextH ∧
    (out.transient.p.get idx).value = (state.transient.p.get idx).value.mul decay := by
  dsimp only at hUnclipped hKept ⊢
  set v := state.linearPrediction features
  set delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
  set vDelta := state.transient.vDelta
  set decay := config.rule.gamma.mul config.lambda
  set mid := state.learnFirstLoop config delta vDelta decay
  simp only [vector_get] at hUnclipped
  have hFirst := firstLoop_pointwise state hUnique delta vDelta decay
  have hMidSlot := hFirst.2.2.2.2.2.2 idx hElig
  have hSecond := secondLoop_pointwise mid features .zero
  have hOutSlot := hSecond.2.2.2.2.2.1 idx hInact
  have hMidBeta : (mid.beta.get idx).value =
      (LogStepSize.project state.rails ((state.beta.get idx).value.add
        (((config.metaStep.div (state.stepSize idx)).mul (delta.sub vDelta)).mul
          (state.transient.p.get idx).value))).value := by
    have h1 := hMidSlot.2.1
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self,
      hUnclipped, Bool.not_true, Bool.false_eq_true, ite_false] at h1
    simpa only [vector_get] using h1
  have hMidRegsEq : registers mid idx =
      registers (state.firstLoopElement idx delta vDelta decay).1 idx := by
    have h1 := hMidSlot.2.2
    rw [hKept] at h1
    simpa only [Bool.false_eq_true, ite_false] using h1
  have hMidRegs := registers_get_fields hMidRegsEq
  have hOutRegs := registers_get_fields hOutSlot.2.2
  simp only [NumericState.step_def]
  refine ⟨hOutSlot.2.1.trans hMidBeta, ?_, ?_, ?_, ?_⟩
  · change ((mid.learnSecondLoop config features .zero).1.transient.hOld.get idx).value = _
    rw [hOutRegs.2.2.2.2.2.2.1, hMidRegs.2.2.2.2.2.2.1]
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self,
      hUnclipped, Bool.not_true, Bool.false_eq_true, ite_false]
  · change ((mid.learnSecondLoop config features .zero).1.transient.h.get idx).value = _
    rw [hOutRegs.2.2.2.2.2.1, hMidRegs.2.2.2.2.2.1]
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self,
      hUnclipped, Bool.not_true, Bool.false_eq_true, ite_false]
  · change ((mid.learnSecondLoop config features .zero).1.transient.hTemp.get idx).value = _
    rw [hOutRegs.2.2.2.2.2.2.2.1, hMidRegs.2.2.2.2.2.2.2.1]
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self,
      hUnclipped, Bool.not_true, Bool.false_eq_true, ite_false]
  · change ((mid.learnSecondLoop config features .zero).1.transient.p.get idx).value = _
    rw [hOutRegs.2.2.2.2.2.2.2.2, hMidRegs.2.2.2.2.2.2.2.2]
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self,
      hUnclipped, Bool.not_true, Bool.false_eq_true, ite_false]

def altSignQ (t : Nat) : ℚ := (-1 : ℚ) ^ t

theorem altSignQ_sq (t : Nat) : altSignQ t * altSignQ t = 1 := by
  unfold altSignQ
  rw [← sq, ← pow_mul, mul_comm, pow_mul]
  norm_num

theorem altSignQ_succ (t : Nat) : altSignQ (t + 1) = -altSignQ t := by
  unfold altSignQ
  rw [pow_succ]
  ring

def period2AmpQ (zStar zD zBar kappa d : ℚ) : ℚ :=
  d * (zBar + zD * kappa) / (2 + zStar - 2 * zD)

structure Period2Ref where
  hOld : ℚ
  h : ℚ
  hTemp : ℚ
  p : ℚ

def repairP3Period2Ref (rho zStar zD zBar kappa d : ℚ) (t : Nat) : Period2Ref :=
  let aH := period2AmpQ zStar zD zBar kappa d
  let s := altSignQ t
  ⟨s * aH, -s * aH, -s * (1 + zStar - 2 * zD) * aH, -s * aH / (1 + rho)⟩

theorem step_period2_alternating_sign_preservation_binary32 {config : Config}
    {dimension : Dimension}
    (state : NumericState config dimension) (features : ActiveSet dimension)
    (reward : Binary32) (idx : FeatIdx dimension)
    (hUnique : state.transient.eligible.toList.Nodup)
    (hElig : idx ∈ state.transient.eligible)
    (hAct : idx ∈ features.indices)
    (hUnclipped :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      let dw := (delta.mul (state.transient.z.get idx).value).sub
        ((state.transient.zDelta.get idx).value.mul state.transient.vDelta)
      let raw := (state.weights.get idx).value.add dw
      (Weight.project config.rule raw).value.numericallyEqual raw = true)
    (hKept :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      (state.firstLoopElement idx delta state.transient.vDelta
        (config.rule.gamma.mul config.lambda)).2 = false)
    (hNoOvr :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      let mid := state.learnFirstLoop config delta state.transient.vDelta
        (config.rule.gamma.mul config.lambda)
      let rate := Binary32.sumFrom .zero (features.indices.map fun j => (mid.beta.get j).alpha)
      config.eta.less rate = false)
    (rho zStar zD zBar kappa d : ℚ) (t : Nat)
    (hThetaPos : 0 < numerical32 config.metaStep)
    (hAlphaPos : 0 < numerical32 (state.stepSize idx))
    (hThetaFin : config.metaStep.Finite)
    (hAlphaFin : (state.stepSize idx).Finite)
    (hRho0 : 0 ≤ rho)
    (hD : d ≠ 0) (hKappa : 0 ≤ kappa) (hZBar : 0 < zBar) (hZD : 0 ≤ zD)
    (hDen : 0 < 2 + zStar - 2 * zD)
    (rH rHTemp rP rErr rInc1 rInc2 rRho rZSub rZD : ℚ)
    (limit : Int) (hLim : limit ≤ 33)
    (hNearH : wordNear (state.transient.h.get idx).value
      (repairP3Period2Ref rho zStar zD zBar kappa d t).h rH)
    (hNearHTemp : wordNear (state.transient.hTemp.get idx).value
      (repairP3Period2Ref rho zStar zD zBar kappa d t).hTemp rHTemp)
    (hNearP : wordNear (state.transient.p.get idx).value
      (repairP3Period2Ref rho zStar zD zBar kappa d t).p rP)
    (hNearErr :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      wordNear (delta.sub state.transient.vDelta) (altSignQ t * d * (1 + kappa)) rErr)
    (hNearInc1 :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      wordNear (delta.mul (state.transient.zBar.get idx).value) (altSignQ t * d * zBar) rInc1)
    (hNearInc2 :
      wordNear ((state.transient.zDelta.get idx).value.mul state.transient.vDelta)
        (-(altSignQ t * d * (zD * kappa))) rInc2)
    (hNearDecay : wordNear (config.rule.gamma.mul config.lambda) rho rRho)
    (hNearZSub :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      let decay := config.rule.gamma.mul config.lambda
      let mid := state.learnFirstLoop config delta state.transient.vDelta decay
      let tSum := Binary32.sumFrom .zero
        (features.indices.map fun j => (mid.transient.z.get j).value)
      let zd := (config.eta.div config.eta).mul (mid.beta.get idx).alpha
      let zNext := ((state.transient.z.get idx).value.mul decay).add
        (zd.mul (Binary32.one.sub tSum))
      wordNear (zNext.sub zd) (zStar - zD) rZSub)
    (hNearZD :
      let v := state.linearPrediction features
      let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
      let mid := state.learnFirstLoop config delta state.transient.vDelta
        (config.rule.gamma.mul config.lambda)
      let zd := (config.eta.div config.eta).mul (mid.beta.get idx).alpha
      wordNear zd zD rZD)
    (hCapGain : |numerical32 config.metaStep / numerical32 (state.stepSize idx)| < (2 : ℚ) ^ limit)
    (hCapGainErr :
      (|numerical32 config.metaStep / numerical32 (state.stepSize idx)| + ulpHalf limit) *
        (|altSignQ t * d * (1 + kappa)| + rErr) < (2 : ℚ) ^ limit)
    (hCapMeta :
      let g := numerical32 config.metaStep / numerical32 (state.stepSize idx)
      let e := altSignQ t * d * (1 + kappa)
      let rGE := |g| * rErr + |e| * ulpHalf limit + ulpHalf limit * rErr + ulpHalf limit
      (|g * e| + rGE) * (|(repairP3Period2Ref rho zStar zD zBar kappa d t).p| + rP) <
        (2 : ℚ) ^ limit)
    (hCapAdd1 :
      |(repairP3Period2Ref rho zStar zD zBar kappa d t).hTemp + altSignQ t * d * zBar| +
        rHTemp + rInc1 < (2 : ℚ) ^ limit)
    (hCapNextH :
      |(repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h| +
        (rHTemp + rInc1 + ulpHalf limit) + rInc2 < (2 : ℚ) ^ limit)
    (hCapPMul :
      (|(repairP3Period2Ref rho zStar zD zBar kappa d t).p| + rP) * (|rho| + rRho) <
        (2 : ℚ) ^ limit)
    (hCapPNext :
      let rHNext := rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit
      let rPMul := |(repairP3Period2Ref rho zStar zD zBar kappa d t).p| * rRho +
        |rho| * rP + rP * rRho + ulpHalf limit
      |(repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).p| + rPMul + rHNext <
        (2 : ℚ) ^ limit)
    (hCapMul1 :
      (|(repairP3Period2Ref rho zStar zD zBar kappa d t).h| + rH) * (|zStar - zD| + rZSub) <
        (2 : ℚ) ^ limit)
    (hCapSub1 :
      let rHNext := rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit
      let rM1 := |(repairP3Period2Ref rho zStar zD zBar kappa d t).h| * rZSub +
        |zStar - zD| * rH + rH * rZSub + ulpHalf limit
      |(repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h -
          (repairP3Period2Ref rho zStar zD zBar kappa d t).h * (zStar - zD)| +
        rHNext + rM1 < (2 : ℚ) ^ limit)
    (hCapMul2 :
      let rHNext := rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit
      (|(repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h| + rHNext) * (|zD| + rZD) <
        (2 : ℚ) ^ limit)
    (hCapHTempNext :
      let rHNext := rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit
      let rM1 := |(repairP3Period2Ref rho zStar zD zBar kappa d t).h| * rZSub +
        |zStar - zD| * rH + rH * rZSub + ulpHalf limit
      let rS1 := rHNext + rM1 + ulpHalf limit
      let rM2 := |(repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h| * rZD +
        |zD| * rHNext + rHNext * rZD + ulpHalf limit
      |(repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).hTemp| + rS1 + rM2 <
        (2 : ℚ) ^ limit)
    (hMargin :
      let theta := numerical32 config.metaStep
      let alpha := numerical32 (state.stepSize idx)
      let g := theta / alpha
      let e := altSignQ t * d * (1 + kappa)
      let pRef := (repairP3Period2Ref rho zStar zD zBar kappa d t).p
      let rGE := |g| * rErr + |e| * ulpHalf limit + ulpHalf limit * rErr + ulpHalf limit
      let eMeta := |g * e| * rP + |pRef| * rGE + rGE * rP + ulpHalf limit
      eMeta < (theta / alpha) *
        (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
          ((1 + rho) * (2 + zStar - 2 * zD)))) :
    let v := state.linearPrediction features
    let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
    let metaDelta := ((config.metaStep.div (state.stepSize idx)).mul
      (delta.sub state.transient.vDelta)).mul (state.transient.p.get idx).value
    let out := (state.step config features reward).1
    let refNext := repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)
    let theta := numerical32 config.metaStep
    let alpha := numerical32 (state.stepSize idx)
    let g := theta / alpha
    let e := altSignQ t * d * (1 + kappa)
    let pRef := (repairP3Period2Ref rho zStar zD zBar kappa d t).p
    let rGE := |g| * rErr + |e| * ulpHalf limit + ulpHalf limit * rErr + ulpHalf limit
    let eMeta := |g * e| * rP + |pRef| * rGE + rGE * rP + ulpHalf limit
    let exactMag := (theta / alpha) *
      (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
        ((1 + rho) * (2 + zStar - 2 * zD)))
    let rHNext := rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit
    let rPMul := |pRef| * rRho + |rho| * rP + rP * rRho + ulpHalf limit
    let rM1 := |(repairP3Period2Ref rho zStar zD zBar kappa d t).h| * rZSub +
      |zStar - zD| * rH + rH * rZSub + ulpHalf limit
    let rM2 := |refNext.h| * rZD + |zD| * rHNext + rHNext * rZD + ulpHalf limit
    wordNear (out.transient.hOld.get idx).value refNext.hOld rH ∧
    wordNear (out.transient.h.get idx).value refNext.h rHNext ∧
    wordNear (out.transient.p.get idx).value refNext.p (rPMul + rHNext + ulpHalf limit) ∧
    wordNear (out.transient.hTemp.get idx).value refNext.hTemp
      (rHNext + rM1 + rM2 + 2 * ulpHalf limit) ∧
    wordNear metaDelta (-exactMag) eMeta ∧
    0 < exactMag ∧
    numerical32 metaDelta < 0 ∧
    (|numerical32 (state.beta.get idx).value + numerical32 metaDelta| ≤ 8589934592 →
      numerical32 (out.beta.get idx).value ≤ numerical32 (state.beta.get idx).value) ∧
    (∀ betaLimit : Int, state.rails.range.lower.key < (state.beta.get idx).value.key →
      betaLimit ≤ 33 →
      |numerical32 (state.beta.get idx).value + numerical32 metaDelta| < (2 : ℚ) ^ betaLimit →
      ulpHalf betaLimit < exactMag - eMeta →
      numerical32 (out.beta.get idx).value < numerical32 (state.beta.get idx).value) := by
  dsimp only
  have hRegs := step_active_meta_registers state features reward idx
    hUnique hElig hAct hUnclipped hKept hNoOvr
  dsimp only at hRegs
  have hRhoPos : 0 < 1 + rho := by linarith
  set aH : ℚ := period2AmpQ zStar zD zBar kappa d
  have hAmp : d * (zBar + zD * kappa) = (2 + zStar - 2 * zD) * aH := by
    dsimp only [aH, period2AmpQ]
    rw [mul_div_cancel₀ _ hDen.ne']
  have hHNextCenter :
      (repairP3Period2Ref rho zStar zD zBar kappa d t).hTemp + altSignQ t * d * zBar -
        -(altSignQ t * d * (zD * kappa)) =
      (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h := by
    dsimp only [repairP3Period2Ref]
    rw [altSignQ_succ]
    have hSum : altSignQ t * d * zBar - -(altSignQ t * d * (zD * kappa)) =
        altSignQ t * (d * (zBar + zD * kappa)) := by ring
    have hEq1 : -altSignQ t * (1 + zStar - 2 * zD) * aH +
        altSignQ t * ((2 + zStar - 2 * zD) * aH) = - -altSignQ t * aH := by ring
    calc
      -altSignQ t * (1 + zStar - 2 * zD) * aH + altSignQ t * d * zBar -
          -(altSignQ t * d * (zD * kappa))
        = -altSignQ t * (1 + zStar - 2 * zD) * aH +
            (altSignQ t * d * zBar - -(altSignQ t * d * (zD * kappa))) := by ring
      _ = -altSignQ t * (1 + zStar - 2 * zD) * aH +
            altSignQ t * (d * (zBar + zD * kappa)) := by rw [hSum]
      _ = -altSignQ t * (1 + zStar - 2 * zD) * aH +
            altSignQ t * ((2 + zStar - 2 * zD) * aH) := by rw [hAmp]
      _ = - -altSignQ t * aH := hEq1
  have hHOldNextCenter :
      (repairP3Period2Ref rho zStar zD zBar kappa d t).h =
      (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).hOld := by
    dsimp only [repairP3Period2Ref]
    rw [altSignQ_succ]
  have hPNextCenter :
      (repairP3Period2Ref rho zStar zD zBar kappa d t).p * rho +
        (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h =
      (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).p := by
    dsimp only [repairP3Period2Ref]
    rw [altSignQ_succ]
    field_simp [hRhoPos.ne']
    ring
  have hHTempNextCenter :
      (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h -
        (repairP3Period2Ref rho zStar zD zBar kappa d t).h * (zStar - zD) -
        (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h * zD =
      (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).hTemp := by
    dsimp only [repairP3Period2Ref]
    rw [altSignQ_succ]
    ring
  have hMetaCenter :
      numerical32 config.metaStep / numerical32 (state.stepSize idx) *
        (altSignQ t * d * (1 + kappa)) *
        (repairP3Period2Ref rho zStar zD zBar kappa d t).p =
      -(numerical32 config.metaStep / numerical32 (state.stepSize idx) *
        (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
          ((1 + rho) * (2 + zStar - 2 * zD)))) := by
    dsimp only [repairP3Period2Ref, period2AmpQ]
    have hSq : altSignQ t * altSignQ t = 1 := altSignQ_sq t
    have hRearr :
        numerical32 config.metaStep / numerical32 (state.stepSize idx) *
          (altSignQ t * d * (1 + kappa)) *
          (-(altSignQ t) * (d * (zBar + zD * kappa) / (2 + zStar - 2 * zD)) / (1 + rho)) =
        -(altSignQ t * altSignQ t) *
          (numerical32 config.metaStep / numerical32 (state.stepSize idx) *
            (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
              ((1 + rho) * (2 + zStar - 2 * zD)))) := by
      field_simp [hAlphaPos.ne', hRhoPos.ne', hDen.ne']
    rw [hRearr, hSq]
    ring
  have hAdd1 := wordNear_add hNearHTemp hNearInc1 hLim hCapAdd1
  have hNextH0 := wordNear_sub hAdd1 hNearInc2 hLim (by rwa [hHNextCenter])
  have hNextH : wordNear
      (((state.transient.hTemp.get idx).value.add
        (((reward.add (config.rule.gamma.mul (state.linearPrediction features))).sub
          state.transient.vOld).mul (state.transient.zBar.get idx).value)).sub
        ((state.transient.zDelta.get idx).value.mul state.transient.vDelta))
      (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h
      (rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit) := by
    rw [hHNextCenter] at hNextH0
    refine ⟨hNextH0.1, ?_⟩
    linarith [hNextH0.2]
  have hPMul := wordNear_mul hNearP hNearDecay hLim hCapPMul
  have hPNext0 := wordNear_add hPMul hNextH hLim (by rwa [hPNextCenter])
  have hPNext : wordNear
      (((state.transient.p.get idx).value.mul (config.rule.gamma.mul config.lambda)).add
        (((state.transient.hTemp.get idx).value.add
          (((reward.add (config.rule.gamma.mul (state.linearPrediction features))).sub
            state.transient.vOld).mul (state.transient.zBar.get idx).value)).sub
          ((state.transient.zDelta.get idx).value.mul state.transient.vDelta)))
      (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).p
      (|(repairP3Period2Ref rho zStar zD zBar kappa d t).p| * rRho + |rho| * rP + rP * rRho +
        ulpHalf limit + (rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit) + ulpHalf limit) := by
    rw [hPNextCenter] at hPNext0
    exact hPNext0
  have hMul1 := wordNear_mul hNearH hNearZSub hLim hCapMul1
  have hSub1 := wordNear_sub hNextH hMul1 hLim hCapSub1
  have hMul2 := wordNear_mul hNextH hNearZD hLim hCapMul2
  have hHTempNext0 := wordNear_sub hSub1 hMul2 hLim (by rwa [hHTempNextCenter])
  rw [hHTempNextCenter] at hHTempNext0
  have hHTempNext : wordNear ((state.step config features reward).1.transient.hTemp.get idx).value
      (repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).hTemp
      (rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit +
        (|(repairP3Period2Ref rho zStar zD zBar kappa d t).h| * rZSub +
          |zStar - zD| * rH + rH * rZSub + ulpHalf limit) +
        (|(repairP3Period2Ref rho zStar zD zBar kappa d (t + 1)).h| * rZD +
          |zD| * (rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit) +
          (rHTemp + rInc1 + rInc2 + 2 * ulpHalf limit) * rZD + ulpHalf limit) +
        2 * ulpHalf limit) := by
    rw [hRegs.2.2.2.2.1]
    refine ⟨hHTempNext0.1, ?_⟩
    linarith [hHTempNext0.2]
  have hDiv := binary32_div_strict_error config.metaStep (state.stepSize idx)
    hThetaFin hAlphaFin hAlphaPos.ne' limit hLim hCapGain
  have hGainNear : wordNear (config.metaStep.div (state.stepSize idx))
      (numerical32 config.metaStep / numerical32 (state.stepSize idx)) (ulpHalf limit) :=
    ⟨hDiv.1, hDiv.2⟩
  have hGENear := wordNear_mul hGainNear hNearErr hLim hCapGainErr
  have hMeta0 := wordNear_mul hGENear hNearP hLim hCapMeta
  have hMeta : wordNear
      (((config.metaStep.div (state.stepSize idx)).mul
        (((reward.add (config.rule.gamma.mul (state.linearPrediction features))).sub
          state.transient.vOld).sub state.transient.vDelta)).mul
        (state.transient.p.get idx).value)
      (-(numerical32 config.metaStep / numerical32 (state.stepSize idx) *
        (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
          ((1 + rho) * (2 + zStar - 2 * zD)))))
      (|numerical32 config.metaStep / numerical32 (state.stepSize idx) *
          (altSignQ t * d * (1 + kappa))| * rP +
        |(repairP3Period2Ref rho zStar zD zBar kappa d t).p| *
          (|numerical32 config.metaStep / numerical32 (state.stepSize idx)| * rErr +
            |altSignQ t * d * (1 + kappa)| * ulpHalf limit + ulpHalf limit * rErr + ulpHalf limit) +
        (|numerical32 config.metaStep / numerical32 (state.stepSize idx)| * rErr +
          |altSignQ t * d * (1 + kappa)| * ulpHalf limit + ulpHalf limit * rErr + ulpHalf limit) *
          rP + ulpHalf limit) := by
    rw [hMetaCenter] at hMeta0
    exact hMeta0
  have hExactPos :
      0 < numerical32 config.metaStep / numerical32 (state.stepSize idx) *
        (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
          ((1 + rho) * (2 + zStar - 2 * zD))) := by
    have hRatio : 0 < numerical32 config.metaStep / numerical32 (state.stepSize idx) :=
      div_pos hThetaPos hAlphaPos
    have hD2 : 0 < d ^ 2 := sq_pos_of_ne_zero hD
    have hK1 : 0 < 1 + kappa := by linarith
    have hZB : 0 < zBar + zD * kappa := by nlinarith
    have hNum : 0 < d ^ 2 * (1 + kappa) * (zBar + zD * kappa) :=
      mul_pos (mul_pos hD2 hK1) hZB
    exact mul_pos hRatio (div_pos hNum (mul_pos hRhoPos hDen))
  have hMetaNeg : numerical32
      (((config.metaStep.div (state.stepSize idx)).mul
        (((reward.add (config.rule.gamma.mul (state.linearPrediction features))).sub
          state.transient.vOld).sub state.transient.vDelta)).mul
        (state.transient.p.get idx).value) < 0 := by
    have hUp := (abs_le.mp hMeta.2).2
    linarith [hMargin]
  refine ⟨?_, ?_, ?_, ?_, hMeta, hExactPos, hMetaNeg, ?_, ?_⟩
  · rw [hRegs.2.1, ← hHOldNextCenter]
    exact hNearH
  · rw [hRegs.2.2.1]
    exact hNextH
  · rw [hRegs.2.2.2.1]
    exact hPNext
  · exact hHTempNext
  · intro hBd
    rw [hRegs.1]
    exact logStep_project_le_of_neg_delta (state.beta.get idx) hMeta.1 hMetaNeg.le hBd
  · intro betaLimit hAbove hBLim hBCap hBClear
    rw [hRegs.1]
    have hUp := (abs_le.mp hMeta.2).2
    exact logStep_project_lt_of_neg_delta (state.beta.get idx) hAbove hMeta.1 hBLim hBCap
      (by linarith)

theorem step_sparse_two_step_derivative_binary32 {config : Config} {dimension : Dimension}
    (st0 : NumericState config dimension)
    (features1 features2 : ActiveSet dimension) (reward1 reward2 : Binary32)
    (idx : FeatIdx dimension)
    (hUnique0 : st0.transient.eligible.toList.Nodup)
    (hElig0 : idx ∈ st0.transient.eligible)
    (hAct1 : idx ∈ features1.indices)
    (hInact2 : idx ∉ features2.indices)
    (hUnclipped1 :
      let v1 := st0.linearPrediction features1
      let delta1 := (reward1.add (config.rule.gamma.mul v1)).sub st0.transient.vOld
      let dw1 := (delta1.mul (st0.transient.z.get idx).value).sub
        ((st0.transient.zDelta.get idx).value.mul st0.transient.vDelta)
      let raw1 := (st0.weights.get idx).value.add dw1
      (Weight.project config.rule raw1).value.numericallyEqual raw1 = true)
    (hKept1 :
      let v1 := st0.linearPrediction features1
      let delta1 := (reward1.add (config.rule.gamma.mul v1)).sub st0.transient.vOld
      (st0.firstLoopElement idx delta1 st0.transient.vDelta
        (config.rule.gamma.mul config.lambda)).2 = false)
    (hNoOvr1 :
      let v1 := st0.linearPrediction features1
      let delta1 := (reward1.add (config.rule.gamma.mul v1)).sub st0.transient.vOld
      let mid1 := st0.learnFirstLoop config delta1 st0.transient.vDelta
        (config.rule.gamma.mul config.lambda)
      let rate1 := Binary32.sumFrom .zero (features1.indices.map fun j => (mid1.beta.get j).alpha)
      config.eta.less rate1 = false)
    (hUnique1 : (st0.step config features1 reward1).1.transient.eligible.toList.Nodup)
    (hElig1 : idx ∈ (st0.step config features1 reward1).1.transient.eligible)
    (hUnclipped2 :
      let st1 := (st0.step config features1 reward1).1
      let v2 := st1.linearPrediction features2
      let delta2 := (reward2.add (config.rule.gamma.mul v2)).sub st1.transient.vOld
      let dw2 := (delta2.mul (st1.transient.z.get idx).value).sub
        ((st1.transient.zDelta.get idx).value.mul st1.transient.vDelta)
      let raw2 := (st1.weights.get idx).value.add dw2
      (Weight.project config.rule raw2).value.numericallyEqual raw2 = true)
    (hKept2 :
      let st1 := (st0.step config features1 reward1).1
      let v2 := st1.linearPrediction features2
      let delta2 := (reward2.add (config.rule.gamma.mul v2)).sub st1.transient.vOld
      (st1.firstLoopElement idx delta2 st1.transient.vDelta
        (config.rule.gamma.mul config.lambda)).2 = false)
    (hH0 : (st0.transient.h.get idx).value = .zero)
    (hHTemp0 : (st0.transient.hTemp.get idx).value = .zero)
    (hP0 : (st0.transient.p.get idx).value = .zero)
    (hVD0 : st0.transient.vDelta = .zero)
    (hZDelta0Fin : (st0.transient.zDelta.get idx).value.Finite)
    (hDecayFin : (config.rule.gamma.mul config.lambda).Finite)
    (alpha r1 r2 : ℚ) (eps1 eps2 epsZ1 epsVD1 : ℚ) (limit : Int) (hLim : limit ≤ 33)
    (hNearInc1 :
      let v1 := st0.linearPrediction features1
      let delta1 := (reward1.add (config.rule.gamma.mul v1)).sub st0.transient.vOld
      wordNear (delta1.mul (st0.transient.zBar.get idx).value) (alpha * r1) eps1)
    (hNearZD1 :
      let st1 := (st0.step config features1 reward1).1
      wordNear (st1.transient.zDelta.get idx).value alpha epsZ1)
    (hNearZSub1Fin :
      let st1 := (st0.step config features1 reward1).1
      ((st1.transient.z.get idx).value.sub (st1.transient.zDelta.get idx).value).Finite)
    (hNearInc2 :
      let st1 := (st0.step config features1 reward1).1
      let v2 := st1.linearPrediction features2
      let delta2 := (reward2.add (config.rule.gamma.mul v2)).sub st1.transient.vOld
      wordNear (delta2.mul (st1.transient.zBar.get idx).value) (alpha * r2) eps2)
    (hNearVD1 :
      let st1 := (st0.step config features1 reward1).1
      wordNear st1.transient.vDelta (alpha * r1) epsVD1)
    (hCap1 : |alpha * r1| + eps1 < (2 : ℚ) ^ limit)
    (hCapH1 : |alpha * r1| + (eps1 + 2 * ulpHalf limit) < (2 : ℚ) ^ limit)
    (hCapH1ZD :
      (|alpha * r1| + (eps1 + 2 * ulpHalf limit)) * (|alpha| + epsZ1) < (2 : ℚ) ^ limit)
    (hCapHT1 :
      let rH1 := eps1 + 2 * ulpHalf limit
      let rM := |alpha * r1| * epsZ1 + |alpha| * rH1 + rH1 * epsZ1 + ulpHalf limit
      |alpha * r1 * (1 - alpha)| + (rH1 + ulpHalf limit) + rM < (2 : ℚ) ^ limit)
    (hCapAdd2 :
      let rH1 := eps1 + 2 * ulpHalf limit
      let rM := |alpha * r1| * epsZ1 + |alpha| * rH1 + rH1 * epsZ1 + ulpHalf limit
      let rHT1 := rH1 + rM + 2 * ulpHalf limit
      |alpha * r1 * (1 - alpha) + alpha * r2| + rHT1 + eps2 < (2 : ℚ) ^ limit)
    (hCapMul2 : (|alpha| + epsZ1) * (|alpha * r1| + epsVD1) < (2 : ℚ) ^ limit)
    (hCapH2 :
      let rH1 := eps1 + 2 * ulpHalf limit
      let rM := |alpha * r1| * epsZ1 + |alpha| * rH1 + rH1 * epsZ1 + ulpHalf limit
      let rHT1 := rH1 + rM + 2 * ulpHalf limit
      let rM2 := |alpha| * epsVD1 + |alpha * r1| * epsZ1 + epsZ1 * epsVD1 + ulpHalf limit
      |alpha * r1 * (1 - 2 * alpha) + alpha * r2| + (rHT1 + eps2 + ulpHalf limit) + rM2 <
        (2 : ℚ) ^ limit) :
    let st1 := (st0.step config features1 reward1).1
    let st2 := (st1.step config features2 reward2).1
    let rH1 := eps1 + 2 * ulpHalf limit
    let rM := |alpha * r1| * epsZ1 + |alpha| * rH1 + rH1 * epsZ1 + ulpHalf limit
    let rHT1 := rH1 + rM + 2 * ulpHalf limit
    let rM2 := |alpha| * epsVD1 + |alpha * r1| * epsZ1 + epsZ1 * epsVD1 + ulpHalf limit
    wordNear (st1.transient.p.get idx).value (alpha * r1) (rH1 + ulpHalf limit) ∧
    wordNear (st1.transient.hTemp.get idx).value (alpha * r1 * (1 - alpha)) rHT1 ∧
    wordNear (st2.transient.h.get idx).value (alpha * r1 * (1 - 2 * alpha) + alpha * r2)
      (rHT1 + eps2 + rM2 + 2 * ulpHalf limit) ∧
    wordNear (st2.transient.hTemp.get idx).value (alpha * r1 * (1 - 2 * alpha) + alpha * r2)
      (rHT1 + eps2 + rM2 + 2 * ulpHalf limit) := by
  dsimp only
  have h1 := step_active_meta_registers st0 features1 reward1 idx
    hUnique0 hElig0 hAct1 hUnclipped1 hKept1 hNoOvr1
  dsimp only at h1
  set st1 := (st0.step config features1 reward1).1
  have h2 := step_inactive_meta_registers st1 features2 reward2 idx
    hUnique1 hElig1 hInact2 hUnclipped2 hKept2
  dsimp only at h2
  have hZeroNear : wordNear Binary32.zero 0 0 := ⟨by decide, by rw [zero_value]; simp⟩
  have hZeroMul : wordNear ((st0.transient.zDelta.get idx).value.mul Binary32.zero) 0 0 := by
    have hz : ((st0.transient.zDelta.get idx).value.mul Binary32.zero).isZero = true :=
      finite_mul_zero hZDelta0Fin (by decide)
    exact ⟨zero_finite hz, by rw [zero_reads hz]; simp⟩
  have hZeroMulDecay : wordNear (Binary32.zero.mul (config.rule.gamma.mul config.lambda)) 0 0 := by
    have hz : (Binary32.zero.mul (config.rule.gamma.mul config.lambda)).isZero = true :=
      zeroWord_mul_finite (by decide) hDecayFin
    exact ⟨zero_finite hz, by rw [zero_reads hz]; simp⟩
  have hZeroMulSub : wordNear (Binary32.zero.mul
      ((st1.transient.z.get idx).value.sub (st1.transient.zDelta.get idx).value)) 0 0 := by
    have hz : (Binary32.zero.mul
        ((st1.transient.z.get idx).value.sub (st1.transient.zDelta.get idx).value)).isZero = true :=
      zeroWord_mul_finite (by decide) hNearZSub1Fin
    exact ⟨zero_finite hz, by rw [zero_reads hz]; simp⟩
  have hAdd0 := wordNear_add hZeroNear hNearInc1 hLim (by simpa using hCap1)
  have hNextH1Raw := wordNear_sub hAdd0 hZeroMul hLim (by
    have hU := ulpHalf_nonneg limit
    simpa [zero_add, sub_zero, add_zero] using (by linarith [hCapH1] :
      |alpha * r1| + (eps1 + ulpHalf limit) < (2 : ℚ) ^ limit))
  have hNextH1 : wordNear (st1.transient.h.get idx).value (alpha * r1)
      (eps1 + 2 * ulpHalf limit) := by
    simp only [zero_add, sub_zero, add_zero] at hNextH1Raw
    rw [h1.2.2.1, hHTemp0, hVD0]
    refine ⟨hNextH1Raw.1, ?_⟩
    linarith [hNextH1Raw.2]
  have hP1 : wordNear (st1.transient.p.get idx).value (alpha * r1)
      (eps1 + 2 * ulpHalf limit + ulpHalf limit) := by
    rw [h1.2.2.2.1, hP0, ← h1.2.2.1]
    have hP := wordNear_add hZeroMulDecay hNextH1 hLim (by simpa [zero_add] using hCapH1)
    simpa [zero_add] using hP
  have hSub0 : wordNear ((st1.transient.h.get idx).value.sub
      (Binary32.zero.mul
        ((st1.transient.z.get idx).value.sub (st1.transient.zDelta.get idx).value)))
      (alpha * r1) (eps1 + 2 * ulpHalf limit + ulpHalf limit) := by
    simpa [sub_zero, add_zero] using wordNear_sub hNextH1 hZeroMulSub hLim
      (by simpa [sub_zero, add_zero] using hCapH1)
  have hMulH1ZD := wordNear_mul hNextH1 hNearZD1 hLim hCapH1ZD
  have hHT1Eq : alpha * r1 - alpha * r1 * alpha = alpha * r1 * (1 - alpha) := by ring
  have hHT1Raw := wordNear_sub hSub0 hMulH1ZD hLim (by rwa [hHT1Eq])
  have hHT1 : wordNear (st1.transient.hTemp.get idx).value (alpha * r1 * (1 - alpha))
      (eps1 + 2 * ulpHalf limit +
        (|alpha * r1| * epsZ1 + |alpha| * (eps1 + 2 * ulpHalf limit) +
          (eps1 + 2 * ulpHalf limit) * epsZ1 + ulpHalf limit) +
        2 * ulpHalf limit) := by
    rw [h1.2.2.2.2.1, hH0, ← h1.2.2.1, ← h1.2.2.2.2.2.1, ← h1.2.2.2.2.2.2]
    rw [hHT1Eq] at hHT1Raw
    refine ⟨hHT1Raw.1, ?_⟩
    linarith [hHT1Raw.2]
  have hAdd2 := wordNear_add hHT1 hNearInc2 hLim hCapAdd2
  have hMulZD2 := wordNear_mul hNearZD1 hNearVD1 hLim hCapMul2
  have hH2Eq : alpha * r1 * (1 - alpha) + alpha * r2 - alpha * (alpha * r1) =
      alpha * r1 * (1 - 2 * alpha) + alpha * r2 := by ring
  have hNextH2Raw := wordNear_sub hAdd2 hMulZD2 hLim (by rwa [hH2Eq])
  have hNextH2 : wordNear
      (((st1.transient.hTemp.get idx).value.add
        (((reward2.add (config.rule.gamma.mul (st1.linearPrediction features2))).sub
          st1.transient.vOld).mul (st1.transient.zBar.get idx).value)).sub
        ((st1.transient.zDelta.get idx).value.mul st1.transient.vDelta))
      (alpha * r1 * (1 - 2 * alpha) + alpha * r2)
      ((eps1 + 2 * ulpHalf limit +
        (|alpha * r1| * epsZ1 + |alpha| * (eps1 + 2 * ulpHalf limit) +
          (eps1 + 2 * ulpHalf limit) * epsZ1 + ulpHalf limit) +
        2 * ulpHalf limit) + eps2 +
        (|alpha| * epsVD1 + |alpha * r1| * epsZ1 + epsZ1 * epsVD1 + ulpHalf limit) +
        2 * ulpHalf limit) := by
    rw [hH2Eq] at hNextH2Raw
    refine ⟨hNextH2Raw.1, ?_⟩
    linarith [hNextH2Raw.2]
  refine ⟨hP1, hHT1, ?_, ?_⟩
  · rw [h2.2.2.1]
    exact hNextH2
  · rw [h2.2.2.2.1]
    exact hNextH2

private theorem fieldUnits23_step (m : Nat) (hGe : 2 ^ 23 ≤ m) :
    fieldUnits 23 (m + 1) - fieldUnits 23 m = 2 ^ (m / 2 ^ 23 - 1) ∧
    fieldUnits 23 m ≤ fieldUnits 23 (m + 1) := by
  have hPos : 0 < 2 ^ 23 := by decide
  set e := m / 2 ^ 23
  set f := m % 2 ^ 23
  have hePos : 1 ≤ e := by
    have := Nat.div_le_div_right (c := 2 ^ 23) hGe
    simpa [e] using this
  have hfLt : f < 2 ^ 23 := Nat.mod_lt m hPos
  have hDecomp : e * 2 ^ 23 + f = m := by
    dsimp only [e, f]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod m (2 ^ 23)
  have hCur : fieldUnits 23 m = (2 ^ 23 + f) * 2 ^ (e - 1) := by
    rw [← hDecomp, fieldUnits_fields 23 e f hfLt]
    have hNe : e ≠ 0 := by omega
    simp [hNe]
  by_cases hTop : f + 1 < 2 ^ 23
  · have hNext : fieldUnits 23 (m + 1) = (2 ^ 23 + (f + 1)) * 2 ^ (e - 1) := by
      have hEq : e * 2 ^ 23 + (f + 1) = m + 1 := by omega
      rw [← hEq, fieldUnits_fields 23 e (f + 1) hTop]
      have hNe : e ≠ 0 := by omega
      simp [hNe]
    rw [hCur, hNext]
    have hDiff : (2 ^ 23 + (f + 1)) * 2 ^ (e - 1) =
        (2 ^ 23 + f) * 2 ^ (e - 1) + 2 ^ (e - 1) := by ring
    rw [hDiff]
    exact ⟨Nat.add_sub_cancel_left _ _, Nat.le_add_right _ _⟩
  · have hfEq : f = 2 ^ 23 - 1 := by omega
    have hEq : (e + 1) * 2 ^ 23 + 0 = m + 1 := by
      rw [← hDecomp, hfEq]
      ring_nf
    have hNext : fieldUnits 23 (m + 1) = 2 ^ 23 * 2 ^ e := by
      rw [← hEq, fieldUnits_fields 23 (e + 1) 0 hPos]
      simp
    have hPow : 2 ^ e = 2 ^ (e - 1) * 2 := by
      have : e = (e - 1) + 1 := by omega
      conv_lhs => rw [this, Nat.pow_succ]
    rw [hCur, hNext, hfEq, hPow]
    have hDiff : 2 ^ 23 * (2 ^ (e - 1) * 2) =
        (2 ^ 23 + (2 ^ 23 - 1)) * 2 ^ (e - 1) + 2 ^ (e - 1) := by
      have h23 : 2 ^ 23 + (2 ^ 23 - 1) + 1 = 2 ^ 23 * 2 := by decide
      calc
        2 ^ 23 * (2 ^ (e - 1) * 2) = (2 ^ 23 * 2) * 2 ^ (e - 1) := by ring
        _ = (2 ^ 23 + (2 ^ 23 - 1) + 1) * 2 ^ (e - 1) := by rw [← h23]
        _ = (2 ^ 23 + (2 ^ 23 - 1)) * 2 ^ (e - 1) + 2 ^ (e - 1) := by ring
    rw [hDiff]
    exact ⟨Nat.add_sub_cancel_left _ _, Nat.le_add_right _ _⟩

private theorem fieldUnits23_power_of_two (k : Int) (hk : (-126 : Int) ≤ k) :
    let ek := (k + 127).toNat
    (fieldUnits 23 (ek * 2 ^ 23) : ℚ) * (2 : ℚ) ^ (-149 : Int) = (2 : ℚ) ^ k := by
  dsimp only
  set ek := (k + 127).toNat
  have hEk : (ek : Int) = k + 127 := Int.toNat_of_nonneg (by omega)
  have hEkPos : 1 ≤ ek := by omega
  rw [show ek * 2 ^ 23 = ek * 2 ^ 23 + 0 from (Nat.add_zero _).symm,
    fieldUnits_fields 23 ek 0 (by decide)]
  have hNe : ek ≠ 0 := by omega
  simp only [hNe, ↓reduceIte, Nat.add_zero, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← zpow_natCast (2 : ℚ) 23, ← zpow_natCast (2 : ℚ) (ek - 1),
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 1
  omega

private theorem fieldUnits23_gap_of_ge {a b : Nat} (hLt : a < b) (hGe : 2 ^ 23 ≤ a) :
    2 ^ (a / 2 ^ 23 - 1) ≤ fieldUnits 23 b - fieldUnits 23 a := by
  have h1 := fieldUnits23_step a hGe
  have hMono : fieldUnits 23 (a + 1) ≤ fieldUnits 23 b :=
    (fieldUnits_order 23 (a + 1) b).mpr hLt
  omega

private theorem binary32_binade_bounds (w : Binary32) (hw : w.Finite) (k : Int)
    (hk : (-126 : Int) ≤ k) (hLo : (2 : ℚ) ^ k ≤ |numerical32 w|)
    (hHi : |numerical32 w| < (2 : ℚ) ^ (k + 1)) :
    let ek := (k + 127).toNat
    ek * 2 ^ 23 ≤ w.magnitude ∧ w.magnitude < (ek + 1) * 2 ^ 23 ∧
    |numerical32 w| ≤ (2 : ℚ) ^ (k + 1) - (2 : ℚ) ^ (k - 23) := by
  dsimp only
  set ek := (k + 127).toNat
  have hEk : (ek : Int) = k + 127 := Int.toNat_of_nonneg (by omega)
  have hPowK := fieldUnits23_power_of_two k hk
  have hPowK1 : (fieldUnits 23 ((ek + 1) * 2 ^ 23) : ℚ) * (2 : ℚ) ^ (-149 : Int) =
      (2 : ℚ) ^ (k + 1) := by
    have hEq : (k + 1 + 127).toNat = ek + 1 := by omega
    simpa [hEq] using fieldUnits23_power_of_two (k + 1) (by omega)
  rw [numerical32_abs_units w hw] at hLo hHi
  have hPos : (0 : ℚ) < (2 : ℚ) ^ (-149 : Int) := zpow_pos (by norm_num) _
  have hLoFu : fieldUnits 23 (ek * 2 ^ 23) ≤ fieldUnits 23 w.magnitude := by
    rw [← hPowK] at hLo
    exact Nat.cast_le.mp ((mul_le_mul_iff_left₀ hPos).mp hLo)
  have hHiFu : fieldUnits 23 w.magnitude < fieldUnits 23 ((ek + 1) * 2 ^ 23) := by
    rw [← hPowK1] at hHi
    exact Nat.cast_lt.mp ((mul_lt_mul_iff_left₀ hPos).mp hHi)
  have hMagLo : ek * 2 ^ 23 ≤ w.magnitude := (fieldUnits_order 23 _ _).mp hLoFu
  have hMagHi : w.magnitude < (ek + 1) * 2 ^ 23 := by
    by_contra hGe
    have := (fieldUnits_order 23 _ _).mpr (Nat.le_of_not_lt hGe)
    omega
  refine ⟨hMagLo, hMagHi, ?_⟩
  have hPredGe : 2 ^ 23 ≤ w.magnitude := by
    have : 1 ≤ ek := by omega
    have : 1 * 2 ^ 23 ≤ ek * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hDiv : w.magnitude / 2 ^ 23 = ek := by
    have h1 : ek ≤ w.magnitude / 2 ^ 23 := by
      have := Nat.div_le_div_right (c := 2 ^ 23) hMagLo
      simpa using this
    have h2 : w.magnitude / 2 ^ 23 < ek + 1 :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hMagHi)
    omega
  have hGap := fieldUnits23_gap_of_ge hMagHi hPredGe
  rw [hDiv] at hGap
  have hLeFu : fieldUnits 23 w.magnitude + 2 ^ (ek - 1) ≤ fieldUnits 23 ((ek + 1) * 2 ^ 23) := by
    have hMono := (fieldUnits_order 23 _ _).mpr (Nat.le_of_lt hMagHi)
    omega
  have hCast : (fieldUnits 23 w.magnitude : ℚ) + (2 : ℚ) ^ (ek - 1) ≤
      (fieldUnits 23 ((ek + 1) * 2 ^ 23) : ℚ) := by
    exact_mod_cast hLeFu
  have hMul := mul_le_mul_of_nonneg_right hCast hPos.le
  rw [add_mul, hPowK1, ← numerical32_abs_units w hw] at hMul
  have hStep : (2 : ℚ) ^ (ek - 1) * (2 : ℚ) ^ (-149 : Int) = (2 : ℚ) ^ (k - 23) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    congr 1
    omega
  rw [hStep] at hMul
  linarith

private theorem binary32_distinct_gap_inward (w v : Binary32) (hw : w.Finite) (hv : v.Finite)
    (k : Int) (hk : (-125 : Int) ≤ k) (hLo : (2 : ℚ) ^ k ≤ |numerical32 w|)
    (hNe : v.key ≠ w.key) :
    (2 : ℚ) ^ (k - 24) ≤ |numerical32 v - numerical32 w| := by
  set ek := (k + 127).toNat
  have hEk : (ek : Int) = k + 127 := Int.toNat_of_nonneg (by omega)
  have hEk2 : 2 ≤ ek := by omega
  have hPos : (0 : ℚ) < (2 : ℚ) ^ (-149 : Int) := zpow_pos (by norm_num) _
  have hPowK : (fieldUnits 23 (ek * 2 ^ 23) : ℚ) * (2 : ℚ) ^ (-149 : Int) = (2 : ℚ) ^ k :=
    fieldUnits23_power_of_two k (by omega)
  have hMagW : ek * 2 ^ 23 ≤ w.magnitude := by
    rw [numerical32_abs_units w hw, ← hPowK] at hLo
    exact (fieldUnits_order 23 _ _).mp (Nat.cast_le.mp ((mul_le_mul_iff_left₀ hPos).mp hLo))
  by_cases hSameSign : w.negative = v.negative
  · have hMagNe : v.magnitude ≠ w.magnitude := by
      intro hEq
      apply hNe
      simp [Binary32.key_eq_negative, hSameSign, hEq]
    have hAbsDiff : |numerical32 v - numerical32 w| =
        abs (|numerical32 v| - |numerical32 w|) := by
      rw [numerical32_abs_units v hv, numerical32_abs_units w hw,
        numerical32_fieldUnits v hv, numerical32_fieldUnits w hw,
        model_word32_sign, model_word32_sign]
      change |signCoefficient (if v.negative then .negative else .positive) *
          (fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) -
          signCoefficient (if w.negative then .negative else .positive) *
          (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)| = _
      rw [← hSameSign]
      cases w.negative
      · simp only [Bool.false_eq_true, ↓reduceIte, signCoefficient, one_mul]
      · simp only [↓reduceIte, signCoefficient, neg_mul, one_mul]
        rw [show -((fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) -
            -((fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) =
            -(((fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) -
              ((fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int))) by ring, abs_neg]
    rw [hAbsDiff, numerical32_abs_units v hv, numerical32_abs_units w hw, ← sub_mul,
      abs_mul, abs_of_pos hPos]
    rcases lt_or_gt_of_ne hMagNe with hLt | hGt
    · have hEkMul : ek * 2 ^ 23 = (ek - 1) * 2 ^ 23 + 2 ^ 23 := by
        have h1 : (ek - 1 + 1) * 2 ^ 23 = (ek - 1) * 2 ^ 23 + 2 ^ 23 := by ring
        rw [Nat.sub_add_cancel (by omega : 1 ≤ ek)] at h1
        exact h1
      have hPred : (ek - 1) * 2 ^ 23 ≤ ek * 2 ^ 23 - 1 := by
        rw [hEkMul, Nat.add_sub_assoc Nat.one_le_two_pow]
        exact Nat.le_add_right _ _
      have hStep := fieldUnits23_step (ek * 2 ^ 23 - 1) (by
        have : 1 * 2 ^ 23 ≤ (ek - 1) * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
        omega)
      have hDivPred : (ek * 2 ^ 23 - 1) / 2 ^ 23 = ek - 1 := by
        have h1 : ek - 1 ≤ (ek * 2 ^ 23 - 1) / 2 ^ 23 := by
          have := Nat.div_le_div_right (c := 2 ^ 23) hPred
          simpa using this
        have h2 : (ek * 2 ^ 23 - 1) / 2 ^ 23 < ek :=
          Nat.div_lt_of_lt_mul (by
            have : 0 < ek * 2 ^ 23 := Nat.mul_pos (by omega) (Nat.two_pow_pos 23)
            omega)
        omega
      rw [hDivPred] at hStep
      have hSuccEq : (ek * 2 ^ 23 - 1) + 1 = ek * 2 ^ 23 := by
        have : 0 < ek * 2 ^ 23 := Nat.mul_pos (by omega) (Nat.two_pow_pos 23)
        omega
      rw [hSuccEq, show ek - 1 - 1 = ek - 2 by omega] at hStep
      by_cases hVLo : v.magnitude < ek * 2 ^ 23
      · have hVLe : fieldUnits 23 v.magnitude ≤ fieldUnits 23 (ek * 2 ^ 23 - 1) :=
          (fieldUnits_order 23 _ _).mpr (by omega)
        have hWGe : fieldUnits 23 (ek * 2 ^ 23) ≤ fieldUnits 23 w.magnitude :=
          (fieldUnits_order 23 _ _).mpr hMagW
        have hDiffNat : 2 ^ (ek - 2) ≤ fieldUnits 23 w.magnitude - fieldUnits 23 v.magnitude := by
          omega
        have hVLtW : fieldUnits 23 v.magnitude ≤ fieldUnits 23 w.magnitude :=
          (fieldUnits_order 23 _ _).mpr (Nat.le_of_lt hLt)
        have hCast : (2 : ℚ) ^ (ek - 2) ≤
            (fieldUnits 23 w.magnitude : ℚ) - (fieldUnits 23 v.magnitude : ℚ) := by
          have : fieldUnits 23 v.magnitude + 2 ^ (ek - 2) ≤ fieldUnits 23 w.magnitude := by omega
          have hC : (fieldUnits 23 v.magnitude : ℚ) + (2 : ℚ) ^ (ek - 2) ≤
              (fieldUnits 23 w.magnitude : ℚ) := by exact_mod_cast this
          linarith
        have hAbs : (2 : ℚ) ^ (ek - 2) ≤
            |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| := by
          rw [abs_sub_comm, abs_of_nonneg
            (by linarith [hCast, pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) (ek - 2)])]
          exact hCast
        have hPow : (2 : ℚ) ^ (ek - 2) * (2 : ℚ) ^ (-149 : Int) = (2 : ℚ) ^ (k - 24) := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
          congr 1; omega
        calc
          (2 : ℚ) ^ (k - 24) = (2 : ℚ) ^ (ek - 2) * (2 : ℚ) ^ (-149 : Int) := hPow.symm
          _ ≤ |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| *
                (2 : ℚ) ^ (-149 : Int) := mul_le_mul_of_nonneg_right hAbs hPos.le
      · have hVGe : ek * 2 ^ 23 ≤ v.magnitude := Nat.le_of_not_lt hVLo
        have hGap := fieldUnits23_gap_of_ge hLt (by
          have : 1 * 2 ^ 23 ≤ ek * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
          omega)
        have hVDiv : ek ≤ v.magnitude / 2 ^ 23 := by
          have := Nat.div_le_div_right (c := 2 ^ 23) hVGe
          simpa using this
        have hPowLe : 2 ^ (ek - 2) ≤ 2 ^ (v.magnitude / 2 ^ 23 - 1) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hVLtW : fieldUnits 23 v.magnitude ≤ fieldUnits 23 w.magnitude :=
          (fieldUnits_order 23 _ _).mpr (Nat.le_of_lt hLt)
        have hCast : (2 : ℚ) ^ (ek - 2) ≤
            (fieldUnits 23 w.magnitude : ℚ) - (fieldUnits 23 v.magnitude : ℚ) := by
          have : fieldUnits 23 v.magnitude + 2 ^ (ek - 2) ≤ fieldUnits 23 w.magnitude := by omega
          have hC : (fieldUnits 23 v.magnitude : ℚ) + (2 : ℚ) ^ (ek - 2) ≤
              (fieldUnits 23 w.magnitude : ℚ) := by exact_mod_cast this
          linarith
        have hAbs : (2 : ℚ) ^ (ek - 2) ≤
            |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith [pow_nonneg (by norm_num : (0:ℚ)≤2) (ek-2)])]
          exact hCast
        have hPow : (2 : ℚ) ^ (ek - 2) * (2 : ℚ) ^ (-149 : Int) = (2 : ℚ) ^ (k - 24) := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
          congr 1; omega
        calc
          (2 : ℚ) ^ (k - 24) = (2 : ℚ) ^ (ek - 2) * (2 : ℚ) ^ (-149 : Int) := hPow.symm
          _ ≤ |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| *
                (2 : ℚ) ^ (-149 : Int) := mul_le_mul_of_nonneg_right hAbs hPos.le
    · have hGap := fieldUnits23_gap_of_ge hGt (by
        have : 1 * 2 ^ 23 ≤ ek * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
        omega)
      have hWDiv : ek ≤ w.magnitude / 2 ^ 23 := by
        have := Nat.div_le_div_right (c := 2 ^ 23) hMagW
        simpa using this
      have hPowLe : 2 ^ (ek - 2) ≤ 2 ^ (w.magnitude / 2 ^ 23 - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hWLtV : fieldUnits 23 w.magnitude ≤ fieldUnits 23 v.magnitude :=
        (fieldUnits_order 23 _ _).mpr (Nat.le_of_lt hGt)
      have hCast : (2 : ℚ) ^ (ek - 2) ≤
          (fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ) := by
        have : fieldUnits 23 w.magnitude + 2 ^ (ek - 2) ≤ fieldUnits 23 v.magnitude := by omega
        have hC : (fieldUnits 23 w.magnitude : ℚ) + (2 : ℚ) ^ (ek - 2) ≤
            (fieldUnits 23 v.magnitude : ℚ) := by exact_mod_cast this
        linarith
      have hAbs : (2 : ℚ) ^ (ek - 2) ≤
          |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| := by
        rw [abs_of_nonneg (by linarith [pow_nonneg (by norm_num : (0:ℚ)≤2) (ek-2)])]
        exact hCast
      have hPow : (2 : ℚ) ^ (ek - 2) * (2 : ℚ) ^ (-149 : Int) = (2 : ℚ) ^ (k - 24) := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1; omega
      calc
        (2 : ℚ) ^ (k - 24) = (2 : ℚ) ^ (ek - 2) * (2 : ℚ) ^ (-149 : Int) := hPow.symm
        _ ≤ |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| *
              (2 : ℚ) ^ (-149 : Int) := mul_le_mul_of_nonneg_right hAbs hPos.le
  · have hSum : |numerical32 v - numerical32 w| = |numerical32 v| + |numerical32 w| := by
      rw [numerical32_abs_units v hv, numerical32_abs_units w hw,
        numerical32_fieldUnits v hv, numerical32_fieldUnits w hw,
        model_word32_sign, model_word32_sign]
      change |signCoefficient (if v.negative then .negative else .positive) *
          (fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) -
          signCoefficient (if w.negative then .negative else .positive) *
          (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)| = _
      have hNonnegV : 0 ≤ (fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) := by
        positivity
      have hNonnegW : 0 ≤ (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) := by
        positivity
      cases hwS : w.negative <;> cases hvS : v.negative
      · exact absurd (hwS.trans hvS.symm) hSameSign
      · simp only [Bool.false_eq_true, ↓reduceIte, signCoefficient, neg_mul, one_mul]
        rw [show -((fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) -
            (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) =
            -((fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) +
              (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) by ring,
          abs_neg, abs_of_nonneg (add_nonneg hNonnegV hNonnegW)]
      · simp only [Bool.false_eq_true, ↓reduceIte, signCoefficient, neg_mul, one_mul,
          sub_neg_eq_add]
        rw [abs_of_nonneg (add_nonneg hNonnegV hNonnegW)]
      · exact absurd (hwS.trans hvS.symm) hSameSign
    have hPowLe : (2 : ℚ) ^ (k - 24) ≤ (2 : ℚ) ^ k :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [hSum]
    linarith [abs_nonneg (numerical32 v)]

private theorem binary32_distinct_gap_above (w v : Binary32) (hw : w.Finite) (hv : v.Finite)
    (k : Int) (hk : (-125 : Int) ≤ k)
    (hW : (2 : ℚ) ^ k ≤ |numerical32 w|)
    (hCase : (2 : ℚ) ^ k < |numerical32 w| ∨ (2 : ℚ) ^ k ≤ |numerical32 v|)
    (hNe : v.key ≠ w.key) :
    (2 : ℚ) ^ (k - 23) ≤ |numerical32 v - numerical32 w| := by
  set ek := (k + 127).toNat
  have hEk : (ek : Int) = k + 127 := Int.toNat_of_nonneg (by omega)
  have hEk2 : 2 ≤ ek := by omega
  have hPos : (0 : ℚ) < (2 : ℚ) ^ (-149 : Int) := zpow_pos (by norm_num) _
  have hPowK : (fieldUnits 23 (ek * 2 ^ 23) : ℚ) * (2 : ℚ) ^ (-149 : Int) = (2 : ℚ) ^ k :=
    fieldUnits23_power_of_two k (by omega)
  have hMagW : ek * 2 ^ 23 ≤ w.magnitude := by
    rw [numerical32_abs_units w hw, ← hPowK] at hW
    exact (fieldUnits_order 23 _ _).mp (Nat.cast_le.mp ((mul_le_mul_iff_left₀ hPos).mp hW))
  by_cases hSameSign : w.negative = v.negative
  · have hMagNe : v.magnitude ≠ w.magnitude := by
      intro hEq
      apply hNe
      simp [Binary32.key_eq_negative, hSameSign, hEq]
    have hAbsDiff : |numerical32 v - numerical32 w| =
        abs (|numerical32 v| - |numerical32 w|) := by
      rw [numerical32_abs_units v hv, numerical32_abs_units w hw,
        numerical32_fieldUnits v hv, numerical32_fieldUnits w hw,
        model_word32_sign, model_word32_sign]
      change |signCoefficient (if v.negative then .negative else .positive) *
          (fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) -
          signCoefficient (if w.negative then .negative else .positive) *
          (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)| = _
      rw [← hSameSign]
      cases w.negative
      · simp only [Bool.false_eq_true, ↓reduceIte, signCoefficient, one_mul]
      · simp only [↓reduceIte, signCoefficient, neg_mul, one_mul]
        rw [show -((fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) -
            -((fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) =
            -(((fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) -
              ((fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int))) by ring, abs_neg]
    rw [hAbsDiff, numerical32_abs_units v hv, numerical32_abs_units w hw, ← sub_mul,
      abs_mul, abs_of_pos hPos]
    have hPow : (2 : ℚ) ^ (ek - 1) * (2 : ℚ) ^ (-149 : Int) = (2 : ℚ) ^ (k - 23) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      congr 1; omega
    rcases lt_or_gt_of_ne hMagNe with hLt | hGt
    · have hDiffNat : 2 ^ (ek - 1) ≤ fieldUnits 23 w.magnitude - fieldUnits 23 v.magnitude := by
        rcases hCase with hWStrict | hVGeQ
        · have hMagWGt : ek * 2 ^ 23 < w.magnitude := by
            rw [numerical32_abs_units w hw, ← hPowK] at hWStrict
            have hFuLt := Nat.cast_lt.mp ((mul_lt_mul_iff_left₀ hPos).mp hWStrict)
            by_contra hLe
            have := (fieldUnits_order 23 _ _).mpr (Nat.le_of_not_lt hLe)
            omega
          by_cases hVGe : ek * 2 ^ 23 ≤ v.magnitude
          · have hGap := fieldUnits23_gap_of_ge hLt (by
              have : 1 * 2 ^ 23 ≤ ek * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
              omega)
            have hVDiv : ek ≤ v.magnitude / 2 ^ 23 := by
              have := Nat.div_le_div_right (c := 2 ^ 23) hVGe
              simpa using this
            have hPowLe : 2 ^ (ek - 1) ≤ 2 ^ (v.magnitude / 2 ^ 23 - 1) :=
              Nat.pow_le_pow_right (by decide) (by omega)
            omega
          · have hVLe : fieldUnits 23 v.magnitude ≤ fieldUnits 23 (ek * 2 ^ 23) :=
              (fieldUnits_order 23 _ _).mpr (Nat.le_of_lt (Nat.lt_of_not_ge hVGe))
            have hGap := fieldUnits23_gap_of_ge hMagWGt (by
              have : 1 * 2 ^ 23 ≤ ek * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
              omega)
            have hEDiv : (ek * 2 ^ 23) / 2 ^ 23 = ek := by simp
            rw [hEDiv] at hGap
            omega
        · have hMagV : ek * 2 ^ 23 ≤ v.magnitude := by
            rw [numerical32_abs_units v hv, ← hPowK] at hVGeQ
            exact (fieldUnits_order 23 _ _).mp
              (Nat.cast_le.mp ((mul_le_mul_iff_left₀ hPos).mp hVGeQ))
          have hGap := fieldUnits23_gap_of_ge hLt (by
            have : 1 * 2 ^ 23 ≤ ek * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
            omega)
          have hVDiv : ek ≤ v.magnitude / 2 ^ 23 := by
            have := Nat.div_le_div_right (c := 2 ^ 23) hMagV
            simpa using this
          have hPowLe : 2 ^ (ek - 1) ≤ 2 ^ (v.magnitude / 2 ^ 23 - 1) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          omega
      have hVLtW : fieldUnits 23 v.magnitude ≤ fieldUnits 23 w.magnitude :=
        (fieldUnits_order 23 _ _).mpr (Nat.le_of_lt hLt)
      have hCast : (2 : ℚ) ^ (ek - 1) ≤
          (fieldUnits 23 w.magnitude : ℚ) - (fieldUnits 23 v.magnitude : ℚ) := by
        have : fieldUnits 23 v.magnitude + 2 ^ (ek - 1) ≤ fieldUnits 23 w.magnitude := by omega
        have hC : (fieldUnits 23 v.magnitude : ℚ) + (2 : ℚ) ^ (ek - 1) ≤
            (fieldUnits 23 w.magnitude : ℚ) := by exact_mod_cast this
        linarith
      have hAbs : (2 : ℚ) ^ (ek - 1) ≤
          |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [pow_nonneg (by norm_num : (0:ℚ)≤2) (ek-1)])]
        exact hCast
      calc
        (2 : ℚ) ^ (k - 23) = (2 : ℚ) ^ (ek - 1) * (2 : ℚ) ^ (-149 : Int) := hPow.symm
        _ ≤ |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| *
              (2 : ℚ) ^ (-149 : Int) := mul_le_mul_of_nonneg_right hAbs hPos.le
    · have hGap := fieldUnits23_gap_of_ge hGt (by
        have : 1 * 2 ^ 23 ≤ ek * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
        omega)
      have hWDiv : ek ≤ w.magnitude / 2 ^ 23 := by
        have := Nat.div_le_div_right (c := 2 ^ 23) hMagW
        simpa using this
      have hPowLe : 2 ^ (ek - 1) ≤ 2 ^ (w.magnitude / 2 ^ 23 - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hWLtV : fieldUnits 23 w.magnitude ≤ fieldUnits 23 v.magnitude :=
        (fieldUnits_order 23 _ _).mpr (Nat.le_of_lt hGt)
      have hCast : (2 : ℚ) ^ (ek - 1) ≤
          (fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ) := by
        have : fieldUnits 23 w.magnitude + 2 ^ (ek - 1) ≤ fieldUnits 23 v.magnitude := by omega
        have hC : (fieldUnits 23 w.magnitude : ℚ) + (2 : ℚ) ^ (ek - 1) ≤
            (fieldUnits 23 v.magnitude : ℚ) := by exact_mod_cast this
        linarith
      have hAbs : (2 : ℚ) ^ (ek - 1) ≤
          |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| := by
        rw [abs_of_nonneg (by linarith [pow_nonneg (by norm_num : (0:ℚ)≤2) (ek-1)])]
        exact hCast
      calc
        (2 : ℚ) ^ (k - 23) = (2 : ℚ) ^ (ek - 1) * (2 : ℚ) ^ (-149 : Int) := hPow.symm
        _ ≤ |(fieldUnits 23 v.magnitude : ℚ) - (fieldUnits 23 w.magnitude : ℚ)| *
              (2 : ℚ) ^ (-149 : Int) := mul_le_mul_of_nonneg_right hAbs hPos.le
  · have hSum : |numerical32 v - numerical32 w| = |numerical32 v| + |numerical32 w| := by
      rw [numerical32_abs_units v hv, numerical32_abs_units w hw,
        numerical32_fieldUnits v hv, numerical32_fieldUnits w hw,
        model_word32_sign, model_word32_sign]
      change |signCoefficient (if v.negative then .negative else .positive) *
          (fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) -
          signCoefficient (if w.negative then .negative else .positive) *
          (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)| = _
      have hNonnegV : 0 ≤ (fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) := by
        positivity
      have hNonnegW : 0 ≤ (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) := by
        positivity
      cases hwS : w.negative <;> cases hvS : v.negative
      · exact absurd (hwS.trans hvS.symm) hSameSign
      · simp only [Bool.false_eq_true, ↓reduceIte, signCoefficient, neg_mul, one_mul]
        rw [show -((fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) -
            (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) =
            -((fieldUnits 23 v.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int) +
              (fieldUnits 23 w.magnitude : ℚ) * (2 : ℚ) ^ (-149 : Int)) by ring,
          abs_neg, abs_of_nonneg (add_nonneg hNonnegV hNonnegW)]
      · simp only [Bool.false_eq_true, ↓reduceIte, signCoefficient, neg_mul, one_mul,
          sub_neg_eq_add]
        rw [abs_of_nonneg (add_nonneg hNonnegV hNonnegW)]
      · exact absurd (hwS.trans hvS.symm) hSameSign
    have hPowLe : (2 : ℚ) ^ (k - 23) ≤ (2 : ℚ) ^ k :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [hSum]
    linarith [abs_nonneg (numerical32 v)]

theorem binary32_add_absorbs_inward (w dw : Binary32) (hw : w.Finite) (hdw : dw.Finite)
    (k : Int) (hkLo : (-125 : Int) ≤ k) (hkHi : k ≤ 32)
    (hWLo : (2 : ℚ) ^ k ≤ |numerical32 w|) (hWHi : |numerical32 w| < (2 : ℚ) ^ (k + 1))
    (hDW : |numerical32 dw| < (2 : ℚ) ^ (k - 25)) :
    (w.add dw).Finite ∧ (w.add dw).key = w.key ∧ numerical32 (w.add dw) = numerical32 w := by
  have hBin := binary32_binade_bounds w hw k (by omega) hWLo hWHi
  have hPow25 : (2 : ℚ) ^ (k - 25) * 2 = (2 : ℚ) ^ (k - 24) := by
    calc
      (2 : ℚ) ^ (k - 25) * 2 = (2 : ℚ) ^ (k - 25) * (2 : ℚ) ^ (1 : Int) := by norm_num
      _ = (2 : ℚ) ^ (k - 24) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1; omega
  have hPow24 : (2 : ℚ) ^ (k - 24) * 2 = (2 : ℚ) ^ (k - 23) := by
    calc
      (2 : ℚ) ^ (k - 24) * 2 = (2 : ℚ) ^ (k - 24) * (2 : ℚ) ^ (1 : Int) := by norm_num
      _ = (2 : ℚ) ^ (k - 23) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1; omega
  have hPowPos25 : (0 : ℚ) < (2 : ℚ) ^ (k - 25) := zpow_pos (by norm_num) _
  by_cases hExactZero : numerical32 dw = 0
  · have hSumBd : |numerical32 w + numerical32 dw| ≤ 8589934592 := by
      have hP : (2 : ℚ) ^ (k + 1) ≤ 8589934592 := by
        have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega : k + 1 ≤ 33)
        norm_num at h
        exact h
      rw [hExactZero, add_zero]
      linarith
    have hRnd := binary32_rounded_add w dw hw hdw hSumBd
    rw [hExactZero, add_zero] at hRnd
    have hEq := rounded_unique hRnd.2 (binary32_rounded_exact w hw)
    have hKey : (w.add dw).key = w.key :=
      le_antisymm ((numerical32_order _ _ hRnd.1 hw).mp hEq.le)
        ((numerical32_order _ _ hw hRnd.1).mp hEq.symm.le)
    exact ⟨hRnd.1, hKey, hEq⟩
  · by_cases hBelow : |numerical32 w + numerical32 dw| < (2 : ℚ) ^ k
    · have hOp := binary32_add_finite_strict_error w dw hw hdw k (by omega) hBelow
      have hMax : max (k - 24) (-149) = k - 24 := by omega
      rw [hMax] at hOp
      have hHalf : (2 : ℚ) ^ (k - 24) / 2 = (2 : ℚ) ^ (k - 25) := by linarith [hPow25]
      have hDist : |numerical32 (w.add dw) - numerical32 w| < (2 : ℚ) ^ (k - 24) := by
        have h1 : numerical32 (w.add dw) - numerical32 w =
            (numerical32 (w.add dw) - (numerical32 w + numerical32 dw)) + numerical32 dw := by ring
        have h2 := abs_add_le (numerical32 (w.add dw) - (numerical32 w + numerical32 dw))
          (numerical32 dw)
        rw [← h1] at h2
        linarith [hOp.2, hHalf, hDW, hPow25]
      have hKey : (w.add dw).key = w.key := by
        by_contra hNe
        have hGap := binary32_distinct_gap_inward w (w.add dw) hw hOp.1 k hkLo hWLo hNe
        linarith
      exact ⟨hOp.1, hKey, le_antisymm
        ((numerical32_order _ _ hOp.1 hw).mpr hKey.le)
        ((numerical32_order _ _ hw hOp.1).mpr hKey.symm.le)⟩
    · have hSumLt : |numerical32 w + numerical32 dw| < (2 : ℚ) ^ (k + 1) := by
        have hTri := abs_add_le (numerical32 w) (numerical32 dw)
        linarith [hBin.2.2, hDW, hPow25, hPow24]
      have hOp := binary32_add_finite_strict_error w dw hw hdw (k + 1) (by omega) hSumLt
      have hMax : max (k + 1 - 24) (-149) = k - 23 := by omega
      rw [hMax] at hOp
      have hHalf : (2 : ℚ) ^ (k - 23) / 2 = (2 : ℚ) ^ (k - 24) := by linarith [hPow24]
      have hDist : |numerical32 (w.add dw) - numerical32 w| < (2 : ℚ) ^ (k - 23) := by
        have h1 : numerical32 (w.add dw) - numerical32 w =
            (numerical32 (w.add dw) - (numerical32 w + numerical32 dw)) + numerical32 dw := by ring
        have h2 := abs_add_le (numerical32 (w.add dw) - (numerical32 w + numerical32 dw))
          (numerical32 dw)
        rw [← h1] at h2
        linarith [hOp.2, hHalf, hDW, hPow25, hPow24]
      have hKey : (w.add dw).key = w.key := by
        by_contra hNe
        by_cases hResGe : (2 : ℚ) ^ k ≤ |numerical32 (w.add dw)|
        · have hGap := binary32_distinct_gap_above w (w.add dw) hw hOp.1 k hkLo hWLo
            (Or.inr hResGe) hNe
          linarith
        · by_cases hWStrict : (2 : ℚ) ^ k < |numerical32 w|
          · have hGap := binary32_distinct_gap_above w (w.add dw) hw hOp.1 k hkLo hWLo
              (Or.inl hWStrict) hNe
            linarith
          · have hWEq : |numerical32 w| = (2 : ℚ) ^ k := le_antisymm (le_of_not_gt hWStrict) hWLo
            have hSumStrict : (2 : ℚ) ^ k < |numerical32 w + numerical32 dw| := by
              have hGe : (2 : ℚ) ^ k ≤ |numerical32 w + numerical32 dw| := le_of_not_gt hBelow
              by_contra hNotGt
              have hEq : |numerical32 w + numerical32 dw| = (2 : ℚ) ^ k :=
                le_antisymm (le_of_not_gt hNotGt) hGe
              have hPow25Lt : (2 : ℚ) ^ (k - 25) < (2 : ℚ) ^ k :=
                zpow_lt_zpow_right₀ (by norm_num) (by omega)
              rcases le_or_gt 0 (numerical32 w) with hWNonneg | hWNeg
              · rw [abs_of_nonneg hWNonneg] at hWEq
                have hPosSum : 0 < numerical32 w + numerical32 dw := by
                  have h1 := (abs_lt.mp hDW).1
                  linarith
                rw [abs_of_pos hPosSum] at hEq
                exact hExactZero (by linarith)
              · rw [abs_of_neg hWNeg] at hWEq
                have hNegSum : numerical32 w + numerical32 dw < 0 := by
                  have h1 := (abs_lt.mp hDW).2
                  linarith
                rw [abs_of_neg hNegSum] at hEq
                exact hExactZero (by linarith)
            have hResBelow : |numerical32 (w.add dw)| ≤ (2 : ℚ) ^ k - (2 : ℚ) ^ (k - 24) := by
              have hResLt : |numerical32 (w.add dw)| < (2 : ℚ) ^ k := lt_of_not_ge hResGe
              by_cases hHalfGe : (2 : ℚ) ^ (k - 1) ≤ |numerical32 (w.add dw)|
              · have hB := binary32_binade_bounds (w.add dw) hOp.1 (k - 1) (by omega) hHalfGe
                  (by simpa [sub_add_cancel] using hResLt)
                simpa [sub_add_cancel, show k - 1 - 23 = k - 24 by omega] using hB.2.2
              · have hPowLt : (2 : ℚ) ^ (k - 1) ≤ (2 : ℚ) ^ k - (2 : ℚ) ^ (k - 24) := by
                  have hP1 : (2 : ℚ) ^ (k - 1) * 2 = (2 : ℚ) ^ k := by
                    calc
                      (2 : ℚ) ^ (k - 1) * 2 = (2 : ℚ) ^ (k - 1) * (2 : ℚ) ^ (1 : Int) := by norm_num
                      _ = (2 : ℚ) ^ k := by
                        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
                        congr 1; omega
                  have hP2 : (2 : ℚ) ^ (k - 24) < (2 : ℚ) ^ (k - 1) :=
                    zpow_lt_zpow_right₀ (by norm_num) (by omega)
                  linarith
                linarith [lt_of_not_ge hHalfGe]
            have hRevTri := abs_sub_abs_le_abs_sub (numerical32 w + numerical32 dw)
              (numerical32 (w.add dw))
            rw [abs_sub_comm] at hRevTri
            have hGtErr : (2 : ℚ) ^ (k - 24) <
                |numerical32 (w.add dw) - (numerical32 w + numerical32 dw)| := by
              have := le_abs_self (|numerical32 w + numerical32 dw| - |numerical32 (w.add dw)|)
              linarith
            linarith [hOp.2, hHalf]
      exact ⟨hOp.1, hKey, le_antisymm
        ((numerical32_order _ _ hOp.1 hw).mpr hKey.le)
        ((numerical32_order _ _ hw hOp.1).mpr hKey.symm.le)⟩

theorem binary32_add_absorbs_interior (w dw : Binary32) (hw : w.Finite) (hdw : dw.Finite)
    (k : Int) (hkLo : (-125 : Int) ≤ k) (hkHi : k ≤ 32)
    (hWLo : (2 : ℚ) ^ k < |numerical32 w|) (hWHi : |numerical32 w| < (2 : ℚ) ^ (k + 1))
    (hDW : |numerical32 dw| < (2 : ℚ) ^ (k - 24)) :
    (w.add dw).Finite ∧ (w.add dw).key = w.key ∧ numerical32 (w.add dw) = numerical32 w := by
  have hBin := binary32_binade_bounds w hw k (by omega) hWLo.le hWHi
  have hPow24 : (2 : ℚ) ^ (k - 24) * 2 = (2 : ℚ) ^ (k - 23) := by
    calc
      (2 : ℚ) ^ (k - 24) * 2 = (2 : ℚ) ^ (k - 24) * (2 : ℚ) ^ (1 : Int) := by norm_num
      _ = (2 : ℚ) ^ (k - 23) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1; omega
  have hPowPos24 : (0 : ℚ) < (2 : ℚ) ^ (k - 24) := zpow_pos (by norm_num) _
  have hSumLt : |numerical32 w + numerical32 dw| < (2 : ℚ) ^ (k + 1) := by
    have hTri := abs_add_le (numerical32 w) (numerical32 dw)
    linarith [hBin.2.2, hDW, hPow24]
  have hOp := binary32_add_finite_strict_error w dw hw hdw (k + 1) (by omega) hSumLt
  have hMax : max (k + 1 - 24) (-149) = k - 23 := by omega
  rw [hMax] at hOp
  have hHalf : (2 : ℚ) ^ (k - 23) / 2 = (2 : ℚ) ^ (k - 24) := by linarith [hPow24]
  have hDist : |numerical32 (w.add dw) - numerical32 w| < (2 : ℚ) ^ (k - 23) := by
    have h1 : numerical32 (w.add dw) - numerical32 w =
        (numerical32 (w.add dw) - (numerical32 w + numerical32 dw)) + numerical32 dw := by ring
    have h2 := abs_add_le (numerical32 (w.add dw) - (numerical32 w + numerical32 dw))
      (numerical32 dw)
    rw [← h1] at h2
    linarith [hOp.2, hHalf, hDW, hPow24]
  have hKey : (w.add dw).key = w.key := by
    by_contra hNe
    have hGap := binary32_distinct_gap_above w (w.add dw) hw hOp.1 k hkLo hWLo.le
      (Or.inl hWLo) hNe
    linarith
  exact ⟨hOp.1, hKey, le_antisymm
    ((numerical32_order _ _ hOp.1 hw).mpr hKey.le)
    ((numerical32_order _ _ hw hOp.1).mpr hKey.symm.le)⟩

theorem firstLoopElement_weight_absorbed {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) (k : Int) (hkLo : (-125 : Int) ≤ k) (hkHi : k ≤ 32)
    (hWLo : (2 : ℚ) ^ k ≤ |numerical32 (state.weights.get idx).value|)
    (hWHi : |numerical32 (state.weights.get idx).value| < (2 : ℚ) ^ (k + 1))
    (hDWFin : ((delta.mul (state.transient.z.get idx).value).sub
      ((state.transient.zDelta.get idx).value.mul vDelta)).Finite)
    (hDW : |numerical32 ((delta.mul (state.transient.z.get idx).value).sub
      ((state.transient.zDelta.get idx).value.mul vDelta))| < (2 : ℚ) ^ (k - 25)) :
    let next := (state.firstLoopElement idx delta vDelta decay).1
    (next.weights.get idx).value.key = (state.weights.get idx).value.key ∧
    numerical32 (next.weights.get idx).value = numerical32 (state.weights.get idx).value := by
  dsimp only
  have hLegal := weight_legal (state.weights.get idx)
  set w := (state.weights.get idx).value
  set dw := (delta.mul (state.transient.z.get idx).value).sub
    ((state.transient.zDelta.get idx).value.mul vDelta)
  have hAbs := binary32_add_absorbs_inward w dw hLegal.1 hDWFin k hkLo hkHi hWLo hWHi hDW
  have hRawLegal : config.rule.domain.range.Contains (w.add dw) :=
    ⟨hAbs.1, hAbs.2.1 ▸ hLegal.2.1, hAbs.2.1 ▸ hLegal.2.2⟩
  have hProj : (Weight.project config.rule (w.add dw)).value = w.add dw := by
    rw [Weight.project_eq]
    exact config.rule.domain.symmetric_project_identity (w.add dw) hRawLegal
  have hUpd : (((state.firstLoopElement idx delta vDelta decay).1).weights.get idx).value =
      w.add dw := by
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self]
    exact hProj
  rw [hUpd]
  exact ⟨hAbs.2.1, hAbs.2.2⟩

theorem etaMin_value (config : Config) :
    numerical32 config.etaMin = 14411519 * (2 : ℚ) ^ (-57 : Int) := by
  unfold Config.etaMin
  change (1 : ℚ) * 14411519 * (2 : ℚ) ^ (-57 : Int) = _
  ring

theorem etaMin_below_absorption_threshold (config : Config) :
    18 * numerical32 config.etaMin < (2 : ℚ) ^ (-29 : Int) ∧
    37 * numerical32 config.etaMin < (2 : ℚ) ^ (-28 : Int) := by
  rw [etaMin_value]
  norm_num

theorem cold_start_overshoot_cliff_binary32 (criterion : Acorn.Features.Criterion) :
    let cfg := criterion.config .control
    1999 * numerical32 stepWord < numerical32 cfg.eta ∧
    numerical32 cfg.eta < 2000 * numerical32 stepWord ∧
    2000 * numerical32 stepWord - numerical32 cfg.eta = 8896 * (2 : ℚ) ^ (-38 : Int) ∧
    (∀ k ≤ 1999,
      cfg.eta.less (Binary32.sumFrom .zero (List.replicate k stepWord)) = false) ∧
    (∀ k, 2001 ≤ k → k ≤ FeatureConstants.defaultWeightSpace →
      cfg.eta.less (Binary32.sumFrom .zero (List.replicate k stepWord)) = true) := by
  dsimp only
  have hEtaVal : numerical32 (criterion.config .control).eta =
      13421773 * (2 : ℚ) ^ (-27 : Int) := by
    cases criterion <;> (change (1 : ℚ) * 13421773 * (2 : ℚ) ^ (-27 : Int) = _; ring)
  have hEtaFin : (criterion.config .control).eta.Finite := by cases criterion <;> decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [step_value, hEtaVal]; norm_num
  · rw [step_value, hEtaVal]; norm_num
  · rw [step_value, hEtaVal]; norm_num
  · intro k hk
    have hRate := repeatSum_rate criterion k hk
    change (criterion.config .control).eta.less (repeatSum stepWord k) = false
    rw [numerical32_less _ _ hEtaFin hRate.1.1, decide_eq_false_iff_not]
    linarith [hRate.2]
  · intro k hkLo hkHi
    have hXs : ∀ x ∈ List.replicate k stepWord, x.Finite ∧ 0 ≤ numerical32 x := by
      intro x hx
      rw [List.mem_replicate.mp hx |>.2]
      exact ⟨small_step.1, step_nonneg⟩
    have hMapSum : ((List.replicate k stepWord).map numerical32).sum =
        (k : ℚ) * numerical32 stepWord := by
      rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
    by_cases hMid : k ≤ 2499
    · have hBound := sumFrom_nonneg_bound (List.replicate k stepWord) hXs
        (2499 * numerical32 stepWord) (-3) (by omega)
        (by
          rw [hMapSum]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hMid) step_nonneg)
        (by
          rw [List.length_replicate, step_value]
          have hKLe : (k : ℚ) ≤ 2499 := by exact_mod_cast hMid
          norm_num
          linarith)
      rw [numerical32_less _ _ hEtaFin hBound.1, decide_eq_true_eq]
      have hLow := (abs_le.mp hBound.2.2).1
      rw [hMapSum, List.length_replicate, step_value] at hLow
      have hKGe : (2001 : ℚ) ≤ k := by exact_mod_cast hkLo
      rw [hEtaVal]
      norm_num at hLow ⊢
      linarith
    · have hKGe : (2500 : ℚ) ≤ k := by exact_mod_cast (show 2500 ≤ k by omega)
      have hKLe : (k : ℚ) ≤ 16384 := by
        simpa [FeatureConstants.defaultWeightSpace] using
          (show (k : ℚ) ≤ FeatureConstants.defaultWeightSpace by exact_mod_cast hkHi)
      have hBound := sumFrom_nonneg_bound (List.replicate k stepWord) hXs
        (16384 * numerical32 stepWord) 0 (by omega)
        (by
          rw [hMapSum]
          exact mul_le_mul_of_nonneg_right hKLe step_nonneg)
        (by
          rw [List.length_replicate, step_value]
          norm_num
          linarith)
      rw [numerical32_less _ _ hEtaFin hBound.1, decide_eq_true_eq]
      have hLow := (abs_le.mp hBound.2.2).1
      rw [hMapSum, List.length_replicate, step_value] at hLow
      rw [hEtaVal]
      norm_num at hLow ⊢
      linarith

end AcornVerif.CurrentMetaGradient
