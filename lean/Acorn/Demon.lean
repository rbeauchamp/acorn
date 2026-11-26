import Acorn.FeatureReferences
import Acorn.SignalValues

namespace Acorn.Features

class Signal (S Obs Res : Type) extends Provenance S where
  discount : S → Discount
  eval : S → Obs → Res → Binary32

structure Demon {S Obs Res : Type} [Signal S Obs Res] (signal : S) (dimension : Dimension) where
  learner : Managed ⟨.demon, .discounted (Signal.discount (Obs := Obs) (Res := Res) signal)⟩ dimension

def Demon.initial {S Obs Res : Type} [Signal S Obs Res] (signal : S) (dimension : Dimension) :
    Demon (Obs := Obs) (Res := Res) signal dimension := ⟨Managed.initial _ _⟩

structure DemonOutput (discount : Discount) where
  cumulant : Binary32
  prediction : Prediction discount
  error : Binary32

def Demon.step {S Obs Res : Type} [Signal S Obs Res] {signal : S} {dimension : Dimension}
    (demon : Demon (Obs := Obs) (Res := Res) signal dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Obs) (res : Res) :
    Demon (Obs := Obs) (Res := Res) signal dimension ×
      DemonOutput (Signal.discount (Obs := Obs) (Res := Res) signal) :=
  let reward := Signal.eval signal obs res
  let result := demon.learner.state.step _ features reward
  (⟨⟨result.1, false, .transition (.step features reward) trivial demon.learner.admitted⟩⟩,
    ⟨reward, Prediction.project _ result.2.value, result.2.error⟩)

def Demon.prediction {S Obs Res : Type} [Signal S Obs Res] {signal : S} {dimension : Dimension}
    (demon : Demon (Obs := Obs) (Res := Res) signal dimension)
    (features : SwiftTd.ActiveSet dimension) : Prediction (Signal.discount (Obs := Obs) (Res := Res) signal) :=
  Prediction.project _ (demon.learner.state.linearPrediction features)

structure DemonBankOutput (dimension : Dimension) (discounts : List Discount) where
  bank : DemonBank dimension discounts
  predictions : PredictionCache discounts
  errors : Vector Binary32 discounts.length
  cumulants : Vector Binary32 discounts.length

def DemonBank.stepCosted {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (rewards : Cumulants discounts) : Costed (DemonBankOutput dimension discounts) :=
  match bank, rewards with
  | .nil, .nil => Costed.op .visit ⟨.nil, .nil, #v[], #v[]⟩
  | .cons learner rest, .cons _origin reward rewards => Costed.charge .visit do
    let result ← Costed.attach (learner.state.stepCosted _ features reward)
    let next ← rest.stepCosted features rewards
    let bank := DemonBank.cons ⟨result.val.1, false, by
      rw [result.property]
      exact .transition (.step features reward) trivial learner.admitted⟩ next.bank
    let predictions := PredictionCache.cons (Prediction.project _ result.val.2.value)
      next.predictions
    let error := result.val.2.error.abs
    Costed.charge .demonOutput do
      let errors ← Costed.prepend error next.errors
      let cumulants ← Costed.prepend reward next.cumulants
      Costed.op .demonClose ⟨bank, predictions, errors, cumulants⟩

def DemonBank.step {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (rewards : Cumulants discounts) : DemonBankOutput dimension discounts :=
  (bank.stepCosted features rewards).val

theorem DemonBank.step_def {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (rewards : Cumulants discounts) :
    bank.step features rewards =
      match bank, rewards with
      | .nil, .nil => ⟨.nil, .nil, #v[], #v[]⟩
      | .cons learner rest, .cons _origin reward rewards =>
        let result := learner.state.step _ features reward
        let next := rest.step features rewards
        ⟨.cons ⟨result.1, false, .transition (.step features reward) trivial learner.admitted⟩
            next.bank,
          .cons (Prediction.project _ result.2.value) next.predictions,
          (#v[result.2.error.abs] ++ next.errors).cast (by simp [Nat.add_comm]),
          (#v[reward] ++ next.cumulants).cast (by simp [Nat.add_comm])⟩ := by
  cases bank <;> cases rewards <;> rfl

theorem Demon.step_prediction_legal {S Obs Res : Type} [Signal S Obs Res]
    {signal : S} {dimension : Dimension} (demon : Demon (Obs := Obs) (Res := Res) signal dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Obs) (res : Res) :
    (Signal.discount (Obs := Obs) (Res := Res) signal).predictionRange.Contains
      (demon.step features obs res).2.prediction.value :=
  (demon.step features obs res).2.prediction.legal

theorem DemonBank.step_feedback_length {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (rewards : Cumulants discounts) :
    (bank.step features rewards).predictions.words.length = discounts.length :=
  (bank.step features rewards).predictions.length

end Acorn.Features
