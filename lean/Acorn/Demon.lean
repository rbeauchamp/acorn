/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureReferences
import Acorn.Provenance

/-!
# On-policy prediction and recursive feedback storage

Sutton, Modayil et al., *Horde: A Scalable Real-Time Architecture for Learning
Knowledge from Unsupervised Sensorimotor Interaction*, AAMAS (2011), pp. 761–768,
p. 764, describes demons and inter-demon questions. Acorn's PAR-3 specialization
uses current on-policy SwiftTD, constant discounts and predictions as subsequent
controller features. It does not establish the paper's off-policy convergence.
-/
namespace Acorn.Features

/-- A signal family must declare its origin before entering the prediction core. -/
class Signal (S Obs Res : Type) extends Provenance S where
  /-- Immutable horizon of each question. -/
  discount : S → Discount
  /-- Raw scalar cumulant, retaining the standalone signal domain. -/
  eval : S → Obs → Res → Binary32

/-- A single demon's storage is indexed by its immutable signal. -/
structure Demon {S Obs Res : Type} [Signal S Obs Res] (signal : S) (dimension : Dimension) where
  /-- The discount used by every learner write is derived from the signal. -/
  learner : Managed ⟨.demon, .discounted (Signal.discount (Obs := Obs) (Res := Res) signal)⟩ dimension

/-- Signal-indexed initialization cannot pair a learner with a different horizon. -/
def Demon.initial {S Obs Res : Type} [Signal S Obs Res] (signal : S) (dimension : Dimension) :
    Demon (Obs := Obs) (Res := Res) signal dimension := ⟨Managed.initial _ _⟩

/-- One observed cumulant, projected prediction and raw TD error. -/
structure DemonOutput (discount : Discount) where
  /-- Evaluate the signal exactly once per transition. -/
  cumulant : Binary32
  /-- Projected pre-update prediction returned by the current learner step. -/
  prediction : Prediction discount
  /-- Raw TD error, not a bounded-state claim. -/
  error : Binary32

/-- The exact current learner observation and update, with no second signal evaluation. -/
def Demon.step {S Obs Res : Type} [Signal S Obs Res] {signal : S} {dimension : Dimension}
    (demon : Demon (Obs := Obs) (Res := Res) signal dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Obs) (res : Res) :
    Demon (Obs := Obs) (Res := Res) signal dimension ×
      DemonOutput (Signal.discount (Obs := Obs) (Res := Res) signal) :=
  let reward := Signal.eval signal obs res
  let result := demon.learner.state.step _ features reward
  (⟨⟨result.1, false, .transition (.step features reward) trivial demon.learner.admitted⟩⟩,
    ⟨reward, Prediction.project _ result.2.value, result.2.error⟩)

/-- Observation uses the same ordered sum and immutable projection horizon. -/
def Demon.prediction {S Obs Res : Type} [Signal S Obs Res] {signal : S} {dimension : Dimension}
    (demon : Demon (Obs := Obs) (Res := Res) signal dimension)
    (features : SwiftTd.ActiveSet dimension) : Prediction (Signal.discount (Obs := Obs) (Res := Res) signal) :=
  Prediction.project _ (demon.learner.state.linearPrediction features)

/-- A bank input has exactly one raw cumulant per immutable discount slot. -/
inductive Cumulants : List Discount → Type where
  /-- Empty tail. -/
  | nil : Cumulants []
  /-- One raw signal value with its mandatory declared origin, in channel order. -/
  | cons {discount : Discount} {rest : List Discount} (origin : Option Departure)
      (value : Binary32) (tail : Cumulants rest) : Cumulants (discount :: rest)

/-- One complete prediction update retains the same heterogeneous bank layout. -/
structure DemonBankOutput (dimension : Dimension) (discounts : List Discount) where
  /-- All updated learners, in canonical order. -/
  bank : DemonBank dimension discounts
  /-- Returned projected pre-update values become the next encoding's feedback. -/
  predictions : PredictionCache discounts
  /-- Absolute raw TD errors, one per slot. -/
  errors : Vector Binary32 discounts.length
  /-- Evaluated cumulants, one per slot. -/
  cumulants : Vector Binary32 discounts.length

/-- Update each prediction learner once through the same managed entry. -/
def DemonBank.step {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (rewards : Cumulants discounts) : DemonBankOutput dimension discounts :=
  match bank, rewards with
  | .nil, .nil => ⟨.nil, .nil, #v[], #v[]⟩
  | .cons learner rest, .cons _origin reward rewards =>
    let result := learner.state.step _ features reward
    let next := rest.step features rewards
    ⟨.cons ⟨result.1, false, .transition (.step features reward) trivial learner.admitted⟩ next.bank,
      .cons (Prediction.project _ result.2.value) next.predictions,
      (#v[result.2.error.abs] ++ next.errors).cast (by simp [Nat.add_comm]),
      (#v[reward] ++ next.cumulants).cast (by simp [Nat.add_comm])⟩

/-- Every prediction returned by a demon step inhabits its own signal range. -/
theorem Demon.step_prediction_legal {S Obs Res : Type} [Signal S Obs Res]
    {signal : S} {dimension : Dimension} (demon : Demon (Obs := Obs) (Res := Res) signal dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Obs) (res : Res) :
    (Signal.discount (Obs := Obs) (Res := Res) signal).predictionRange.Contains
      (demon.step features obs res).2.prediction.value :=
  (demon.step features obs res).2.prediction.legal

/-- Prediction feedback has exactly the bank's channel count after every update. -/
theorem DemonBank.step_feedback_length {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension discounts) (features : SwiftTd.ActiveSet dimension)
    (rewards : Cumulants discounts) :
    (bank.step features rewards).predictions.words.length = discounts.length :=
  (bank.step features rewards).predictions.length

end Acorn.Features
