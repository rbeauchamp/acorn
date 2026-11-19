/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentDeclaredStep

/-!
# The declared step reads the representation only through the active set

`AcornVerif.CurrentDeclaredStep.StepsByRule` leaves the representation and the lifetime
observations to the step and fixes everything else as the declared step's. The declared step is
applied to the agent's own control, which holds that representation. This module proves that,
for a profile with no hierarchy, what the declared step decides and leaves outside the
representation and the lifetime observations depends on the representation in one way only:
through the active set the encoder lays for the percept's frame.

`declaredStep_blind`: two controls that hold the same learners, temporal references, credit,
gain and rate (`SameLearned`), and for which the encoder lays the same active set at the
percept's frame, have declared steps with the same decision that again hold the same there.
So in one application of the declared step, for a profile with no hierarchy, the decision and
the learners, temporal references, credit, gain and rate the step leaves read the
representation and the lifetime observations only through which slots are active.

The theorem is about the declared step alone. Under `StepsByRule` the agent's step also forgets
a list of units, and that list is chosen outside the declared step, by a computation that may
read the representation: a unit whose projection the step rewrites is in it, and it may hold
others. The theorem does not cover that choice.

The proof moves a control's representation and lifetime observations aside (`regraft`) and
shows that each part of the transition commutes with that: preparing the selection, serving a
committed run, interrupting, the primitive choice, and the learning part, whose completion
passes the representation's clock to the lifetime observations and to nothing else.

Degenerate instances, read for what they say. With the two controls equal the theorem says
nothing. With equal representations and different lifetime observations it says that one
declared step's decision, and what it leaves outside the representation and the lifetime
observations, do not read the lifetime observations. It makes no claim for a profile with a
hierarchy.
-/

namespace AcornVerif.CurrentDeclaredStep
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}

/-- A control with another representation and other lifetime observations. -/
def regraft (state : TemporalControl interface profile config criterion dimension)
    (representation : Representation interface.symbols config)
    (lifetime : Lifetime.Stats interface.layout) :
    TemporalControl interface profile config criterion dimension :=
  ⟨⟨⟨representation, state.runtime.lifecycle.consumers⟩, state.runtime.references⟩,
    state.credit, state.creditMatches, state.average, state.rate, lifetime⟩

/-- Preparing the selection of a profile with no hierarchy commutes with moving the
representation and the lifetime observations aside. -/
theorem prepare_regraft (state : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false)
    (representation : Representation interface.symbols config)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (regraft state representation lifetime).prepareSelection models features reward =
      regraft (state.prepareSelection models features reward) representation lifetime := by
  simp only [TemporalControl.prepareSelection, primitive, Bool.false_and, Bool.false_eq_true,
    ite_false]
  rfl

/-- Interrupting a held option commutes with moving the representation and the lifetime
observations aside. -/
theorem interrupt_regraft (state : TemporalControl interface profile config criterion dimension)
    (representation : Representation interface.symbols config)
    (lifetime : Lifetime.Stats interface.layout)
    (origin : Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation (profile.mode != .frozen))) :
    (regraft state representation lifetime).interrupt origin =
      (regraft (state.interrupt origin).1 representation lifetime,
        (state.interrupt origin).2) := by
  unfold TemporalControl.interrupt
  cases origin with
  | none => rfl
  | some held =>
    obtain ⟨slot, activation⟩ := held
    dsimp only
    split <;> rfl

/-- Serving a committed run commutes with moving the representation and the lifetime
observations aside, for a profile with no hierarchy. -/
theorem serve_regraft (state : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false)
    (representation : Representation interface.symbols config)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension) :
    (regraft state representation lifetime).serve features =
      (state.serve features).map fun result =>
        (regraft result.1 representation lifetime, result.2) := by
  unfold TemporalControl.serve
  change (match state.runtime.references.phase with
    | .exploring committed => _
    | .idle | .option _ _ => none) = _
  cases state.runtime.references.phase with
  | idle => rfl
  | option slot activation => rfl
  | exploring committed =>
    dsimp only
    cases committed.run.serve with
    | none => rfl
    | some served =>
      simp only [primitive, Bool.false_eq_true, ite_false, TemporalControl.skipMeta,
        Bool.false_and, ite_self, interrupt_regraft]
      rfl

/-- The fresh primitive choice commutes with moving the representation and the lifetime
observations aside. -/
theorem choose_regraft (state : TemporalControl interface profile config criterion dimension)
    (representation : Representation interface.symbols config)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    ((regraft state representation lifetime).withPhase .idle).choosePrimitive features metaValues
        metaDecision ended =
      (regraft ((state.withPhase .idle).choosePrimitive features metaValues metaDecision
          ended).1 representation lifetime,
        ((state.withPhase .idle).choosePrimitive features metaValues metaDecision ended).2) :=
  rfl

/-- **The selection of a profile with no hierarchy reads neither the representation nor the
lifetime observations**: it commutes with moving them aside. -/
theorem select_regraft (state : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false)
    (representation : Representation interface.symbols config)
    (lifetime : Lifetime.Stats interface.layout) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) :
    (regraft state representation lifetime).select planning features declared reward goal =
      (state.select planning features declared reward goal).map fun result =>
        (regraft result.1 representation lifetime, result.2) := by
  unfold TemporalControl.select TemporalControl.selectWithOperations
  rw [prepare_regraft state primitive]
  generalize state.prepareSelection (modelOperations criterion dimension) features reward =
    prepared
  dsimp only
  rw [serve_regraft prepared primitive]
  cases prepared.serve features with
  | some result => rfl
  | none =>
    simp only [primitive, Bool.not_false, ite_true, Option.map_none]
    rfl

/-- Two controls hold the same outside the representation and the lifetime observations. -/
def SameLearned (left right : TemporalControl interface profile config criterion dimension) :
    Prop :=
  left.runtime.lifecycle.consumers = right.runtime.lifecycle.consumers ∧
    left.runtime.references = right.runtime.references ∧ left.credit = right.credit ∧
    left.average = right.average ∧ left.rate = right.rate

/-- **The learning part of a profile with no hierarchy reads the representation only for the
lifetime observations.** What it leaves outside the representation and the lifetime
observations is the same whatever representation and lifetime observations the control
holds. -/
theorem learn_regraft (state : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false)
    (representation : Representation interface.symbols config)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension)
    (obs : Frame interface) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    SameLearned ((regraft state representation lifetime).learn features obs reward goal decision)
      (state.learn features obs reward goal decision) := by
  unfold TemporalControl.learn
  dsimp only
  rw [TemporalControl.followOptions_eq, TemporalControl.followOptions_eq]
  simp only [TemporalControl.takeoverValue, primitive, Bool.false_and, Bool.false_eq_true,
    ite_false, TemporalControl.closeSpan]
  rw [TemporalControl.finish_eq, TemporalControl.finish_eq]
  unfold PredictionControl.advanceWith
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A control that holds the same as another outside the representation and the lifetime
observations is that other with its own representation and lifetime observations. -/
theorem regraft_of_same {left right : TemporalControl interface profile config criterion dimension}
    (same : SameLearned left right) :
    right = regraft left right.runtime.lifecycle.representation right.lifetime := by
  obtain ⟨⟨⟨_, consumers⟩, references⟩, credit, _, average, rate, _⟩ := left
  obtain ⟨⟨⟨_, _⟩, _⟩, _, _, _, _, _⟩ := right
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
  rfl

/-- **The declared step reads the representation only through the active set.** For a profile
with no hierarchy: two controls that hold the same outside the representation and the lifetime
observations, and whose encoders lay the same active set for the percept's frame, have declared
steps with the same decision that hold the same outside the representation and the lifetime
observations. -/
theorem declaredStep_blind (primitive : profile.usesHierarchy = false)
    (left right : TemporalControl interface profile config criterion dimension)
    (alignedLeft : left.Aligned) (alignedRight : right.Aligned) (planning : PlanningSelection)
    (percept : Percept interface) (same : SameLearned left right)
    (active : perceivedActive left percept.frame = perceivedActive right percept.frame) :
    SameLearned (declaredStep left alignedLeft planning percept).1
        (declaredStep right alignedRight planning percept).1 ∧
      (declaredStep left alignedLeft planning percept).2 =
        (declaredStep right alignedRight planning percept).2 := by
  have steppedLeft : (advanced left).step planning (perceivedActive left percept.frame)
      percept.frame percept.reward percept.frame.achieved =
        some (declaredStep left alignedLeft planning percept) :=
    ((advanced left).alignedStep alignedLeft planning (perceivedActive left percept.frame)
      percept.frame percept.reward percept.frame.achieved).2.1
  have steppedRight : (advanced right).step planning (perceivedActive right percept.frame)
      percept.frame percept.reward percept.frame.achieved =
        some (declaredStep right alignedRight planning percept) :=
    ((advanced right).alignedStep alignedRight planning (perceivedActive right percept.frame)
      percept.frame percept.reward percept.frame.achieved).2.1
  have advancedSame : SameLearned (advanced left) (advanced right) := same
  rw [← active, regraft_of_same advancedSame, TemporalControl.step_parts,
    select_regraft _ primitive] at steppedRight
  rw [TemporalControl.step_parts] at steppedLeft
  cases chosen : (advanced left).select planning (perceivedActive left percept.frame)
      percept.frame.declared percept.reward percept.frame.achieved with
  | none =>
    rw [chosen] at steppedLeft
    exact absurd steppedLeft (by simp)
  | some selected =>
    rw [chosen] at steppedLeft steppedRight
    have fromLeft := Option.some.inj steppedLeft
    have fromRight := Option.some.inj steppedRight
    rw [← fromLeft, ← fromRight]
    have learned := learn_regraft selected.1 primitive
      (advanced right).runtime.lifecycle.representation (advanced right).lifetime
      (perceivedActive left percept.frame) percept.frame percept.reward percept.frame.achieved
      selected.2
    exact ⟨⟨learned.1.symm, learned.2.1.symm, learned.2.2.1.symm, learned.2.2.2.1.symm,
      learned.2.2.2.2.symm⟩, rfl⟩

end AcornVerif.CurrentDeclaredStep
