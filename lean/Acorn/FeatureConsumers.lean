/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.FeatureRanking

/-!
# Complete feature-consumer storage and resets

This slice executes current SwiftTD resets in the current control, meta,
skill-policy, model and demon shapes. Later controller/option modules supply
updates through the same phase-indexed learner interface. The unrestricted
standalone SwiftTD input domain remains unchanged.
-/
namespace Acorn.Features

/-- Erased provenance of phase-disciplined calls to the actual learner.
The same `Permitted` definition owns the existing universal capacity theorem. -/
inductive ManagedAdmission (config : Acorn.Config) (dimension : Dimension) :
    NumericState config dimension → Bool → Prop where
  /-- Fresh legal storage. -/
  | initial : ManagedAdmission config dimension (NumericState.initial config dimension) true
  /-- Every permitted executing entry extends admission. -/
  | transition {state : NumericState config dimension} {phase : Bool}
      (entry : SwiftTd.Entry dimension) (permitted : SwiftTd.Permitted entry phase)
      (before : ManagedAdmission config dimension state phase) :
      ManagedAdmission config dimension (entry.apply state) (SwiftTd.nextReady entry phase)

/-- A learner scheduled under the already proved eligibility/resource contract.
The invariant is erased, so no learning history is retained. -/
structure Managed (config : Acorn.Config) (dimension : Dimension) where
  /-- Executing current learner storage. -/
  state : NumericState config dimension
  /-- Whether a standalone second loop is presently permitted. -/
  phase : Bool
  /-- Core safety, unique eligibility and phase-specific readiness. -/
  admitted : ManagedAdmission config dimension state phase

/-- Fresh phase-disciplined learner. -/
def Managed.initial (config : Acorn.Config) (dimension : Dimension) : Managed config dimension :=
  ⟨NumericState.initial config dimension, true, .initial⟩

/-- Apply any current learner entry under its explicit scheduling premise. -/
def Managed.apply {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (entry : SwiftTd.Entry dimension)
    (permitted : SwiftTd.Permitted entry learner.phase) : Managed config dimension :=
  ⟨entry.apply learner.state, SwiftTd.nextReady entry learner.phase,
    .transition entry permitted learner.admitted⟩

/-- Receiver-owned reset of all nine registers, knowledge, eligibility and aggregates. -/
def Managed.retire {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (feature : FeatIdx dimension) : Managed config dimension :=
  learner.apply (.retire feature) trivial

/-- A common read-only carrier preserves each consumer's own immutable configuration. -/
abbrev PackedLearner (dimension : Dimension) := Σ config : Acorn.Config, Managed config dimension

/-- Read negligibility under exactly this stored learner's derived bounds. -/
def PackedLearner.negligible {dimension : Dimension} (learner : PackedLearner dimension)
    (feature : FeatIdx dimension) : Bool := learner.2.state.unitIsNegligible feature

/-- Reset a heterogeneous learner without replacing its configuration. -/
def PackedLearner.retire {dimension : Dimension} (feature : FeatIdx dimension)
    (learner : PackedLearner dimension) : PackedLearner dimension :=
  ⟨learner.1, learner.2.retire feature⟩

/-- Complete current controller state relevant to representation replacement. -/
structure Controller (config : Acorn.Config) (dimension : Dimension) (actions : Nat) where
  /-- One learner per action, under the shared immutable configuration. -/
  learners : Vector (Managed config dimension) actions
  /-- Shared previous prediction. -/
  vOld : Binary32
  /-- Shared weight-change accumulator. -/
  vDelta : Binary32
  /-- Deferred trace restart after action-identity replacement. -/
  restartPending : Bool

/-- Fresh controller storage. -/
def Controller.initial (config : Acorn.Config) (dimension : Dimension) (actions : Nat) :
    Controller config dimension actions :=
  ⟨Vector.ofFn (fun _ => Managed.initial config dimension), .zero, .zero, false⟩

/-- Structural consumer order of the current controller. -/
def Controller.readers {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) : List (PackedLearner dimension) :=
  controller.learners.toList.map (fun learner => ⟨config, learner⟩)

/-- Every controller learner resets, followed by both wrapper aggregates.
The action-restart marker is retained, as in the current controller. -/
def Controller.retire {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (feature : FeatIdx dimension) :
    Controller config dimension actions :=
  let ⟨learners, _, _, restart⟩ := controller
  ⟨learners.map (·.retire feature), .zero, .zero, restart⟩

/-- One new action identity resets its learner and schedules a trace restart;
shared lags are retained for pending credit to unchanged actions. -/
def Controller.resetAction {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (action : Fin actions) :
    Controller config dimension actions :=
  { controller with
    learners := controller.learners.set action.val (Managed.initial config dimension) action.isLt
    restartPending := true }

/-- Current control criteria, separate from research-profile selection. -/
inductive Criterion where
  /-- Preserved discounted control. -/
  | discounted
  /-- Continuing differential control. -/
  | differential
  deriving DecidableEq

/-- The current criterion's exact numeric rule. -/
def Criterion.rule : Criterion → ValueRule
  | .discounted => .discounted .g99
  | .differential => .differential

/-- A role's configuration derives from the immutable criterion. -/
def Criterion.config (criterion : Criterion) (role : Role) : Acorn.Config :=
  ⟨role, criterion.rule⟩

/-- Optional duration storage follows the criterion by construction. -/
inductive Model (dimension : Dimension) : Criterion → Type where
  /-- Discounted models store reward and continuation only. -/
  | discounted (reward continuation : Managed (Criterion.config .discounted .demon) dimension) :
      Model dimension .discounted
  /-- Differential models additionally store duration. -/
  | differential (reward continuation duration : Managed (Criterion.config .differential .demon) dimension) :
      Model dimension .differential

/-- Fresh complete model storage. -/
def Model.initial (dimension : Dimension) : (criterion : Criterion) → Model dimension criterion
  | .discounted => .discounted (Managed.initial _ _) (Managed.initial _ _)
  | .differential => .differential (Managed.initial _ _) (Managed.initial _ _) (Managed.initial _ _)

/-- All three reader positions; discounted duration deliberately aliases reward. -/
def Model.readers {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : List (PackedLearner dimension) :=
  match model with
  | .discounted reward continuation => [⟨_, reward⟩, ⟨_, continuation⟩, ⟨_, reward⟩]
  | .differential reward continuation duration => [⟨_, reward⟩, ⟨_, continuation⟩, ⟨_, duration⟩]

/-- Each physically stored learner once, without reader aliases. -/
def Model.stored {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : List (PackedLearner dimension) :=
  match model with
  | .discounted reward continuation => [⟨_, reward⟩, ⟨_, continuation⟩]
  | .differential reward continuation duration => [⟨_, reward⟩, ⟨_, continuation⟩, ⟨_, duration⟩]

/-- Exhaustive model reset, including the optional duration state. -/
def Model.retire {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (feature : FeatIdx dimension) : Model dimension criterion :=
  match model with
  | .discounted reward continuation =>
    .discounted (reward.retire feature) (continuation.retire feature)
  | .differential reward continuation duration =>
    .differential (reward.retire feature) (continuation.retire feature) (duration.retire feature)

/-- Heterogeneous prediction storage follows the supplied closed horizon layout.
The layout is immutable and supplied by the declared composition boundary. -/
inductive DemonBank (dimension : Dimension) : List Discount → Type where
  /-- No further prediction channels. -/
  | nil : DemonBank dimension []
  /-- One configured prediction learner and the remaining channels. -/
  | cons {discount : Discount} {rest : List Discount}
      (learner : Managed ⟨.demon, .discounted discount⟩ dimension)
      (tail : DemonBank dimension rest) : DemonBank dimension (discount :: rest)

/-- Initialize the complete supplied prediction layout. -/
def DemonBank.initial (dimension : Dimension) : (discounts : List Discount) → DemonBank dimension discounts
  | [] => .nil
  | _ :: rest => .cons (Managed.initial _ _) (DemonBank.initial dimension rest)

/-- Every demon once, in canonical channel order. -/
def DemonBank.readers {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) : List (PackedLearner dimension) :=
  match demons with
  | .nil => []
  | .cons learner rest => ⟨_, learner⟩ :: rest.readers

/-- Every demon uses the same receiver-derived feature reset. -/
def DemonBank.retire {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) (feature : FeatIdx dimension) : DemonBank dimension discounts :=
  match demons with
  | .nil => .nil
  | .cons learner rest => .cons (learner.retire feature) (rest.retire feature)

/-- A learned target or an explicitly declared opaque potential choice.
The learned module never interprets the declared tag as host vocabulary. -/
inductive Interest (config : Config) where
  /-- Learned objective. -/
  | learned (assignment : Assignment config)
  /-- Declared composition choice, with its register witness. -/
  | declared (origin : Departure) (tag : Fin Acorn.FeatureConstants.skillCount)

/-- Complete storage belonging to one option assignment. -/
structure Skill (config : Config) (criterion : Criterion) (dimension : Dimension) where
  /-- Objective identity, retained by feature-slot retirement. -/
  interest : Interest config
  /-- Current option-policy consumers. -/
  policy : Controller (criterion.config .optionSkill) dimension Acorn.FeatureConstants.primitiveCount
  /-- Current model consumers. -/
  model : Model dimension criterion

/-- Fresh policy and model for the selected target. -/
def Skill.initial (config : Config) (criterion : Criterion) (dimension : Dimension)
    (interest : Interest config) : Skill config criterion dimension :=
  ⟨interest, Controller.initial _ _ _, Model.initial _ _⟩

/-- Each policy reader followed by its three model reader positions. -/
def Skill.readers {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) : List (PackedLearner dimension) :=
  skill.policy.readers ++ skill.model.readers

/-- Reset knowledge in the complete skill while retaining its target identity. -/
def Skill.retire {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (feature : FeatIdx dimension) : Skill config criterion dimension :=
  let ⟨interest, policy, model⟩ := skill
  ⟨interest, policy.retire feature, model.retire feature⟩

/-- All current learned consumers; dimensions, criteria and channel layout are nominal. -/
structure Ensemble (config : Config) (criterion : Criterion) (dimension : Dimension)
    (discounts : List Discount) where
  /-- Primitive-action controller. -/
  control : Controller (criterion.config .control) dimension Acorn.FeatureConstants.primitiveCount
  /-- Meta controller, including the primitive delegation action. -/
  metaController : Controller (criterion.config .control) dimension Acorn.FeatureConstants.metaActionCount
  /-- Every current skill and its model. -/
  skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount
  /-- Every configured prediction channel. -/
  demons : DemonBank dimension discounts

/-- Complete reader traversal, with the current alias-preserving model positions. -/
def Ensemble.readers {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts) :
    List (PackedLearner dimension) :=
  let ⟨control, metaController, skills, demons⟩ := ensemble
  control.readers ++ metaController.readers ++ skills.toList.flatMap Skill.readers ++ demons.readers

/-- Complete structural reset of the same stored families the scan traverses. -/
def Ensemble.retire {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (feature : FeatIdx dimension) : Ensemble config criterion dimension discounts :=
  let ⟨control, metaController, skills, demons⟩ := ensemble
  ⟨control.retire feature, metaController.retire feature, skills.map (·.retire feature), demons.retire feature⟩

/-- The actual conjunction reads each learner's own current words. -/
def Ensemble.negligible {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (feature : FeatIdx dimension) : Bool := ensemble.readers.all (·.negligible feature)

/-- Initial storage includes every action, model and supplied prediction channel. -/
def Ensemble.initial (config : Config) (criterion : Criterion) (dimension : Dimension)
    (discounts : List Discount) (interests : Vector (Interest config) Acorn.FeatureConstants.skillCount) :
    Ensemble config criterion dimension discounts :=
  ⟨Controller.initial _ _ _, Controller.initial _ _ _,
    interests.map (Skill.initial config criterion dimension), DemonBank.initial dimension discounts⟩

/-- Reader count follows the controller's type-level action count. -/
theorem Controller.reader_count {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) : controller.readers.length = actions := by
  simp [Controller.readers]

/-- Both model criteria expose the same three canonical reader positions. -/
theorem Model.reader_count {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : model.readers.length = 3 := by
  cases model <;> rfl

/-- A discounted model's aliased duration reader does not imply additional storage. -/
theorem Model.storage_count {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) :
    model.stored.length = (match criterion with | .discounted => 2 | .differential => 3) := by
  cases model <;> rfl

/-- Every physically stored model learner participates in retirement admission. -/
theorem Model.stored_covered {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (learner : PackedLearner dimension)
    (member : learner ∈ model.stored) : learner ∈ model.readers := by
  cases model with
  | discounted reward continuation =>
    simp only [Model.stored, Model.readers, List.mem_cons, List.not_mem_nil, or_false] at *
    exact member.elim Or.inl (fun h => Or.inr (Or.inl h))
  | differential reward continuation duration => exact member

/-- Heterogeneous storage and traversal have exactly the supplied channel count. -/
theorem DemonBank.reader_count {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension discounts) : bank.readers.length = discounts.length := by
  induction bank with
  | nil => rfl
  | cons learner rest ih => simp [DemonBank.readers, ih]

/-- Each skill's coverage is derived from its policy shape and model interface. -/
theorem Skill.reader_count {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) :
    skill.readers.length = Acorn.FeatureConstants.primitiveCount + 3 := by
  simp [Skill.readers, Controller.reader_count, Model.reader_count]

/-- The complete reader count is derived from the actual nested storage shapes. -/
theorem Ensemble.reader_count {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts) :
    ensemble.readers.length = Acorn.FeatureConstants.primitiveCount + Acorn.FeatureConstants.metaActionCount +
      Acorn.FeatureConstants.skillCount * (Acorn.FeatureConstants.primitiveCount + 3) + discounts.length := by
  have skillCount (skills : List (Skill config criterion dimension)) :
      (skills.flatMap Skill.readers).length = skills.length * (Acorn.FeatureConstants.primitiveCount + 3) := by
    induction skills with
    | nil => simp
    | cons head tail ih => simp [Skill.reader_count, ih, Nat.add_mul, Nat.add_comm]
  simp [Ensemble.readers, Controller.reader_count, DemonBank.reader_count, skillCount, Nat.add_assoc]

/-- Controller scanning and reset cannot have different learner coverage. -/
theorem Controller.retire_readers {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (feature : FeatIdx dimension) :
    (controller.retire feature).readers = controller.readers.map (PackedLearner.retire feature) := by
  simp [Controller.retire, Controller.readers, Vector.toList_map, List.map_map, Function.comp_def, PackedLearner.retire]

/-- Model scanning preserves its intentional alias under the actual reset. -/
theorem Model.retire_readers {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (feature : FeatIdx dimension) :
    (model.retire feature).readers = model.readers.map (PackedLearner.retire feature) := by
  cases model <;> rfl

/-- Every prediction reader is reset by the same traversal. -/
theorem DemonBank.retire_readers {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) (feature : FeatIdx dimension) :
    (demons.retire feature).readers = demons.readers.map (PackedLearner.retire feature) := by
  induction demons with
  | nil => rfl
  | cons learner rest ih => simp [DemonBank.retire, DemonBank.readers, PackedLearner.retire, ih]

/-- Skill scanning and reset include both policy and model state. -/
theorem Skill.retire_readers {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (feature : FeatIdx dimension) :
    (skill.retire feature).readers = skill.readers.map (PackedLearner.retire feature) := by
  simp [Skill.retire, Skill.readers, Controller.retire_readers, Model.retire_readers]

/-- Complete reset commutes with the complete reader traversal, for all criteria,
channel layouts, dimensions and states. No enumerated current consumer is omitted. -/
theorem Ensemble.retire_readers {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (feature : FeatIdx dimension) :
    (ensemble.retire feature).readers = ensemble.readers.map (PackedLearner.retire feature) := by
  simp [Ensemble.retire, Ensemble.readers, Controller.retire_readers, DemonBank.retire_readers,
    Vector.toList_map, List.flatMap_map, List.map_flatMap, Skill.retire_readers]

end Acorn.Features
