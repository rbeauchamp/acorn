import Acorn.FeatureConstants
import Acorn.FeatureRanking
import Acorn.RankedFeatures

namespace Acorn.Features

variable {actions : Word.Count}

def referenceRange : Interval32 :=
  ⟨.zero, ⟨0x40a00000⟩, by decide, by decide, by decide⟩

def _root_.Acorn.NumericState.clearAt {config : Acorn.Config} {dimension : Dimension}
    (state : NumericState config dimension) (index : FeatIdx dimension) : Bool :=
  (state.transient.z.get index).value == .zero &&
    (state.transient.zDelta.get index).value == .zero &&
    (state.transient.zBar.get index).value == .zero &&
    (state.transient.lastAlpha.get index).value == .zero &&
    (state.transient.deltaWeight.get index).value == .zero &&
    (state.transient.h.get index).value == .zero &&
    (state.transient.hOld.get index).value == .zero &&
    (state.transient.hTemp.get index).value == .zero &&
    (state.transient.p.get index).value == .zero

def _root_.Acorn.NumericState.resumable {config : Acorn.Config} {dimension : Dimension}
    (state : NumericState config dimension) (phase : Bool) : Bool :=
  let eligible := state.transient.eligible.toList
  let builder := eligible.foldl UniqueBuilder.add (UniqueBuilder.empty dimension)
  builder.reversed.length == eligible.length &&
    (List.finRange dimension.capacity).all (fun index =>
      (builder.seen[index.val] || state.clearAt index) &&
        decide (referenceRange.Contains (state.transient.lastAlpha.get index).value)) &&
    (!phase || eligible.all fun index => !(state.transient.z.get index).value.isZero)

inductive ManagedAdmission (config : Acorn.Config) (dimension : Dimension) :
    NumericState config dimension → Bool → Prop where
  | initial : ManagedAdmission config dimension (NumericState.initial config dimension) true
  | transition {state : NumericState config dimension} {phase : Bool}
      (entry : SwiftTd.Entry dimension) (permitted : SwiftTd.Permitted entry phase)
      (before : ManagedAdmission config dimension state phase) :
      ManagedAdmission config dimension (entry.apply state) (SwiftTd.nextReady entry phase)
  | durable {state : NumericState config dimension} {phase : Bool}
      (checked : state.resumable phase = true) : ManagedAdmission config dimension state phase

structure Managed (config : Acorn.Config) (dimension : Dimension) where
  state : NumericState config dimension
  phase : Bool
  admitted : ManagedAdmission config dimension state phase

def Managed.initial (config : Acorn.Config) (dimension : Dimension) : Managed config dimension :=
  ⟨NumericState.initial config dimension, true, .initial⟩

def Managed.applyCosted {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (entry : SwiftTd.Entry dimension)
    (permitted : SwiftTd.Permitted entry learner.phase) : Costed (Managed config dimension) :=
  Costed.charge .managedEntry <| Costed.bind (Costed.attach (entry.applyCosted learner.state))
    fun state => Costed.pure ⟨state.val, SwiftTd.nextReady entry learner.phase, by
      rw [state.property]
      exact .transition entry permitted learner.admitted⟩

def Managed.apply {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (entry : SwiftTd.Entry dimension)
    (permitted : SwiftTd.Permitted entry learner.phase) : Managed config dimension :=
  (learner.applyCosted entry permitted).val

theorem Managed.apply_def {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (entry : SwiftTd.Entry dimension)
    (permitted : SwiftTd.Permitted entry learner.phase) :
    learner.apply entry permitted = ⟨entry.apply learner.state, SwiftTd.nextReady entry learner.phase,
      .transition entry permitted learner.admitted⟩ := rfl

theorem Managed.apply_state {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (entry : SwiftTd.Entry dimension)
    (permitted : SwiftTd.Permitted entry learner.phase) :
    (learner.apply entry permitted).state = entry.apply learner.state := rfl

theorem Managed.apply_phase {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (entry : SwiftTd.Entry dimension)
    (permitted : SwiftTd.Permitted entry learner.phase) :
    (learner.apply entry permitted).phase = SwiftTd.nextReady entry learner.phase := rfl

def Managed.retireCosted {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (feature : FeatIdx dimension) :
    Costed (Managed config dimension) :=
  learner.applyCosted (.retire feature) trivial

def Managed.retire {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (feature : FeatIdx dimension) : Managed config dimension :=
  (learner.retireCosted feature).val

theorem Managed.retire_def {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (feature : FeatIdx dimension) :
    learner.retire feature = learner.apply (.retire feature) trivial := rfl

abbrev PackedLearner (dimension : Dimension) := Σ config : Acorn.Config, Managed config dimension

def PackedLearner.retire {dimension : Dimension} (feature : FeatIdx dimension)
    (learner : PackedLearner dimension) : PackedLearner dimension :=
  ⟨learner.1, learner.2.retire feature⟩

@[noinline] def takeOut {α : Type} {size : Nat} (items : Vector α size) (index : Fin size)
    (stand : α) : α × Vector α size :=
  (items.get index, items.set index.val stand index.isLt)

def detachedUpdate {α β : Type} {size : Nat} (items : Vector α size) (index : Fin size)
    (update : α → α × β) : Vector α size × β :=
  let next : Fin size := ⟨(index.val + 1) % size, Nat.mod_lt _ (Nat.zero_lt_of_lt index.isLt)⟩
  let (taken, rest) := takeOut items index (items.get next)
  let (updated, observed) := update taken
  (rest.set index.val updated index.isLt, observed)

def detachedUpdateCosted {α β : Type} {size : Nat} (items : Vector α size) (index : Fin size)
    (update : α → Costed (α × β)) : Costed (Vector α size × β) :=
  let next : Fin size := ⟨(index.val + 1) % size, Nat.mod_lt _ (Nat.zero_lt_of_lt index.isLt)⟩
  let (taken, rest) := takeOut items index (items.get next)
  Costed.bind (update taken) fun (updated, observed) =>
    Costed.pure (rest.set index.val updated index.isLt, observed)

theorem detachedUpdate_eq {α β : Type} {size : Nat} (items : Vector α size) (index : Fin size)
    (update : α → α × β) :
    detachedUpdate items index update =
      (items.set index.val (update (items.get index)).1 index.isLt,
        (update (items.get index)).2) := by
  simp only [detachedUpdate, takeOut, Vector.set_set]

structure Controller (config : Acorn.Config) (dimension : Dimension) (actions : Nat) where
  learners : Vector (Managed config dimension) actions
  vOld : Binary32
  vDelta : Binary32
  restartPending : Bool

def Controller.initial (config : Acorn.Config) (dimension : Dimension) (actions : Nat) :
    Controller config dimension actions :=
  ⟨Vector.ofFn (fun _ => Managed.initial config dimension), .zero, .zero, false⟩

def Controller.readers {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) : List (PackedLearner dimension) :=
  controller.learners.toList.map (fun learner => ⟨config, learner⟩)

def Controller.retireCosted {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (feature : FeatIdx dimension) :
    Costed (Controller config dimension actions) :=
  let ⟨learners, vOld, vDelta, restart⟩ := controller
  Costed.bind (Costed.mapVector (·.retireCosted feature) learners) fun rows =>
    Costed.op .controllerClose ⟨rows, vOld, vDelta, restart⟩

def Controller.retire {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (feature : FeatIdx dimension) :
    Controller config dimension actions :=
  (controller.retireCosted feature).val

theorem Controller.retire_def {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (feature : FeatIdx dimension) :
    controller.retire feature =
      let ⟨learners, vOld, vDelta, restart⟩ := controller
      ⟨learners.map (·.retire feature), vOld, vDelta, restart⟩ := by
  cases controller
  rfl

def Controller.resetAction {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (action : Fin actions) :
    Controller config dimension actions :=
  { controller with
    learners := controller.learners.set action.val (Managed.initial config dimension) action.isLt
    restartPending := true }

inductive Criterion where
  | discounted
  | differential
  deriving DecidableEq

def Criterion.tag : Criterion → UInt8
  | .discounted => 0
  | .differential => 1

def Criterion.rule : Criterion → ValueRule
  | .discounted => .discounted .g99
  | .differential => .differential

def Criterion.config (criterion : Criterion) (role : Role) : Acorn.Config :=
  ⟨role, criterion.rule⟩

structure Transition (dimension : Dimension) (criterion : Criterion) where
  ranked : RankedFeatures dimension
  rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
    (rankDimension dimension).capacity
  deviations : Vector (Managed (criterion.config .demon) (rankDimension dimension))
    Acorn.FeatureConstants.metaActionCount

def Transition.initial (dimension : Dimension) (criterion : Criterion) :
    Transition dimension criterion :=
  ⟨.empty dimension, Vector.replicate _ (Managed.initial _ _),
    Vector.replicate _ (Managed.initial _ _)⟩

def Transition.forget {dimension : Dimension} {criterion : Criterion}
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity) (positions : List (RankIdx dimension)) :
    Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity :=
  rows.mapFinIdx fun index row bound =>
    if positions.contains ⟨index, bound⟩ then Managed.initial _ _
    else positions.foldl (fun learner position => learner.retire position) row

def Transition.forgetColumns {dimension : Dimension} {criterion : Criterion} {count : Nat}
    (learners : Vector (Managed (criterion.config .demon) (rankDimension dimension)) count)
    (positions : List (RankIdx dimension)) :
    Vector (Managed (criterion.config .demon) (rankDimension dimension)) count :=
  learners.map fun learner =>
    positions.foldl (fun current position => current.retire position) learner

def Transition.rerank {dimension : Dimension} {criterion : Criterion}
    (transition : Transition dimension criterion) (order : List (FeatIdx dimension))
    (fresh : order.Nodup) : Transition dimension criterion :=
  let ranked := transition.ranked.rerank order fresh
  let changed := transition.ranked.changed ranked
  ⟨ranked, Transition.forget transition.rows changed,
    Transition.forgetColumns transition.deviations changed⟩

def Transition.retire {dimension : Dimension} {criterion : Criterion}
    (transition : Transition dimension criterion) (feature : FeatIdx dimension) :
    Transition dimension criterion :=
  match transition.ranked.holding feature with
  | [] => transition
  | position :: more =>
    ⟨transition.ranked.vacate (position :: more),
      Transition.forget transition.rows (position :: more),
      Transition.forgetColumns transition.deviations (position :: more)⟩

inductive Model (dimension : Dimension) : Criterion → Type where
  | discounted (reward continuation : Managed (Criterion.config .discounted .demon) dimension)
      (transition : Transition dimension .discounted) : Model dimension .discounted
  | differential (reward continuation duration : Managed (Criterion.config .differential .demon) dimension)
      (transition : Transition dimension .differential) : Model dimension .differential

def Model.initial (dimension : Dimension) : (criterion : Criterion) → Model dimension criterion
  | .discounted => .discounted (Managed.initial _ _) (Managed.initial _ _) (.initial _ _)
  | .differential =>
    .differential (Managed.initial _ _) (Managed.initial _ _) (Managed.initial _ _) (.initial _ _)

def Model.transition {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : Transition dimension criterion :=
  match model with
  | .discounted _ _ transition => transition
  | .differential _ _ _ transition => transition

def Model.rerank {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (order : List (FeatIdx dimension))
    (fresh : order.Nodup) : Model dimension criterion :=
  match model with
  | .discounted reward continuation transition =>
    .discounted reward continuation (transition.rerank order fresh)
  | .differential reward continuation duration transition =>
    .differential reward continuation duration (transition.rerank order fresh)

def Model.readers {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : List (PackedLearner dimension) :=
  match model with
  | .discounted reward continuation _ => [⟨_, reward⟩, ⟨_, continuation⟩, ⟨_, reward⟩]
  | .differential reward continuation duration _ => [⟨_, reward⟩, ⟨_, continuation⟩, ⟨_, duration⟩]

def Model.stored {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : List (PackedLearner dimension) :=
  match model with
  | .discounted reward continuation _ => [⟨_, reward⟩, ⟨_, continuation⟩]
  | .differential reward continuation duration _ => [⟨_, reward⟩, ⟨_, continuation⟩, ⟨_, duration⟩]

def Model.retire {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (feature : FeatIdx dimension) : Model dimension criterion :=
  match model with
  | .discounted reward continuation transition =>
    .discounted (reward.retire feature) (continuation.retire feature) (transition.retire feature)
  | .differential reward continuation duration transition =>
    .differential (reward.retire feature) (continuation.retire feature) (duration.retire feature)
      (transition.retire feature)

inductive DemonBank (dimension : Dimension) : List Discount → Type where
  | nil : DemonBank dimension []
  | cons {discount : Discount} {rest : List Discount}
      (learner : Managed ⟨.demon, .discounted discount⟩ dimension)
      (tail : DemonBank dimension rest) : DemonBank dimension (discount :: rest)

def DemonBank.initial (dimension : Dimension) : (discounts : List Discount) → DemonBank dimension discounts
  | [] => .nil
  | _ :: rest => .cons (Managed.initial _ _) (DemonBank.initial dimension rest)

def DemonBank.readers {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) : List (PackedLearner dimension) :=
  match demons with
  | .nil => []
  | .cons learner rest => ⟨_, learner⟩ :: rest.readers

def DemonBank.retire {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) (feature : FeatIdx dimension) : DemonBank dimension discounts :=
  match demons with
  | .nil => .nil
  | .cons learner rest => .cons (learner.retire feature) (rest.retire feature)

inductive Interest (config : Config) where
  | learned (assignment : Assignment config)
  | declared (origin : Departure) (tag : Fin Acorn.FeatureConstants.skillCount)

def Interest.held {config : Config} : Interest config → Assignment config
  | .learned assignment => assignment
  | .declared _ _ => .neutral

structure Following where
  age : Fin (Acorn.FeatureConstants.optionMaxDuration + 1)
  live : Bool
  previous : Bool

structure Skill (actions : Word.Count) (config : Config) (criterion : Criterion) (dimension : Dimension)
    (discounts : List Discount) where
  interest : Interest config
  policy : Controller (criterion.config .optionSkill) dimension actions.word.toNat
  model : Model dimension criterion
  following : Option Following

def Skill.initial (config : Config) (criterion : Criterion) (dimension : Dimension)
    {discounts : List Discount} (interest : Interest config) :
    Skill actions config criterion dimension discounts :=
  ⟨interest, Controller.initial _ _ _, Model.initial _ _, none⟩

def Skill.readers {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts) :
    List (PackedLearner dimension) :=
  skill.policy.readers ++ skill.model.readers

def Skill.retire {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (feature : FeatIdx dimension) : Skill actions config criterion dimension discounts :=
  let ⟨interest, policy, model, following⟩ := skill
  ⟨interest, policy.retire feature, model.retire feature, following⟩

structure Ensemble (actions : Word.Count) (config : Config) (criterion : Criterion) (dimension : Dimension)
    (discounts : List Discount) where
  control : Controller (criterion.config .control) dimension actions.word.toNat
  metaController : Controller (criterion.config .control) dimension Acorn.FeatureConstants.metaActionCount
  skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount
  demons : DemonBank dimension discounts

def Ensemble.readers {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts) :
    List (PackedLearner dimension) :=
  let ⟨control, metaController, skills, demons⟩ := ensemble
  control.readers ++ metaController.readers ++ skills.toList.flatMap Skill.readers ++ demons.readers

def Ensemble.retire {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (feature : FeatIdx dimension) : Ensemble actions config criterion dimension discounts :=
  let ⟨control, metaController, skills, demons⟩ := ensemble
  ⟨control.retire feature, metaController.retire feature, skills.map (·.retire feature), demons.retire feature⟩

def Skill.stored {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts) :
    List (PackedLearner dimension) :=
  skill.policy.readers ++ skill.model.stored

def Ensemble.stored {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts) :
    List (PackedLearner dimension) :=
  let ⟨control, metaController, skills, demons⟩ := ensemble
  control.readers ++ metaController.readers ++ skills.toList.flatMap Skill.stored ++ demons.readers

def outgoing {dimension : Dimension} (readers : List (PackedLearner dimension))
    (feature : FeatIdx dimension) : Binary32 :=
  Binary32.sumMap .zero readers (fun learner => (learner.2.state.weights.get feature).value.abs)

def Ensemble.initial (config : Config) (criterion : Criterion) (dimension : Dimension)
    (discounts : List Discount) (interests : Vector (Interest config) Acorn.FeatureConstants.skillCount) :
    Ensemble actions config criterion dimension discounts :=
  ⟨Controller.initial _ _ _, Controller.initial _ _ _,
    interests.map (Skill.initial config criterion dimension), DemonBank.initial dimension discounts⟩

theorem Controller.reader_count {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) : controller.readers.length = actions := by
  simp [Controller.readers]

theorem Model.reader_count {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : model.readers.length = 3 := by
  cases model <;> rfl

theorem Model.storage_count {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) :
    model.stored.length = (match criterion with | .discounted => 2 | .differential => 3) := by
  cases model <;> rfl

theorem Model.stored_covered {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (learner : PackedLearner dimension)
    (member : learner ∈ model.stored) : learner ∈ model.readers := by
  cases model with
  | discounted reward continuation transition =>
    simp only [Model.stored, Model.readers, List.mem_cons, List.not_mem_nil, or_false] at *
    exact member.elim Or.inl (fun h => Or.inr (Or.inl h))
  | differential reward continuation duration transition => exact member

theorem DemonBank.reader_count {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension discounts) : bank.readers.length = discounts.length := by
  induction bank with
  | nil => rfl
  | cons learner rest ih => simp [DemonBank.readers, ih]

theorem Skill.reader_count {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts) :
    skill.readers.length = actions.word.toNat + 3 := by
  simp [Skill.readers, Controller.reader_count, Model.reader_count]

theorem Ensemble.reader_count {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts) :
    ensemble.readers.length = actions.word.toNat + Acorn.FeatureConstants.metaActionCount +
      Acorn.FeatureConstants.skillCount * (actions.word.toNat + 3) + discounts.length := by
  have skillCount (skills : List (Skill actions config criterion dimension discounts)) :
      (skills.flatMap Skill.readers).length = skills.length * (actions.word.toNat + 3) := by
    induction skills with
    | nil => simp
    | cons head tail ih => simp [Skill.reader_count, ih, Nat.add_mul, Nat.add_comm]
  simp [Ensemble.readers, Controller.reader_count, DemonBank.reader_count, skillCount, Nat.add_assoc]

theorem Controller.retire_readers {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (feature : FeatIdx dimension) :
    (controller.retire feature).readers = controller.readers.map (PackedLearner.retire feature) := by
  simp [Controller.retire_def, Controller.readers, Vector.toList_map, List.map_map, Function.comp_def,
    PackedLearner.retire]

theorem Model.retire_readers {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (feature : FeatIdx dimension) :
    (model.retire feature).readers = model.readers.map (PackedLearner.retire feature) := by
  cases model <;> rfl

theorem DemonBank.retire_readers {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) (feature : FeatIdx dimension) :
    (demons.retire feature).readers = demons.readers.map (PackedLearner.retire feature) := by
  induction demons with
  | nil => rfl
  | cons learner rest ih => simp [DemonBank.retire, DemonBank.readers, PackedLearner.retire, ih]

theorem Skill.retire_readers {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (feature : FeatIdx dimension) :
    (skill.retire feature).readers = skill.readers.map (PackedLearner.retire feature) := by
  simp [Skill.retire, Skill.readers, Controller.retire_readers, Model.retire_readers]

theorem Ensemble.retire_readers {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (feature : FeatIdx dimension) :
    (ensemble.retire feature).readers = ensemble.readers.map (PackedLearner.retire feature) := by
  simp [Ensemble.retire, Ensemble.readers, Controller.retire_readers, DemonBank.retire_readers,
    Vector.toList_map, List.flatMap_map, List.map_flatMap, Skill.retire_readers]

end Acorn.Features
