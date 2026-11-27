import AcornVerif.CurrentConcealedTargetMission
import AcornVerif.CurrentExplorer

namespace AcornVerif.CurrentConcealedTargetFinding
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentConcealedTargetMission
open AcornVerif.CurrentExplorer

variable {config : Host.WorldConfig}

def Unpaid : Option (Live config) → Prop
  | none => True
  | some live => live.world.goal = some (.find nowhere) ∧ live.carried.reward = ⟨0⟩

theorem unpaid_step (mode : TaskFeatureMode) (state : Option (Live config))
    (action : Kernel.Act Grid.interface) (held : Unpaid state) :
    Unpaid ((gridWorld config mode).step state action) := by
  cases state with
  | none => exact trivial
  | some live =>
    change Unpaid (advance live action)
    cases stepped : advance live action with
    | none => exact trivial
    | some next =>
      obtain ⟨events, moved, carried⟩ := advance_some live next action stepped
      have installed : next.world.goal = some (.find nowhere) :=
        (Host.World.step_goal _ _ _ _ moved).1.trans held.1
      have done : events.done = false :=
        (Host.World.step_completion _ _ _ _ moved).trans (nowhere_unmet next.world installed)
      refine ⟨installed, ?_⟩
      rw [carried]
      change events.reward = ⟨0⟩
      unfold Host.StepResult.reward
      rw [done]
      rfl

theorem unpaid_reward (mode : TaskFeatureMode) (state : Option (Live config))
    (held : Unpaid state) : ((gridWorld config mode).percept state).reward = ⟨0⟩ := by
  cases state with
  | none => rfl
  | some live => exact held.2

theorem reference_unpaid (mode : TaskFeatureMode) (live : Live config)
    (fresh : live.carried.reward = ⟨0⟩) (length : ℕ) (agent : Kernel.Agent Grid.interface)
    (time : ℕ) :
    (Kernel.perceptAt (Kernel.visits (gridWorld config mode) (member live nowhere) length) agent
      (Kernel.visitStart (gridWorld config mode) (member live nowhere) length) time).reward =
        ⟨0⟩ := by
  have origin : Unpaid (member live nowhere) := ⟨rfl, fresh⟩
  have every : ∀ state,
      Kernel.Reachable (Kernel.visits (gridWorld config mode) (member live nowhere) length)
        (Kernel.visitStart (gridWorld config mode) (member live nowhere) length) state →
      Unpaid state.1 := by
    intro state reachable
    induction reachable with
    | here => exact origin
    | next earlier action ih =>
      rename_i before
      change Unpaid (if within : before.2.val < length then
        ((gridWorld config mode).step before.1 action, (⟨before.2.val + 1, by omega⟩ :
          Fin (length + 1)))
        else (member live nowhere, ⟨0, Nat.succ_pos length⟩)).1
      split
      · exact unpaid_step mode before.1 action ih
      · exact origin
  exact unpaid_reward mode _ (every _ (Kernel.stateAt_reachable _ agent _ time))

variable {profile : FeatureProfile} {features : Features.Config} {criterion : Criterion}
  {dimension : Dimension}

theorem reference_actions (primitive : profile.usesHierarchy = false)
    (declared : profile.rate = .declared) (planning : PlanningSelection)
    (mode : TaskFeatureMode) (live : Live config) (fresh : live.carried.reward = ⟨0⟩)
    (length visit step : ℕ) :
    Kernel.visitActions (gridWorld config mode) (member live nowhere) length
        (executedAgent (Agent.initial Grid.interface profile features criterion dimension
          planning)) visit step =
      (Explorer.cold Grid.interface.actions features.seed).actionAt
        (visit * (length + 1) + step) :=
  cold_actions primitive declared planning _ _ _ (fun earlier _ => by
    rw [reference_unpaid mode live fresh length _ earlier]
    rfl)

theorem cold_found_within (primitive : profile.usesHierarchy = false)
    (declared : profile.rate = .declared) (planning : PlanningSelection)
    (live : Live config) (fresh : live.carried.reward = ⟨0⟩) (length count : ℕ)
    (index : (feasibleFind config profile.taskMode live length).Index) :
    (∃ visit, visit < count ∧
        Kernel.SolvesOnVisit (feasibleFind config profile.taskMode live length)
          (fun _ => completion config profile.taskMode length) length
          (executedAgent (Agent.initial Grid.interface profile features criterion dimension
            planning)) visit index) ↔
      ∃ visit, visit < count ∧
        (completion config profile.taskMode length).MetBy (member live index.1.1)
          (fun step => (Explorer.cold Grid.interface.actions features.seed).actionAt
            (visit * (length + 1) + step)) := by
  have walks : ∀ visit,
      Kernel.visitActions (gridWorld config profile.taskMode) (member live nowhere) length
          (executedAgent (Agent.initial Grid.interface profile features criterion dimension
            planning)) visit =
        fun step => (Explorer.cold Grid.interface.actions features.seed).actionAt
          (visit * (length + 1) + step) :=
    fun visit => funext fun step =>
      reference_actions primitive declared planning profile.taskMode live fresh length visit step
  rw [Kernel.Conceals.found_within (feasibleFind_conceals profile.taskMode live length length)]
  simp only [walks]
  rfl

theorem cold_finds_iff (primitive : profile.usesHierarchy = false)
    (declared : profile.rate = .declared) (planning : PlanningSelection)
    (live : Live config) (fresh : live.carried.reward = ⟨0⟩) (length : ℕ)
    (counted : List (feasibleFind config profile.taskMode live length).Index) :
    ExecutedFinds (Agent.initial Grid.interface profile features criterion dimension planning)
        config live length counted ↔
      ∃ solved : Finset (feasibleFind config profile.taskMode live length).Index,
        49 + 7 * length < solved.card ∧ ∀ index ∈ solved, index ∈ counted ∧
          ∃ visit, (completion config profile.taskMode length).MetBy (member live index.1.1)
            (fun step => (Explorer.cold Grid.interface.actions features.seed).actionAt
              (visit * (length + 1) + step)) := by
  have walks : ∀ visit,
      Kernel.visitActions (gridWorld config profile.taskMode) (member live nowhere) length
          (executedAgent (Agent.initial Grid.interface profile features criterion dimension
            planning)) visit =
        fun step => (Explorer.cold Grid.interface.actions features.seed).actionAt
          (visit * (length + 1) + step) :=
    fun visit => funext fun step =>
      reference_actions primitive declared planning profile.taskMode live fresh length visit step
  unfold ExecutedFinds
  rw [Kernel.Conceals.finds_iff (feasibleFind_conceals profile.taskMode live length length)]
  simp only [walks]
  rfl

def tileTrace (state : Option (Host.World config)) : List Host.Action → List (Option (ℤ × ℤ))
  | [] => []
  | action :: rest =>
    match state.bind (physicalStep · (code action)) with
    | none => none :: tileTrace none rest
    | some world => some (tile world.body.position.position) :: tileTrace (some world) rest

theorem tileTrace_cons (state : Option (Host.World config)) (action : Host.Action)
    (rest : List Host.Action) :
    tileTrace state (action :: rest) =
      (state.bind (physicalStep · (code action))).map
          (fun world => tile world.body.position.position) ::
        tileTrace (state.bind (physicalStep · (code action))) rest := by
  cases stepped : state.bind (physicalStep · (code action)) with
  | none => simp only [tileTrace, stepped, Option.map_none]
  | some world => simp only [tileTrace, stepped, Option.map_some]

theorem tileTrace_path (start : Host.World config) (actions : ℕ → Kernel.Act Grid.interface) :
    ∀ (listed : List Host.Action) (done : ℕ),
      (∀ index, index < listed.length →
        actions (done + index) = code (listed.getD index .wait)) →
      ∀ step, step < listed.length →
        (tileTrace (physicalPath start actions done) listed)[step]? =
          some ((physicalPath start actions (done + step + 1)).map
            (fun world => tile world.body.position.position)) := by
  intro listed
  induction listed with
  | nil => exact fun _ _ step within => absurd within (Nat.not_lt_zero step)
  | cons action rest ih =>
    intro done taken step within
    have first : actions done = code action := taken 0 (Nat.succ_pos rest.length)
    have advanced : (physicalPath start actions done).bind (physicalStep · (code action)) =
        physicalPath start actions (done + 1) := by
      rw [← first]
      rfl
    rw [tileTrace_cons, advanced]
    cases step with
    | zero => rfl
    | succ step =>
      rw [List.getElem?_cons_succ, ih (done + 1) (fun index inside => by
        have shifted := taken (index + 1) (Nat.succ_lt_succ inside)
        rw [List.getD_cons_succ] at shifted
        rw [← shifted]
        exact congrArg actions (show done + 1 + index = done + (index + 1) by omega)) step
        (Nat.lt_of_succ_lt_succ within)]
      exact congrArg (fun time => some ((physicalPath start actions time).map
        (fun world => tile world.body.position.position)))
        (show done + 1 + step + 1 = done + (step + 1) + 1 by omega)

end AcornVerif.CurrentConcealedTargetFinding
