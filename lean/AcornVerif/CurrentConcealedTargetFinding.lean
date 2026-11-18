/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetMission
import AcornVerif.CurrentExplorer

/-!
# What the executed agent finds among the concealed targets

`AcornVerif.CurrentConcealedTargetMission.ExecutedFinds` says that the executed agent solves
each of more counted members than the covering bound on some visit, and the premise of the
mission theorem, `AcornVerif.CurrentConcealedTargetMission.ExecutedFindsBy`, says so with a visit
before which each is solved. This module reduces both, for the cold agent of a profile with no
hierarchy under the declared exploration rate, over a host world that carries the zero reward
word, to statements that read no learner: which concealed targets the walks of one fixed action
sequence meet, and by which visit.

Two results give the reduction.

- A member is solved on some visit exactly when the actions of the agent's run in the reference
  meet its goal on some visit (`AcornVerif.Kernel.Conceals.found_iff`). The reference of this
  class is the same world with the target `nowhere` installed, which no state satisfies.
- In the reference of a host world that carries the zero reward word, no reward is ever paid:
  every state on every run delivers the zero reward word (`reference_unpaid`). So the cold
  agent's run there is its run before a first reward, on which it takes the actions of the
  explorer of its seed (`AcornVerif.CurrentExplorer.cold_actions`, `reference_actions`).

`cold_finds_iff` is the result: the cold agent finds exactly when, for more counted members than
the covering bound, the explorer's actions on some visit meet the member's target within the
visit, and `cold_found_within` is the same with a number of visits stated.
`AcornVerif.CurrentConcealedTarget.find_near_met` gives the form a computation can check: a
target within three tiles of the tile the body stands on after one of a visit's steps is met
there, and `tileTrace` computes those tiles in one pass over the executed world step
(`tileTrace_path`).

The explorer's actions are a function of the feature configuration's seed
(`AcornVerif.CurrentExplorer.Explorer.cold`). Whether its walks meet more targets than the
covering bound in a given world is therefore a property of one seed and one terrain, which a
finite evaluation of the executed generator and world step can decide for a stated number of
visits. This module does not evaluate them. It proves nothing about retention: what the agent
does after its first reward is outside it.
-/

namespace AcornVerif.CurrentConcealedTargetFinding
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentConcealedTargetMission
open AcornVerif.CurrentExplorer

variable {config : Host.WorldConfig}

/-! ## No reward in the reference -/

/-- A state of the grid world at which nothing is paid and from which nothing will be: the refused
state, or a live state with the target `nowhere` installed that carries the zero reward word. -/
def Unpaid : Option (Live config) → Prop
  | none => True
  | some live => live.world.goal = some (.find nowhere) ∧ live.carried.reward = ⟨0⟩

/-- Every step keeps a state unpaid: no step replaces the installed goal, and no world satisfies
the target `nowhere`. -/
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

/-- An unpaid state delivers the zero reward word. -/
theorem unpaid_reward (mode : TaskFeatureMode) (state : Option (Live config))
    (held : Unpaid state) : ((gridWorld config mode).percept state).reward = ⟨0⟩ := by
  cases state with
  | none => rfl
  | some live => exact held.2

/-- **No reward in the reference.** In the reference's visits, from a host world that carries the
zero reward word, every agent receives the zero reward word at every time. -/
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

/-! ## The cold agent's run in the reference -/

variable {profile : FeatureProfile} {features : Features.Config} {criterion : Criterion}
  {dimension : Dimension}

/-- **In the reference the cold agent takes the explorer's actions.** For a profile with no
hierarchy under the declared rate, from a host world that carries the zero reward word: on every
visit of the reference's visits, the cold agent's action at each decision is the action of the
explorer of its seed at that decision's time. -/
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

/-- **What the cold agent has found by a visit is what the explorer's walks have met by it.** For
a profile with no hierarchy under the declared rate, over a host world that carries the zero
reward word: the cold agent solves a member on one of its first `count` visits exactly when the
explorer's actions on one of those visits meet the member's target within the visit. -/
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

/-- **Finding, for the cold agent, is a property of the explorer's walks.** For a profile with no
hierarchy under the declared rate, over a host world that carries the zero reward word: the cold
agent finds exactly when there are more counted members than the covering bound `49 + 7 length`
each of whose targets the explorer's actions meet on some visit, within the visit. The right-hand
side reads the feature configuration's seed and the world, and no learner. -/
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

/-! ## A walk in one pass -/

/-- The tile the body stands on after each of a list of actions, from a world of the dynamics
without the goal, in one pass over the executed world step. A refused step and every step after
it give none. -/
def tileTrace (state : Option (Host.World config)) : List Host.Action → List (Option (ℤ × ℤ))
  | [] => []
  | action :: rest =>
    match state.bind (physicalStep · (code action)) with
    | none => none :: tileTrace none rest
    | some world => some (tile world.body.position.position) :: tileTrace (some world) rest

/-- The trace of a list of actions starts with the tile after the first, and continues from the
world after it. -/
theorem tileTrace_cons (state : Option (Host.World config)) (action : Host.Action)
    (rest : List Host.Action) :
    tileTrace state (action :: rest) =
      (state.bind (physicalStep · (code action))).map
          (fun world => tile world.body.position.position) ::
        tileTrace (state.bind (physicalStep · (code action))) rest := by
  cases stepped : state.bind (physicalStep · (code action)) with
  | none => simp only [tileTrace, stepped, Option.map_none]
  | some world => simp only [tileTrace, stepped, Option.map_some]

/-- **The trace is the walk.** Where an action sequence takes the listed actions from a time on,
the trace of the list from the world of that time holds, at each of its places, the tile of the
dynamics' path one step later. -/
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
