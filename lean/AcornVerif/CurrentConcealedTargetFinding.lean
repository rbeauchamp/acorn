/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetMission
import AcornVerif.CurrentExplorer

/-!
# What the executed agent finds among the concealed targets

`AcornVerif.CurrentConcealedTargetMission.ExecutedFinds` is the premise that the executed agent
solves each of more counted members than the covering bound on some visit. This module reduces
it, for the cold agent of a profile with no hierarchy under the declared exploration rate, to a
statement that reads no learner: which concealed targets the walks of one fixed action sequence
meet.

Two results give the reduction.

- A member is solved on some visit exactly when the actions of the agent's run in the reference
  meet its goal on some visit (`AcornVerif.Kernel.Conceals.found_iff`). The reference of this
  class is the same world with the target `nowhere` installed, which no state satisfies.
- In the reference no reward is ever paid: every state on every run delivers the zero reward word
  (`reference_unpaid`). So the cold agent's run there is its run before a first reward, on which
  it takes the actions of the explorer of its seed (`AcornVerif.CurrentExplorer.cold_actions`,
  `reference_actions`).

`cold_finds_iff` is the result: the cold agent finds exactly when, for more counted members than
the covering bound, the explorer's actions on some visit meet the member's target within the
visit. `AcornVerif.CurrentConcealedTarget.find_near_met` gives the form a computation can check:
a target within three tiles of the tile the body stands on after one of a visit's steps is met
there.

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

end AcornVerif.CurrentConcealedTargetFinding
