/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetRungCredit
import AcornVerif.CurrentTraceCounts

/-!
# On the first rung, the first decision after a first reward reads the traces

Question 3 of rbeauchamp/acorn#232 asks whether, after a first success, the greedy choice away
from the route repeats one action. This module states, for the rung's agent, what the first
decision after a member's first reward reads. It is the opening statement of that question, and
does not answer it.

Take a member's first success by the rung's agent
(`AcornVerif.CurrentConcealedTargetRungCredit.FirstSuccess`), within the agent's first 1000
decisions. The percept after that step carries the reward word one, and the agent's step on it
learns the reward. Times count the agent's decisions from zero.

- **The weights.** Right after that step, every row's weight on every slot reads the trace the
  row held there when the step began (`rung_weights`). The traces were laid by the agent's steps
  before the reward, which are the explorer's
  (`AcornVerif.CurrentConcealedTargetRung.rungExplorer`).
- **The value at the start.** Right after that step, the value of the action the agent took at
  the visit's first decision, at the frame it laid there, is above the tie window
  (`rung_start_value`). This is the statement of a frame that
  `AcornVerif.CurrentConcealedTargetRungCredit.rung_credit` makes of each of its slots.
- **The decision.** The agent's next action is one decision of primitive control over the policy
  whose value for each action is the total of the traces its row held on the slots of the frame
  the decision reads, from the explorer's state after the agent's decisions up to and including
  the one on the rewarded percept (`rung_choice`). It is
  `AcornVerif.CurrentFirstChoice.first_choice` at the rung's constants.
- **The frame the next decision reads.** Every two frames of the run share a slot: every percept
  of a member's visits carries the word of day phase zero, since the rung's world starts at the
  day's first step and a visit's seven steps stay within the day's first eighth
  (`rung_frames_share`, from `AcornVerif.CurrentConcealedTargetRungCredit.rung_day_word`). So at
  the agent's next decision, the value of the action taken at the visit's first decision, at the
  frame the next decision reads, is above the tie window (`rung_next_value`). After a success on
  a visit's last step, the next decision is the next visit's first.
- **After a success on the first visit.** Such a success is at the visit's second or third step:
  of the explorer's first seven actions only the second and the third name a direction, and
  after any other the body stands where it stood (`rung_first_visit`). The explorer's first three
  actions are pairwise different (`rung_early_distinct`), so each row taken before such a reward
  was taken once, and its trace total on a frame is the ordered sum of one word, taken once for
  each slot the frame holds of the frame the row laid
  (`AcornVerif.CurrentTraceCounts.loop_totals`). At the times three and four the explorer holds
  no committed run with a step left and begins none (`rung_calm`). So where the frame the next
  decision reads holds at least as many slots of the frame laid at the decision whose action met
  the target as of each earlier frame, the agent's first action after the step that learns the
  reward is that action again (`rung_early_repeat`). The condition on the frames is a
  hypothesis here. `AcornVerif.CurrentConcealedTargetRungFirstVisit` proves it for a first
  success at the first visit's second step, which exactly seven members have.

`rung_first_choice` states the decision of every member the agent solves on one of its first 125
visits, at the member's first success. `rung_found_choice` states it of the 102 members that
`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds` lists, each first solved within the first
72 visits.

What this does not say.

- Which action the decision takes, outside the case above. Outside a committed run, when the
  generator begins none, it is a near-maximum candidate of the trace totals
  (`AcornVerif.CurrentFirstChoice.first_choice_greedy`), and an action the agent took on none of
  the 119 steps before the reward is no candidate where the frame shares a slot with a frame laid
  at most nine steps before (`AcornVerif.CurrentFirstChoice.unlaid_excluded`), as every frame of
  the run does (`rung_frames_share`). That excludes no action for not having been taken at a
  first reward at a time from 39 to 576: at each of those times the explorer has taken every one
  of the nine actions on the 119 decisions before (`rung_taken`). No theorem lists the explorer's
  actions after its first 576. No theorem here says that two frames of the rung's run share more
  than one slot, so none here says without a hypothesis which of the actions taken before the
  reward is the candidate, or that there is only one.
  `AcornVerif.CurrentConcealedTargetRungFirstVisit` proves that the frames laid at the times zero
  and one are one frame, and with it names the action after a first success at the first visit's
  second step; of two frames laid on different observations no theorem counts the shared slots.
  And the explorer's sixth action repeats its fourth
  (`AcornVerif.CurrentConcealedTargetRungFinds.rung_actions`), so a first reward after the
  agent's first six decisions finds a row that was laid twice, and of such a row's total
  `AcornVerif.CurrentTraceCounts` says nothing.
- Anything of a later decision, and so nothing of whether one action is repeated: after the first
  reward the error of a later step need not be a zero word.
- That a member has its first success on the first visit. `rung_early_repeat` is stated of such
  a success and names none; `AcornVerif.CurrentConcealedTargetRungFirstVisit.second_step_repeats`
  lists the seven that have one at the visit's second step.
- Anything of a first success after the first 1000 decisions, or of another profile, criterion,
  rate policy or step order.

Trust. The statements are about executed binary32 words. Lean's kernel, its model of binary32
arithmetic and the agreement of the native operations with that model on finite operands remain
trusted, as for every proof of executed words in this library.
-/

namespace AcornVerif.CurrentConcealedTargetRungChoice
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentConcealedTargetRungFinds AcornVerif.CurrentConcealedTargetRungCredit
open AcornVerif.CurrentCreditHorizon AcornVerif.CurrentExplorer AcornVerif.CurrentFirstChoice
open AcornVerif.CurrentFirstCredit AcornVerif.CurrentFrameSlots AcornVerif.CurrentPreReward
open AcornVerif.CurrentTraceCounts

/-! ## Right after the step that learns the reward -/

/-- **Right after a member's first reward, every weight reads its trace.** At a member's first
success by the rung's agent, at step `step` of visit `visit` and within the agent's first 1000
decisions: right after the agent's step on the percept that carries that reward, every row's
weight on every slot reads the trace the row held there when that step began. -/
theorem rung_weights (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (visit step : ℕ) (first : FirstSuccess planning index (rungAgent planning) visit step)
    (early : visit * 8 + step < 1000) (row : Action Grid.interface.actions.word.toNat)
    (slot : FeatIdx (rungConstruction planning).dimension) :
    numerical32 (((controlOf (Kernel.memoryAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) (visit * 8 + step + 1))).learners.get row).state.weights.get
        slot).value =
      numerical32 (((controlOf (Kernel.memoryAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) (visit * 8 + step))).learners.get row).state.transient.z.get
        slot).value := by
  obtain ⟨silent, pays⟩ := rung_first_rewards planning index (rungAgent planning) visit step
    first
  exact first_reward_weights (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl
    (Agent.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config .discounted (rungConstruction planning).dimension
      planning) [] Quiet.initial ctrlQuiet_initial (rungVisits planning index)
    (rungOrigin planning index) (visit * 8 + step)
    (by change 0 + (visit * 8 + step) < 1000; omega) silent pays
    (fun time _ => Nat.le_trans (rung_laid planning index time) (by decide)) row slot

/-- **Right after a member's first reward, the value of its visit's first action at that visit's
start frame is above the tie window.** At a member's first success by the rung's agent, at step
`step` of visit `visit` and within the agent's first 1000 decisions: right after the agent's step
on the percept that carries that reward, the value of the action the agent took at the visit's
first decision, at the frame it laid there, reads more than the tie window of the greedy choice.
The frame holds a slot (`AcornVerif.CurrentConcealedTargetRung.rung_frame_slot`), and the value
is at least that slot's trace. -/
theorem rung_start_value (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (visit step : ℕ) (first : FirstSuccess planning index (rungAgent planning) visit step)
    (early : visit * 8 + step < 1000) :
    numerical32 tieWindow <
      numerical32 (((controlOf (Kernel.memoryAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) (visit * 8 + step + 1))).predictAll
          (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
            (rungOrigin planning index) (visit * 8)).features).get
        (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
          (rungOrigin planning index) (visit * 8)).row) := by
  obtain ⟨silent, pays⟩ := rung_first_rewards planning index (rungAgent planning) visit step
    first
  obtain ⟨low, high, -⟩ := first
  obtain ⟨slot, held⟩ := rung_frame_slot planning (rungConstruction planning).profile.taskMode
    .learnThenAct
    (Kernel.memoryAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      (visit * 8))
    (Kernel.stateAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      (visit * 8)).1
  have valued := shared_value (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl
    (Agent.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config .discounted (rungConstruction planning).dimension
      planning) [] Quiet.initial ctrlQuiet_initial (rungVisits planning index)
    (rungOrigin planning index) (visit * 8 + step)
    (by change 0 + (visit * 8 + step) < 1000; omega) silent pays
    (fun time _ => Nat.le_trans (rung_laid planning index time) (by decide)) (visit * 8)
    (by omega) (by omega) (Nat.le_trans (rung_laid planning index (visit * 8)) (by decide))
    (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
      (rungOrigin planning index) (visit * 8)).features
    (Nat.le_trans (rung_laid planning index (visit * 8)) (by decide)) slot held held
  exact lt_of_lt_of_le (lowChain_above_tie .discounted 8 le_rfl) valued

/-! ## The next decision -/

/-- **The first decision after a member's first reward reads the traces.** At a member's first
success by the rung's agent, at step `step` of visit `visit` and within the agent's first 1000
decisions: the agent's action right after its step on the percept that carries that reward is
one decision of primitive control, from the explorer's state after `visit * 8 + step + 1`
decisions, over the policy whose value for each action is the total of the traces its row held,
when that step began, on the slots of the frame the decision reads. -/
theorem rung_choice (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (visit step : ℕ) (first : FirstSuccess planning index (rungAgent planning) visit step)
    (early : visit * 8 + step < 1000) :
    Kernel.actionAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
        (visit * 8 + step + 1) =
      ((rungExplorer.after (visit * 8 + step + 1)).stepOver
        (tracePolicy
          (controlOf (Kernel.memoryAt (rungVisits planning index) (rungAgent planning)
            (rungOrigin planning index) (visit * 8 + step)))
          (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
            (rungOrigin planning index) (visit * 8 + step + 1)).features declaredRate)).1 := by
  obtain ⟨silent, pays⟩ := rung_first_rewards planning index (rungAgent planning) visit step
    first
  exact first_choice (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl rfl
    (Agent.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config .discounted (rungConstruction planning).dimension
      planning) [] Quiet.initial ctrlQuiet_initial (rungVisits planning index)
    (rungOrigin planning index) (visit * 8 + step)
    (by change 0 + (visit * 8 + step) < 1000; omega) silent pays
    (fun time _ => Nat.le_trans (rung_laid planning index time) (by decide))
    (Nat.le_trans (rung_laid planning index (visit * 8 + step + 1)) (by decide))

/-- **At a member's first success, the next decision reads the traces.** Every member of the
rung's class that the rung's agent solves on one of its first 125 visits has a first success on
one of them; and the agent's action right after its step on the percept that carries that reward
is one decision of primitive control over the policy of the trace totals, as `rung_choice` states
it. -/
theorem rung_first_choice (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (bound : ℕ) (within : bound ≤ 125)
    (solved : ∃ visit, visit < bound ∧ Kernel.SolvesOnVisit
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
      (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
      (rungAgent planning) visit index) :
    ∃ visit step, visit < bound ∧ FirstSuccess planning index (rungAgent planning) visit step ∧
      Kernel.actionAt (rungVisits planning index) (rungAgent planning)
          (rungOrigin planning index) (visit * 8 + step + 1) =
        ((rungExplorer.after (visit * 8 + step + 1)).stepOver
          (tracePolicy
            (controlOf (Kernel.memoryAt (rungVisits planning index) (rungAgent planning)
              (rungOrigin planning index) (visit * 8 + step)))
            (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
              (rungOrigin planning index) (visit * 8 + step + 1)).features declaredRate)).1 := by
  obtain ⟨visit, step, before, first⟩ :=
    rung_first_success planning index (rungAgent planning) bound solved
  exact ⟨visit, step, before, first, rung_choice planning index visit step first (by
    obtain ⟨-, high, -⟩ := first
    omega)⟩

/-- **Each member the rung's agent is proved to find has its next decision read the traces.**
There are 102 distinct members of the rung's class, those of
`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds`, each of which the agent first solves on
one of its first 72 visits, and for each of which the conclusion of `rung_first_choice` holds at
that first success. -/
theorem rung_found_choice (planning : PlanningSelection) :
    ∃ counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index,
      counted.Nodup ∧ counted.length = 102 ∧ ∀ index ∈ counted,
        ∃ visit step, visit < 72 ∧
          FirstSuccess planning index (rungAgent planning) visit step ∧
          Kernel.actionAt (rungVisits planning index) (rungAgent planning)
              (rungOrigin planning index) (visit * 8 + step + 1) =
            ((rungExplorer.after (visit * 8 + step + 1)).stepOver
              (tracePolicy
                (controlOf (Kernel.memoryAt (rungVisits planning index) (rungAgent planning)
                  (rungOrigin planning index) (visit * 8 + step)))
                (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
                  (rungOrigin planning index) (visit * 8 + step + 1)).features
                declaredRate)).1 := by
  obtain ⟨counted, distinct, size, solved, -⟩ := rung_finds planning
  exact ⟨counted, distinct, size, fun index member =>
    rung_first_choice planning index 72 (by decide) (solved index member)⟩

/-! ## The frame the next decision reads -/

/-- **Every two frames of the rung's run share a slot.** Every percept of a member's visits
carries the word of day phase zero
(`AcornVerif.CurrentConcealedTargetRungCredit.rung_day_word`), and two frames whose percepts
carry a common word share a slot. -/
theorem rung_frames_share (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (one two : ℕ) :
    ∃ slot, slot ∈ (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) one).features.indices ∧
      slot ∈ (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) two).features.indices :=
  shared_slot
    (Kernel.memoryAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      one)
    (Kernel.memoryAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      two)
    .learnThenAct .learnThenAct _ _ ⟨0x41, 0⟩ (rung_day_word planning index one)
    (rung_day_word planning index two) (by
      change 0 < Acorn.FeatureConstants.defaultTilings.toUInt64.toNat
      decide)

/-- **At the decision after a member's first reward, the visit's first action is valued above the
tie window.** At a member's first success by the rung's agent, at step `step` of visit `visit`
and within the agent's first 1000 decisions: at the agent's next decision, the value of the
action the agent took at the visit's first decision, at the frame the next decision reads, is
above the tie window of the greedy choice. The step that learns the reward writes the weights
that decision freezes, and the two frames share a slot (`rung_frames_share`). After a success on
the visit's seventh step, the next decision is the next visit's first. -/
theorem rung_next_value (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (visit step : ℕ) (first : FirstSuccess planning index (rungAgent planning) visit step)
    (early : visit * 8 + step < 1000) :
    numerical32 tieWindow <
      numerical32 (((controlOf (Kernel.memoryAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) (visit * 8 + step + 1))).predictAll
          (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
            (rungOrigin planning index) (visit * 8 + step + 1)).features).get
        (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
          (rungOrigin planning index) (visit * 8)).row) := by
  obtain ⟨silent, pays⟩ := rung_first_rewards planning index (rungAgent planning) visit step
    first
  obtain ⟨low, high, -⟩ := first
  obtain ⟨slot, heldLaid, heldNext⟩ := rung_frames_share planning index (visit * 8)
    (visit * 8 + step + 1)
  have valued := shared_value (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl
    (Agent.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config .discounted (rungConstruction planning).dimension
      planning) [] Quiet.initial ctrlQuiet_initial (rungVisits planning index)
    (rungOrigin planning index) (visit * 8 + step)
    (by change 0 + (visit * 8 + step) < 1000; omega) silent pays
    (fun time _ => Nat.le_trans (rung_laid planning index time) (by decide)) (visit * 8)
    (by omega) (by omega) (Nat.le_trans (rung_laid planning index (visit * 8)) (by decide))
    (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
      (rungOrigin planning index) (visit * 8 + step + 1)).features
    (Nat.le_trans (rung_laid planning index (visit * 8 + step + 1)) (by decide)) slot heldLaid
    heldNext
  exact lt_of_lt_of_le (lowChain_above_tie .discounted 8 le_rfl) valued

/-! ## Which actions the explorer has taken -/

/-- The explorer's first 576 action codes in fourteen blocks of forty decisions, the first block
beginning at time 39: the eighty decisions before each block, or all of them where there are
fewer, hold every one of the nine codes. -/
theorem rung_codes : ((List.range 14).all fun block => (List.range 9).all fun code =>
    ((rungRows.flatten.drop (39 + 40 * block - 80)).take (min (39 + 40 * block) 80)).elem
      code) = true := by
  decide +kernel

/-- **On the rung the explorer soon takes every action.** Count the explorer's decisions from
time zero. At each time from 39 to 576, the explorer has taken each of the nine actions at one of
the 119 times before. So at a first reward at such a time, no action is excluded from the
candidates of the trace totals for not having been taken
(`AcornVerif.CurrentFirstChoice.unlaid_excluded`). -/
theorem rung_taken (time : ℕ) (low : 39 ≤ time) (high : time ≤ 576)
    (action : Action Grid.interface.actions.word.toNat) :
    ∃ earlier, earlier < time ∧ time ≤ earlier + 119 ∧
      rungExplorer.actionAt earlier = action := by
  have nine : action.val < 9 := action.isLt
  have size : rungRows.flatten.length = 576 := by decide +kernel
  have block : (time - 39) / 40 < 14 := by omega
  have listed := List.all_eq_true.mp (List.all_eq_true.mp rung_codes ((time - 39) / 40)
    (List.mem_range.mpr block)) action.val (List.mem_range.mpr nine)
  rw [List.elem_eq_mem, decide_eq_true_eq] at listed
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp listed
  rw [List.length_take, List.length_drop, size] at bound
  refine ⟨39 + 40 * ((time - 39) / 40) - 80 + index, by omega, by omega, Fin.ext ?_⟩
  rw [rung_action _ (by omega), ← same, List.getElem_take, List.getElem_drop,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [size]; omega)]
  rfl

/-! ## A first success on the first visit -/

/-- Within a member's first visit, the world's state after one more decision is the grid world's
step from the state before it, on the action taken there. It is `AcornVerif.Kernel.visits_step`
at the rung's world. -/
theorem rung_step_state (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (agent : Kernel.Agent Grid.interface) (time : ℕ) (within : time < 7) :
    (Kernel.stateAt (rungVisits planning index) agent (rungOrigin planning index) (time + 1)).1 =
      (gridWorld witnessConfig (rungConstruction planning).profile.taskMode).step
        (Kernel.stateAt (rungVisits planning index) agent (rungOrigin planning index) time).1
        (Kernel.actionAt (rungVisits planning index) agent (rungOrigin planning index) time) :=
  Kernel.visits_step (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
    (member witnessLive index.1.1) 7 agent time within

/-- Of the first seven codes that `rungRows` lists, all but the second and the third are codes
of actions that name no direction: to craft an axe, to eat, to harvest, and to eat twice. -/
theorem rung_still_codes : ∀ time, time < 7 → time ≠ 1 → time ≠ 2 →
    (Host.Action.fromIndex (rungRows.flatten.getD time 0)).direction = none := by
  decide +kernel

/-- **A first success on the first visit is at its second or third step.** The agent's actions
up to a first reward are the explorer's, and on the first visit only the second and the third of
them name a direction. After any other step the body stands where it stood before it
(`AcornVerif.CurrentStep.step_stays`): at the start after the first step, where no member's
target is met, and after a later one where the step before had not met the target. -/
theorem rung_first_visit (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (step : ℕ)
    (first : FirstSuccess planning index (rungAgent planning) 0 step) : step = 2 ∨ step = 3 := by
  obtain ⟨silent, -⟩ := rung_first_rewards planning index (rungAgent planning) 0 step first
  obtain ⟨low, high, -, unmet, met⟩ := first
  rw [Nat.zero_mul, Nat.zero_add] at silent met
  by_contra other
  obtain ⟨prev, rfl⟩ : ∃ prev, step = prev + 1 := ⟨step - 1, by omega⟩
  have explored : Kernel.actionAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) prev = rungExplorer.actionAt prev :=
    cold_actions (profile := (rungConstruction planning).profile)
      (config := (rungConstruction planning).config)
      (dimension := (rungConstruction planning).dimension) rfl rfl planning
      (rungVisits planning index) (rungOrigin planning index) prev
      (fun earlier sooner =>
        (congrArg Binary32.isZero (silent earlier (by omega))).trans (by decide))
  have still : (Host.Action.fromIndex (Kernel.actionAt (rungVisits planning index)
      (rungAgent planning) (rungOrigin planning index) prev).val).direction = none := by
    rw [explored, rung_action prev (by omega)]
    exact rung_still_codes prev (by omega) (by omega) (by omega)
  have next := rung_step_state planning index (rungAgent planning) prev (by omega)
  obtain ⟨after, reached, satisfied⟩ := met
  rw [next] at reached
  cases before : (Kernel.stateAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) prev).1 with
  | none =>
    rw [before] at reached
    cases reached
  | some prior =>
    rw [before] at reached
    have moved : advance prior (Kernel.actionAt (rungVisits planning index)
        (rungAgent planning) (rungOrigin planning index) prev) = some after := reached
    obtain ⟨events, stepped, -⟩ := advance_some prior after _ moved
    have stays := AcornVerif.CurrentStep.step_stays prior.world after.world _ events stepped
      still
    have goalPrior : prior.world.goal = some (.find index.1.1) :=
      visits_goal (rungConstruction planning).profile.taskMode witnessLive index.1.1 7
        (Kernel.actionAt (rungVisits planning index) (rungAgent planning)
          (rungOrigin planning index)) prev prior (by
            rw [← Kernel.stateAt_eq_path]
            exact before)
    have goalAfter : after.world.goal = some (.find index.1.1) :=
      (Host.World.step_goal _ _ _ _ stepped).1.trans goalPrior
    have inside := (AcornVerif.CurrentGoals.find_goal_iff after.world index.1.1 goalAfter).mp
      satisfied
    rw [stays] at inside
    rcases Nat.eq_zero_or_pos prev with zero | positive
    · subst zero
      have start : member witnessLive index.1.1 = some prior := before
      obtain rfl := Option.some.inj start
      exact index.1.2 inside
    · exact unmet prev positive (by omega) (by
        rw [Nat.zero_mul, Nat.zero_add]
        exact ⟨prior, before,
          (AcornVerif.CurrentGoals.find_goal_iff prior.world index.1.1 goalPrior).mpr inside⟩)

/-- The explorer's first three actions are pairwise different: their codes are six, one and two,
for crafting an axe, a step south and a step east. -/
theorem rung_early_distinct (one two : ℕ) (first : one < 3) (second : two < 3)
    (apart : one ≠ two) : rungExplorer.actionAt one ≠ rungExplorer.actionAt two := by
  intro same
  have codes := congrArg Fin.val same
  rw [rung_action one (by omega), rung_action two (by omega)] at codes
  have table : ∀ time, time < 3 → rungRows.flatten.getD time 0 = [6, 1, 2].getD time 0 := by
    decide +kernel
  rw [table one first, table two second] at codes
  have all : ∀ left, left < 3 → ∀ right, right < 3 → left ≠ right →
      [6, 1, 2].getD left 0 ≠ [6, 1, 2].getD right 0 := by decide
  exact all one first two second apart codes

/-- At the times three and four the explorer holds no committed run with a step left, and its
generator begins none at the declared rate. -/
theorem rung_calm (time : ℕ) (low : 3 ≤ time) (high : time ≤ 4) :
    (rungExplorer.after time).run.bind ExploratoryRun.serve = none ∧
      (beginExploration Grid.interface.actions declaredRate (rungExplorer.after time).rng).1 =
        none := by
  obtain rfl | rfl : time = 3 ∨ time = 4 := by omega
  all_goals decide +kernel

/-- **After a first success on the first visit, the agent takes again the action that met the
target, where the frames allow.** At a member's first success by the rung's agent on the first
visit, at step `last + 1`: suppose the frame the decision at the time `last + 2` reads holds at
least as many slots of the frame laid at the time `last` as of the frame laid at each earlier
time. Then the agent's action at the time `last + 2`, the first it takes after the step that
learns the reward, is the explorer's action at the time `last`, the action after which the target
was met. Such a success is at the visit's second or third step (`rung_first_visit`), so the
actions before the reward are among the explorer's first three, which are pairwise different;
every row taken before the reward then holds a fresh trace
(`AcornVerif.CurrentTraceCounts.loop_fresh`), the frames share a slot (`rung_frames_share`), and
at the times three and four the explorer is outside a run (`rung_calm`). -/
theorem rung_early_repeat (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (last : ℕ) (first : FirstSuccess planning index (rungAgent planning) 0 (last + 1))
    (most : ∀ earlier, earlier < last →
      ((laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) (last + 2)).features.indices.countP fun slot =>
        decide (slot ∈ (laidAt (rungConstruction planning).initial.agent
          (rungVisits planning index) (rungOrigin planning index) earlier).features.indices)) ≤
      (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) (last + 2)).features.indices.countP fun slot =>
        decide (slot ∈ (laidAt (rungConstruction planning).initial.agent
          (rungVisits planning index) (rungOrigin planning index) last).features.indices)) :
    Kernel.actionAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      (last + 2) = rungExplorer.actionAt last := by
  have reach := rung_first_visit planning index (last + 1) first
  obtain ⟨silent, pays⟩ := rung_first_rewards planning index (rungAgent planning) 0 (last + 1)
    first
  rw [Nat.zero_mul, Nat.zero_add] at silent pays
  have explored : ∀ time, time < last + 1 →
      Kernel.actionAt (rungVisits planning index) (rungAgent planning)
        (rungOrigin planning index) time = rungExplorer.actionAt time := fun time before =>
    cold_actions (profile := (rungConstruction planning).profile)
      (config := (rungConstruction planning).config)
      (dimension := (rungConstruction planning).dimension) rfl rfl planning
      (rungVisits planning index) (rungOrigin planning index) time
      (fun earlier sooner =>
        (congrArg Binary32.isZero (silent earlier (by omega))).trans (by decide))
  obtain ⟨slot, heldNext, heldLast⟩ := rung_frames_share planning index (last + 2) last
  have shares : 1 ≤ (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
      (rungOrigin planning index) (last + 2)).features.indices.countP fun slot =>
      decide (slot ∈ (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
        (rungOrigin planning index) last).features.indices) :=
    List.countP_pos_iff.mpr ⟨slot, heldNext, decide_eq_true heldLast⟩
  have calm := rung_calm (last + 2) (by omega) (by omega)
  have repeated := first_choice_last (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl rfl
    (Agent.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config .discounted (rungConstruction planning).dimension
      planning) Quiet.initial ctrlQuiet_initial (rungVisits planning index)
    (rungOrigin planning index) last (by omega)
    (by change 0 + (last + 1) < 1000; omega) silent pays
    (fun time _ => Nat.le_trans (rung_laid planning index time) (by decide))
    (Nat.le_trans (rung_laid planning index (last + 2)) (by decide))
    (fun one two early1 early2 apart same =>
      rung_early_distinct one two (by omega) (by omega) apart
        ((explored one early1).symm.trans (same.trans (explored two early2))))
    shares most calm.1 calm.2
  exact repeated.trans (explored last (by omega))

end AcornVerif.CurrentConcealedTargetRungChoice
