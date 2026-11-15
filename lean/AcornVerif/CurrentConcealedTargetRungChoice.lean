/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetRungCredit
import AcornVerif.CurrentFirstChoice

/-!
# On the first rung, the first decision after a first reward reads the traces

Question 3 of rbeauchamp/acorn#232 asks whether, after a first success, the greedy choice away
from the route repeats one action. This module states, for the rung's agent, what the first
decision after a member's first reward reads. It is the opening statement of that question, and
does not answer it.

In the visits of a member, let the agent meet the member's target for the first time at a step of
a visit, within its first 1000 decisions. The percept after that step carries the reward word
one, and the agent's step on it learns the reward.

- **The weights.** Right after that step, every row's weight on every slot reads the trace the
  row held there when the step began (`rung_weights`). The traces were laid by the agent's steps
  before the reward, which are the explorer's
  (`AcornVerif.CurrentConcealedTargetRung.rungExplorer`).
- **The value at the start.** Right after that step, the value of the action the agent took at
  the visit's first decision, at the frame it laid there, is above the tie window
  (`rung_start_value`). This is the statement of a frame that
  `AcornVerif.CurrentConcealedTargetRungCredit.rung_credit` makes of each of its slots.
- **The decision.** The agent's next action is one decision of primitive control, from the
  explorer's state after that many decisions, over the policy whose value for each action is the
  total of the traces its row held on the slots of the frame the decision reads (`rung_choice`).
  It is `AcornVerif.CurrentFirstChoice.first_choice` at the rung's constants.

`rung_first_choice` states the decision of every member the agent solves on one of its first 125
visits, at the member's first success. `rung_found_choice` states it of the 102 members that
`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds` lists, each first solved within the first
72 visits.

What this does not say.

- Which action the decision takes. Outside a committed run, when the generator begins none, it is
  a near-maximum candidate of the trace totals
  (`AcornVerif.CurrentFirstChoice.first_choice_greedy`), and an action the agent took on none of
  the 119 steps before the reward is no candidate where the frame shares a slot with a frame laid
  at most nine steps before (`AcornVerif.CurrentFirstChoice.unlaid_excluded`). On the rung that
  excludes an action only at a first reward among the agent's first 38 decisions: from the 39th
  to the 576th, the explorer has taken every one of the nine actions on the 119 decisions before
  (`rung_taken`). No theorem evaluates a trace total of the rung's run, so none says which of the
  actions taken before the reward is the candidate, or that there is only one. Nor does a theorem
  say that the frame of that decision shares a slot with an earlier one: every frame of the rung
  holds a slot (`AcornVerif.CurrentConcealedTargetRung.rung_frame_slot`), and two frames whose
  percepts carry a common word share one (`AcornVerif.CurrentFrameSize.shared_slot`), but no
  theorem names a word that two percepts of the run carry.
- Anything of a later decision, and so nothing of whether one action is repeated: after the first
  reward the errors of the agent's steps are not zero words.
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
open AcornVerif.CurrentFirstCredit AcornVerif.CurrentPreReward

/-- **Right after a member's first reward, every weight reads its trace.** In the visits of a
member of the rung's class, let the rung's agent meet the member's target for the first time at
step `step` of visit `visit`, within its first 1000 decisions. Then right after the agent's step
on the percept that carries that reward, every row's weight on every slot reads the trace the row
held there when that step began. -/
theorem rung_weights (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (visit step : ℕ) (low : 1 ≤ step) (high : step ≤ 7) (early : visit * 8 + step < 1000) :
    let mode := (rungConstruction planning).profile.taskMode
    let world := Kernel.visits (gridWorld witnessConfig mode) (member witnessLive index.1.1) 7
    let origin := Kernel.visitStart (gridWorld witnessConfig mode) (member witnessLive index.1.1) 7
    (∀ earlier, earlier < visit →
      ¬ Kernel.SolvesOnVisit (feasibleFind witnessConfig mode witnessLive 7)
        (fun _ => completion witnessConfig mode 7) 7 (rungAgent planning) earlier index) →
    (∀ sooner, 1 ≤ sooner → sooner < step → ¬ (completion witnessConfig mode 7).satisfied
      (Kernel.stateAt world (rungAgent planning) origin (visit * 8 + sooner)).1) →
    (completion witnessConfig mode 7).satisfied
      (Kernel.stateAt world (rungAgent planning) origin (visit * 8 + step)).1 →
    ∀ (row : Action Grid.interface.actions.word.toNat)
      (slot : FeatIdx (rungConstruction planning).dimension),
      numerical32 (((controlOf (Kernel.memoryAt world (rungAgent planning) origin
          (visit * 8 + step + 1))).learners.get row).state.weights.get slot).value =
        numerical32 (((controlOf (Kernel.memoryAt world (rungAgent planning) origin
          (visit * 8 + step))).learners.get row).state.transient.z.get slot).value := by
  intro mode world origin unsolved unmet met
  obtain ⟨silent, pays⟩ := rung_first_rewards planning index (rungAgent planning) visit step low
    high unsolved unmet met
  exact first_reward_weights (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl
    (Agent.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config .discounted (rungConstruction planning).dimension
      planning) [] Quiet.initial ctrlQuiet_initial world origin (visit * 8 + step)
    (by change 0 + (visit * 8 + step) < 1000; omega) silent pays
    (fun time _ => Nat.le_trans (rung_frame planning mode .learnThenAct
      (Kernel.memoryAt world (rungAgent planning) origin time)
      (Kernel.stateAt world (rungAgent planning) origin time).1) (by decide))

/-- **Right after a member's first reward, the value of its visit's first action at that visit's
start frame is above the tie window.** In the visits of a member of the rung's class, let the
rung's agent meet the member's target for the first time at step `step` of visit `visit`, within
its first 1000 decisions. Then right after the agent's step on the percept that carries that
reward, the value of the action the agent took at the visit's first decision, at the frame it
laid there, reads more than the tie window of the greedy choice. The frame holds a slot
(`AcornVerif.CurrentConcealedTargetRung.rung_frame_slot`), and the value is at least that slot's
trace. -/
theorem rung_start_value (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (visit step : ℕ) (low : 1 ≤ step) (high : step ≤ 7) (early : visit * 8 + step < 1000) :
    let mode := (rungConstruction planning).profile.taskMode
    let world := Kernel.visits (gridWorld witnessConfig mode) (member witnessLive index.1.1) 7
    let origin := Kernel.visitStart (gridWorld witnessConfig mode) (member witnessLive index.1.1) 7
    (∀ earlier, earlier < visit →
      ¬ Kernel.SolvesOnVisit (feasibleFind witnessConfig mode witnessLive 7)
        (fun _ => completion witnessConfig mode 7) 7 (rungAgent planning) earlier index) →
    (∀ sooner, 1 ≤ sooner → sooner < step → ¬ (completion witnessConfig mode 7).satisfied
      (Kernel.stateAt world (rungAgent planning) origin (visit * 8 + sooner)).1) →
    (completion witnessConfig mode 7).satisfied
      (Kernel.stateAt world (rungAgent planning) origin (visit * 8 + step)).1 →
    numerical32 tieWindow <
      numerical32 (((controlOf (Kernel.memoryAt world (rungAgent planning) origin
        (visit * 8 + step + 1))).predictAll
          (laidAt (rungConstruction planning).initial.agent world origin (visit * 8)).features).get
        (laidAt (rungConstruction planning).initial.agent world origin (visit * 8)).row) := by
  intro mode world origin unsolved unmet met
  obtain ⟨silent, pays⟩ := rung_first_rewards planning index (rungAgent planning) visit step low
    high unsolved unmet met
  have framed : ∀ time, (laidAt (rungConstruction planning).initial.agent world origin
      time).features.indices.length ≤ 1712 := fun time =>
    rung_frame planning mode .learnThenAct
      (Kernel.memoryAt world (rungAgent planning) origin time)
      (Kernel.stateAt world (rungAgent planning) origin time).1
  obtain ⟨slot, held⟩ := rung_frame_slot planning mode .learnThenAct
    (Kernel.memoryAt world (rungAgent planning) origin (visit * 8))
    (Kernel.stateAt world (rungAgent planning) origin (visit * 8)).1
  have valued := shared_value (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl
    (Agent.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config .discounted (rungConstruction planning).dimension
      planning) Quiet.initial ctrlQuiet_initial world origin (visit * 8 + step)
    (by change 0 + (visit * 8 + step) < 1000; omega) silent pays
    (fun time _ => Nat.le_trans (framed time) (by decide)) (visit * 8) (by omega) (by omega)
    (laidAt (rungConstruction planning).initial.agent world origin (visit * 8)).features
    (Nat.le_trans (framed (visit * 8)) (by decide)) slot held held
  exact lt_of_lt_of_le (lowChain_above_tie .discounted 8 le_rfl) valued

/-- **The first decision after a member's first reward reads the traces.** In the visits of a
member of the rung's class, let the rung's agent meet the member's target for the first time at
step `step` of visit `visit`, within its first 1000 decisions. Then the agent's action right after
its step on the percept that carries that reward is one decision of primitive control, from the
explorer's state after that many decisions, over the policy whose value for each action is the
total of the traces its row held, when that step began, on the slots of the frame the decision
reads. -/
theorem rung_choice (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (visit step : ℕ) (low : 1 ≤ step) (high : step ≤ 7) (early : visit * 8 + step < 1000) :
    let mode := (rungConstruction planning).profile.taskMode
    let world := Kernel.visits (gridWorld witnessConfig mode) (member witnessLive index.1.1) 7
    let origin := Kernel.visitStart (gridWorld witnessConfig mode) (member witnessLive index.1.1) 7
    (∀ earlier, earlier < visit →
      ¬ Kernel.SolvesOnVisit (feasibleFind witnessConfig mode witnessLive 7)
        (fun _ => completion witnessConfig mode 7) 7 (rungAgent planning) earlier index) →
    (∀ sooner, 1 ≤ sooner → sooner < step → ¬ (completion witnessConfig mode 7).satisfied
      (Kernel.stateAt world (rungAgent planning) origin (visit * 8 + sooner)).1) →
    (completion witnessConfig mode 7).satisfied
      (Kernel.stateAt world (rungAgent planning) origin (visit * 8 + step)).1 →
    Kernel.actionAt world (rungAgent planning) origin (visit * 8 + step + 1) =
      ((rungExplorer.after (visit * 8 + step + 1)).stepOver
        (tracePolicy
          (controlOf (Kernel.memoryAt world (rungAgent planning) origin (visit * 8 + step)))
          (laidAt (rungConstruction planning).initial.agent world origin
            (visit * 8 + step + 1)).features declaredRate)).1 := by
  intro mode world origin unsolved unmet met
  obtain ⟨silent, pays⟩ := rung_first_rewards planning index (rungAgent planning) visit step low
    high unsolved unmet met
  exact first_choice (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl rfl
    (Agent.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config .discounted (rungConstruction planning).dimension
      planning) [] Quiet.initial ctrlQuiet_initial world origin (visit * 8 + step)
    (by change 0 + (visit * 8 + step) < 1000; omega) silent pays
    (fun time _ => Nat.le_trans (rung_frame planning mode .learnThenAct
      (Kernel.memoryAt world (rungAgent planning) origin time)
      (Kernel.stateAt world (rungAgent planning) origin time).1) (by decide))

/-- **At a member's first success, the next decision reads the traces.** Every member of the
rung's class that the rung's agent solves on one of its first 125 visits has a first visit on
which its target is met and a first step of that visit at which it is met; and the agent's action
right after its step on the percept that carries that reward is one decision of primitive control
over the policy of the trace totals, as `rung_choice` states it. -/
theorem rung_first_choice (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (bound : ℕ) (within : bound ≤ 125)
    (solved : ∃ visit, visit < bound ∧ Kernel.SolvesOnVisit
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
      (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
      (rungAgent planning) visit index) :
    let mode := (rungConstruction planning).profile.taskMode
    let world := Kernel.visits (gridWorld witnessConfig mode) (member witnessLive index.1.1) 7
    let origin := Kernel.visitStart (gridWorld witnessConfig mode) (member witnessLive index.1.1) 7
    ∃ visit step, visit < bound ∧ 1 ≤ step ∧ step ≤ 7 ∧
      (∀ earlier, earlier < visit →
        ¬ Kernel.SolvesOnVisit (feasibleFind witnessConfig mode witnessLive 7)
          (fun _ => completion witnessConfig mode 7) 7 (rungAgent planning) earlier index) ∧
      (∀ sooner, 1 ≤ sooner → sooner < step → ¬ (completion witnessConfig mode 7).satisfied
        (Kernel.stateAt world (rungAgent planning) origin (visit * 8 + sooner)).1) ∧
      (completion witnessConfig mode 7).satisfied
        (Kernel.stateAt world (rungAgent planning) origin (visit * 8 + step)).1 ∧
      Kernel.actionAt world (rungAgent planning) origin (visit * 8 + step + 1) =
        ((rungExplorer.after (visit * 8 + step + 1)).stepOver
          (tracePolicy
            (controlOf (Kernel.memoryAt world (rungAgent planning) origin (visit * 8 + step)))
            (laidAt (rungConstruction planning).initial.agent world origin
              (visit * 8 + step + 1)).features declaredRate)).1 := by
  intro mode world origin
  obtain ⟨visit, step, before, low, high, unsolved, unmet, met⟩ :=
    rung_first_success planning index (rungAgent planning) bound solved
  exact ⟨visit, step, before, low, high, unsolved, unmet, met,
    rung_choice planning index visit step low high (by omega) unsolved unmet met⟩

/-- **Each member the rung's agent is proved to find has its next decision read the traces.**
There are 102 distinct members of the rung's class, those of
`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds`, each of which the agent first solves on
one of its first 72 visits, and for each of which the conclusion of `rung_first_choice` holds at
that first success. -/
theorem rung_found_choice (planning : PlanningSelection) :
    ∃ counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index,
      counted.Nodup ∧ counted.length = 102 ∧ ∀ index ∈ counted,
        ∃ visit step, visit < 72 ∧ 1 ≤ step ∧ step ≤ 7 ∧
          (∀ earlier, earlier < visit →
            ¬ Kernel.SolvesOnVisit
              (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
                witnessLive 7)
              (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7)
              7 (rungAgent planning) earlier index) ∧
          (∀ sooner, 1 ≤ sooner → sooner < step →
            ¬ (completion witnessConfig (rungConstruction planning).profile.taskMode 7).satisfied
              (Kernel.stateAt (Kernel.visits
                (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
                (member witnessLive index.1.1) 7) (rungAgent planning)
                (Kernel.visitStart
                  (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
                  (member witnessLive index.1.1) 7) (visit * 8 + sooner)).1) ∧
          (completion witnessConfig (rungConstruction planning).profile.taskMode 7).satisfied
            (Kernel.stateAt (Kernel.visits
              (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
              (member witnessLive index.1.1) 7) (rungAgent planning)
              (Kernel.visitStart
                (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
                (member witnessLive index.1.1) 7) (visit * 8 + step)).1 ∧
          Kernel.actionAt (Kernel.visits
              (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
              (member witnessLive index.1.1) 7) (rungAgent planning)
              (Kernel.visitStart
                (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
                (member witnessLive index.1.1) 7) (visit * 8 + step + 1) =
            ((rungExplorer.after (visit * 8 + step + 1)).stepOver
              (tracePolicy
                (controlOf (Kernel.memoryAt (Kernel.visits
                  (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
                  (member witnessLive index.1.1) 7) (rungAgent planning)
                  (Kernel.visitStart
                    (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
                    (member witnessLive index.1.1) 7) (visit * 8 + step)))
                (laidAt (rungConstruction planning).initial.agent (Kernel.visits
                  (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
                  (member witnessLive index.1.1) 7)
                  (Kernel.visitStart
                    (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
                    (member witnessLive index.1.1) 7) (visit * 8 + step + 1)).features
                declaredRate)).1 := by
  obtain ⟨counted, distinct, size, solved, -⟩ := rung_finds planning
  exact ⟨counted, distinct, size, fun index member =>
    rung_first_choice planning index 72 (by decide) (solved index member)⟩

/-! ## Which actions the explorer has taken -/

/-- The explorer's first 576 action codes in fourteen blocks of forty decisions from the 39th:
the eighty decisions before each block, or all of them where there are fewer, hold every one of
the nine codes. -/
theorem rung_codes : ((List.range 14).all fun block => (List.range 9).all fun code =>
    ((rungRows.flatten.drop (39 + 40 * block - 80)).take (min (39 + 40 * block) 80)).elem
      code) = true := by
  decide +kernel

/-- **On the rung the explorer soon takes every action.** At each time from its 39th decision to
its 576th, the explorer has taken each of the nine actions on one of the 119 decisions before.
So for a first reward at such a time, no action is excluded from the candidates of the trace
totals for not having been taken (`AcornVerif.CurrentFirstChoice.unlaid_excluded`). -/
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

end AcornVerif.CurrentConcealedTargetRungChoice
