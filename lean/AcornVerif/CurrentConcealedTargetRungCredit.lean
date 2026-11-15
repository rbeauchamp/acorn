/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetRung
import AcornVerif.CurrentFirstCredit

/-!
# On the first rung, a first reward's credit reaches the start of its visit

Question 2 of rbeauchamp/acorn#232 asks whether, after a first success in a member, credit
reaches the start of the visit. Its test is the corrected one of rbeauchamp/acorn#140: credit has
not reached the start when the start frame's own credit is at most the tie window of the greedy
choice (`Acorn.Features.tieWindow`).

`rung_credit` answers it for the rung's agent. In the visits of a member, let the agent meet the
member's target for the first time at a step of a visit, within its first 1000 decisions. Then
after the agent's step on the percept that carries that reward, every slot of the frame laid at
the visit's first decision holds, in the row of the action taken there, a weight of at least the
least laid trace decayed once for each later step before the reward, and that word is above the
tie window. So by that test credit reaches the start, on every slot the start frame holds.
`rung_first_credit` states it of every member the agent solves on one of its first 125 visits,
which include the visits on which it solves the 102 members that
`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds` lists.

The proof reads the member's reward words and applies
`AcornVerif.CurrentFirstCredit.loop_first_credit`. At the start of each visit the reward word is
the one the host world carries, the zero word in the rung's world (`start_reward`); after each
step it is the word one when the step met the target and the zero word when it did not
(`reward_word_step`, `step_reward`). So the first reward of one arrives with the first step that
meets the target, at most seven decisions after the visit's first. Every frame of the run is
within the rung's bound (`AcornVerif.CurrentConcealedTargetRung.rung_frames`), and 1000 decisions
are within the declared tester's maturity threshold, so no slot is retired before the reward.

What this does not say.

- That the weight is still there at the start of the next visit: the steps that remain in the
  visit, and every later step, learn from it and can lower it.
- That the greedy choice at the next visit's start is the action of this visit's first decision.
  Other rows hold credit on the slots their own frames share with the start frame, and the next
  start frame differs from this one where the agent's own predictions are fed back. Questions 3
  and 4 of rbeauchamp/acorn#232 ask these.
- That the start frame holds a slot. The statement is of each slot it holds.
- Anything of a first success after the first 1000 decisions, when a unit can be replaced and its
  slot retired, or of another profile, criterion or step order.
- The weight's value. The word is a lower bound for a frame of at most 1900 slots, the least a
  laying step can write there.
-/

namespace AcornVerif.CurrentConcealedTargetRungCredit
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentCreditHorizon AcornVerif.CurrentFirstCredit AcornVerif.CurrentFrameSize

variable {config : Host.WorldConfig}

/-! ## The reward word in a member's visits -/

/-- **The grid world's reward word.** After every step of the grid world the reward word is the
word one when the step satisfies the installed goal and the zero word when it does not, the
refused state included. -/
theorem reward_word_step (mode : TaskFeatureMode) (state : Option (Live config))
    (action : Kernel.Act Grid.interface) :
    ((gridWorld config mode).percept ((gridWorld config mode).step state action)).reward =
      if goalMet ((gridWorld config mode).step state action) then Binary32.one
      else Binary32.zero := by
  cases state with
  | none => rfl
  | some live =>
    change ((gridWorld config mode).percept (advance live action)).reward =
      if goalMet (advance live action) then Binary32.one else Binary32.zero
    cases stepped : advance live action with
    | none => rfl
    | some next =>
      obtain ⟨events, moved, carried⟩ := advance_some live next action stepped
      have done := Host.World.step_completion _ _ _ _ moved
      change next.carried.reward = if next.world.goalSatisfied then Binary32.one else Binary32.zero
      rw [carried, ← done]
      change events.reward = _
      unfold Host.StepResult.reward
      cases events.done <;> rfl

/-- At the start of each visit of a member, the reward word is the one the host world carries. -/
theorem start_reward (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (length : ℕ) (agent : Kernel.Agent Grid.interface) (count : ℕ) :
    (Kernel.perceptAt (Kernel.visits (gridWorld config mode) (member live target) length) agent
      (Kernel.visitStart (gridWorld config mode) (member live target) length)
      (count * (length + 1))).reward = live.carried.reward := by
  unfold Kernel.perceptAt
  rw [Kernel.visits_period]
  rfl

/-- After each step of a visit of a member, the reward word is the word one when that step
satisfied the member's goal and the zero word when it did not. -/
theorem step_reward (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (length : ℕ) (agent : Kernel.Agent Grid.interface) (count step : ℕ) (low : 1 ≤ step)
    (high : step ≤ length) :
    (Kernel.perceptAt (Kernel.visits (gridWorld config mode) (member live target) length) agent
      (Kernel.visitStart (gridWorld config mode) (member live target) length)
      (count * (length + 1) + step)).reward =
      if goalMet (Kernel.stateAt (Kernel.visits (gridWorld config mode) (member live target)
          length) agent (Kernel.visitStart (gridWorld config mode) (member live target) length)
          (count * (length + 1) + step)).1 then Binary32.one
      else Binary32.zero := by
  obtain ⟨before, rfl⟩ : ∃ before, step = before + 1 := ⟨step - 1, by omega⟩
  have inner : (Kernel.stateAt (Kernel.visits (gridWorld config mode) (member live target)
      length) agent (Kernel.visitStart (gridWorld config mode) (member live target) length)
      (count * (length + 1) + (before + 1))).1 =
        Kernel.stateAt (gridWorld config mode)
          (agent.resume (Kernel.memoryAt (Kernel.visits (gridWorld config mode)
            (member live target) length) agent
            (Kernel.visitStart (gridWorld config mode) (member live target) length)
            (count * (length + 1)))) (member live target) (before + 1) := by
    rw [Kernel.stateAt_add, Kernel.visits_period]
    exact congrArg Prod.fst (congrArg Prod.fst
      (Kernel.visits_loop (gridWorld config mode) (member live target) length _ (before + 1)
        high))
  change ((gridWorld config mode).percept (Kernel.stateAt (Kernel.visits (gridWorld config mode)
    (member live target) length) agent
    (Kernel.visitStart (gridWorld config mode) (member live target) length)
    (count * (length + 1) + (before + 1))).1).reward = _
  rw [inner]
  exact reward_word_step mode _ _

/-! ## The first reward of a member reaches its visit's start -/

/-- The rung's agent as a kernel agent: the executed decision function from the cold state of the
rung's construction. -/
abbrev rungAgent (planning : PlanningSelection) : Kernel.Agent Grid.interface :=
  executedAgent (rungConstruction planning).initial.agent

/-- **Credit reaches the start.** In the visits of a member of the rung's class, let the rung's
agent meet the member's target for the first time at step `step` of visit `visit`, within its
first 1000 decisions. Then after the agent's step on the percept that carries that reward, every
slot of the frame it laid at the visit's first decision holds, in the row of the action it took
there, a weight that reads at least the least laid trace decayed once for each later step of the
visit before the reward (`AcornVerif.CurrentCreditHorizon.lowChain`), and that word is above the
tie window of the greedy choice. -/
theorem rung_credit (planning : PlanningSelection)
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
    ∀ slot ∈ ((Kernel.memoryAt world (rungAgent planning) origin (visit * 8)).choose .learnThenAct
        (Kernel.perceptAt world (rungAgent planning) origin (visit * 8))).features.indices,
      numerical32 tieWindow < numerical32 (lowChain .discounted (step - 1)) ∧
        numerical32 (lowChain .discounted (step - 1)) ≤
          numerical32 (((controlOf (Kernel.memoryAt world (rungAgent planning) origin
            (visit * 8 + step + 1))).learners.get
            ((Kernel.memoryAt world (rungAgent planning) origin (visit * 8)).choose .learnThenAct
              (Kernel.perceptAt world (rungAgent planning) origin
                (visit * 8))).decision.action).state.weights.get slot).value := by
  intro mode world origin unsolved unmet met slot held
  obtain ⟨gap, rfl⟩ : ∃ gap, step = gap + 1 := ⟨step - 1, by omega⟩
  have quietBefore : ∀ time, time < visit * 8 + (gap + 1) →
      (Kernel.perceptAt world (rungAgent planning) origin time).reward = Binary32.zero := by
    intro time before
    obtain ⟨count, rest, rfl, small⟩ : ∃ count rest, time = count * (7 + 1) + rest ∧ rest < 8 :=
      ⟨time / 8, time % 8, by omega, Nat.mod_lt _ (by decide)⟩
    cases rest with
    | zero => exact start_reward mode witnessLive index.1.1 7 (rungAgent planning) count
    | succ rest =>
      have notMet : ¬ (completion witnessConfig mode 7).satisfied
          (Kernel.stateAt world (rungAgent planning) origin (count * (7 + 1) + (rest + 1))).1 := by
        by_cases earlierVisit : count < visit
        · intro satisfied
          exact unsolved count earlierVisit ⟨rest + 1, by omega, by omega, satisfied⟩
        · have same : count = visit := by omega
          subst same
          exact unmet (rest + 1) (by omega) (by omega)
      have unpaid : goalMet (Kernel.stateAt world (rungAgent planning) origin
          (count * (7 + 1) + (rest + 1))).1 = false :=
        Bool.eq_false_iff.mpr (fun shown => notMet ((goalMet_iff mode 7 _).mp shown))
      rw [step_reward mode witnessLive index.1.1 7 (rungAgent planning) count (rest + 1)
        (by omega) (by omega), unpaid]
      rfl
  have paysAt : (Kernel.perceptAt world (rungAgent planning) origin (visit * 8 + 1 + gap)).reward =
      Binary32.one := by
    have time : visit * 8 + 1 + gap = visit * (7 + 1) + (gap + 1) := by omega
    have paid : goalMet (Kernel.stateAt world (rungAgent planning) origin
        (visit * (7 + 1) + (gap + 1))).1 = true := (goalMet_iff mode 7 _).mpr met
    rw [time, step_reward mode witnessLive index.1.1 7 (rungAgent planning) visit (gap + 1)
      (by omega) high, paid]
    rfl
  have delivered : ∀ times : List ℕ, Delivered witnessConfig mode
      (times.map (Kernel.perceptAt world (rungAgent planning) origin)) := by
    intro times percept member
    obtain ⟨time, -, rfl⟩ := List.mem_map.mp member
    exact ⟨(Kernel.stateAt world (rungAgent planning) origin time).1, rfl⟩
  have credited := loop_first_credit (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl planning world origin
    (visit * 8) gap (by omega) (by change visit * 8 + gap + 2 ≤ 1000; omega)
    (fun time bound => quietBefore time (by omega)) paysAt
    (fun laid member => Nat.le_trans
      (rung_frames planning mode .learnThenAct _ (delivered _) _ laid member) (by decide))
    (Nat.le_trans (rung_frames planning mode .learnThenAct _ (delivered [visit * 8])
      (Kernel.memoryAt world (rungAgent planning) origin (visit * 8)) _ List.mem_cons_self)
      (by decide))
    (fun laid member => Nat.le_trans
      (rung_frames planning mode .learnThenAct _ (delivered _) _ laid member) (by decide))
    slot held
  have time : visit * 8 + 1 + gap + 1 = visit * 8 + (gap + 1) + 1 := by omega
  rw [time] at credited
  exact ⟨lowChain_above_tie .discounted gap (by omega), credited⟩

/-- **At a member's first success, credit reaches the start of that visit.** Every member of the
rung's class that the rung's agent solves on one of its first 125 visits has a first visit and a
first step of it at which its target is met; and after the agent's step on the percept that
carries that reward, every slot of the frame laid at that visit's first decision holds, in the row
of the action taken there, a weight above the tie window of the greedy choice. -/
theorem rung_first_credit (planning : PlanningSelection)
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
      (completion witnessConfig mode 7).satisfied
        (Kernel.stateAt world (rungAgent planning) origin (visit * 8 + step)).1 ∧
      ∀ slot ∈ ((Kernel.memoryAt world (rungAgent planning) origin (visit * 8)).choose
          .learnThenAct (Kernel.perceptAt world (rungAgent planning) origin
            (visit * 8))).features.indices,
        numerical32 tieWindow <
          numerical32 (((controlOf (Kernel.memoryAt world (rungAgent planning) origin
            (visit * 8 + step + 1))).learners.get
            ((Kernel.memoryAt world (rungAgent planning) origin (visit * 8)).choose .learnThenAct
              (Kernel.perceptAt world (rungAgent planning) origin
                (visit * 8))).decision.action).state.weights.get slot).value := by
  classical
  intro mode world origin
  obtain ⟨some, before, once⟩ := solved
  have ever : ∃ visit, Kernel.SolvesOnVisit (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 (rungAgent planning) visit index :=
    ⟨some, once⟩
  have least : Nat.find ever ≤ some := Nat.find_min' ever once
  have stepped : ∃ step, 1 ≤ step ∧ step ≤ 7 ∧ (completion witnessConfig mode 7).satisfied
      (Kernel.stateAt world (rungAgent planning) origin (Nat.find ever * 8 + step)).1 :=
    Nat.find_spec ever
  obtain ⟨low, high, met⟩ := Nat.find_spec stepped
  have credit := rung_credit planning index (Nat.find ever) (Nat.find stepped) low high
    (by omega) (fun earlier sooner => Nat.find_min ever sooner)
    (fun sooner lowSooner early satisfied =>
      Nat.find_min stepped early ⟨lowSooner, by omega, satisfied⟩) met
  exact ⟨Nat.find ever, Nat.find stepped, by omega, low, high,
    fun earlier sooner => Nat.find_min ever sooner, met,
    fun slot held => lt_of_lt_of_le (credit slot held).1 (credit slot held).2⟩

end AcornVerif.CurrentConcealedTargetRungCredit
