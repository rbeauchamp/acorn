/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetRungFinds
import AcornVerif.CurrentFirstCredit

/-!
# On the first rung, a first reward's credit is written at the start of its visit

Question 2 of rbeauchamp/acorn#232 asks whether, after a first success in a member, credit
reaches the start of the next visit. Its test is the corrected one of rbeauchamp/acorn#140, which
reads the credit where the reward writes it and nothing of the next visit: credit has not reached
the start when the own credit of the successful visit's start frame is at most the tie window of
the greedy choice (`Acorn.Features.tieWindow`). The own credit is what that visit's first
decision laid on the frame's slots, as the reward finds it, summed over the slots.

`rung_credit` bounds each slot's weight for the rung's agent. In the visits of a member, let the
agent meet the member's target for the first time at a step of a visit, within its first 1000
decisions. Then right after the agent's step on the percept that carries that reward, every slot
of the frame laid at the visit's first decision holds, in the row of the action taken there, a
weight of at least `AcornVerif.CurrentCreditHorizon.lowChain`'s word decayed once for each later
step before the reward, and that word is above the tie window. The word bounds what the first
decision's own laying puts on a slot, so each slot's share of the own credit passes the test by
itself (argued: the bound on the laid increment is a step of
`AcornVerif.CurrentCreditHorizon.laid_lower`'s proof, and no theorem here states the own credit
as an executed word). The frame holds a slot
(`AcornVerif.CurrentConcealedTargetRung.rung_frame_slot`), and the statement of the frame is
`AcornVerif.CurrentConcealedTargetRungChoice.rung_start_value`: right after that step, the value
of the action taken at the visit's first decision, at the frame laid there, is above the tie
window.

`rung_first_credit` states it of every member the agent solves on one of its first 125 visits,
at the member's first such visit and the first step of it that meets the target.
`rung_found_credit` states it of the 102 members that
`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds` lists, each first solved within the first
72 visits.

The proof reads the member's reward words and applies
`AcornVerif.CurrentFirstCredit.loop_first_credit`. At the start of each visit the reward word is
the one the host world carries, the zero word in the rung's world (`start_reward`); after each
step it is the word one when the step met the target and the zero word when it did not
(`AcornVerif.CurrentConcealedTargetMission.reward_word_step`, `step_reward`). So the first reward
of one arrives with the percept after the first step that meets the target, at most seven
decisions after the visit's first (`rung_first_rewards`). Every frame of the run is within the
rung's bound (`rung_laid`, from `AcornVerif.CurrentConcealedTargetRung.rung_frame`), and 1000
decisions are within the declared tester's maturity threshold, so no slot is retired before the
reward.

The statements name a member's first success by one proposition, `FirstSuccess`: the agent meets
the member's target for the first time at a step of a visit. `rungVisits` and `rungOrigin` are
the member's visits and their start.

Two facts of the live states of a member's visits are stated for every configuration and every
action sequence: a live state's clock is past the member's own by at most the steps the visit
has taken (`visits_clock`), and every live state holds the member's goal (`visits_goal`). So
where a visit stays within the first eighth of the day, every percept of the visits carries the
word of day phase zero (`visits_day_word`). The rung's world starts at the day's first step and
its visits take seven, so every percept of the rung's run carries that word (`rung_day_word`).

What this does not say.

- That the weight is still there at the start of the next visit, except for a first success on
  the visit's seventh step: the memory the statement is of is then the one the next visit starts
  from. After an earlier step, the steps that remain in the visit form their errors from the
  weights this reward wrote and can lower it (argued). No question of rbeauchamp/acorn#232 asks
  this.
- That the greedy choice at the next visit's start is the action of this visit's first decision.
  The rows of later actions can hold more credit on the slots their frames share with the start
  frame, and the next start frame can differ from this one where the agent's own predictions are
  fed back (argued). Questions 3 and 4 of rbeauchamp/acorn#232 ask what the greedy choice then
  does.
- Anything of a first success after the first 1000 decisions, when a unit can be replaced and its
  slot retired, or of another profile, criterion or step order.
- The weight's value. The word is a lower bound, computed for frames of at most 1900 slots; no
  theorem says that a laying step writes as little.

Trust. The statements are about executed binary32 words. Lean's kernel, its model of binary32
arithmetic and the agreement of the native operations with that model on finite operands remain
trusted, as for every proof of executed words in this library.
-/

namespace AcornVerif.CurrentConcealedTargetRungCredit
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentConcealedTargetRungFinds AcornVerif.CurrentCreditHorizon
open AcornVerif.CurrentFirstCredit AcornVerif.CurrentFrameSize AcornVerif.CurrentFrameSlots

variable {config : Host.WorldConfig}

/-! ## The percepts in a member's visits -/

/-- At the start of each visit of a member, the percept is the one the member's world shows at
its start. -/
theorem start_percept (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (length : ℕ) (agent : Kernel.Agent Grid.interface) (count : ℕ) :
    Kernel.perceptAt (Kernel.visits (gridWorld config mode) (member live target) length) agent
      (Kernel.visitStart (gridWorld config mode) (member live target) length)
      (count * (length + 1)) = (gridWorld config mode).percept (member live target) := by
  unfold Kernel.perceptAt
  rw [Kernel.visits_period]
  rfl

/-- At the start of each visit of a member, the reward word is the one the host world carries. -/
theorem start_reward (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (length : ℕ) (agent : Kernel.Agent Grid.interface) (count : ℕ) :
    (Kernel.perceptAt (Kernel.visits (gridWorld config mode) (member live target) length) agent
      (Kernel.visitStart (gridWorld config mode) (member live target) length)
      (count * (length + 1))).reward = live.carried.reward :=
  congrArg (fun percept => percept.reward) (start_percept mode live target length agent count)

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
  have inner := Kernel.visits_state (gridWorld config mode) (member live target) length agent
    count (before + 1) high
  change ((gridWorld config mode).percept (Kernel.stateAt (Kernel.visits (gridWorld config mode)
    (member live target) length) agent
    (Kernel.visitStart (gridWorld config mode) (member live target) length)
    (count * (length + 1) + (before + 1))).1).reward = _
  rw [inner]
  exact reward_word_step mode _ _

/-! ## The live states of a member's visits -/

/-- **A visit's clock.** In the visits of a member, along every action sequence, the clock of a
live state is past the member's own by at most the number of steps the visit has taken. Each
visit starts from the member's world, and a successful step advances the clock by one. -/
theorem visits_clock (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (length : ℕ) (actions : ℕ → Kernel.Act Grid.interface) :
    ∀ (time : ℕ) (here : Live config),
      (Kernel.path (Kernel.visits (gridWorld config mode) (member live target) length)
        (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
        time).1 = some here →
      here.world.time.toNat ≤ live.world.time.toNat +
        (Kernel.path (Kernel.visits (gridWorld config mode) (member live target) length)
          (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
          time).2.val := by
  intro time
  induction time with
  | zero =>
    intro here reached
    have same : member live target = some here := reached
    obtain rfl := Option.some.inj same
    exact Nat.le_add_right _ _
  | succ time ih =>
    intro here reached
    by_cases within : (Kernel.path (Kernel.visits (gridWorld config mode) (member live target)
        length) (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
        time).2.val < length
    · have taken : Kernel.path (Kernel.visits (gridWorld config mode) (member live target)
          length) (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
          (time + 1) =
          ((gridWorld config mode).step (Kernel.path (Kernel.visits (gridWorld config mode)
            (member live target) length) (Kernel.visitStart (gridWorld config mode)
            (member live target) length) actions time).1 (actions time),
            ⟨(Kernel.path (Kernel.visits (gridWorld config mode) (member live target) length)
              (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
              time).2.val + 1, by omega⟩) := dite_eq_left within
      rw [taken] at reached ⊢
      cases before : (Kernel.path (Kernel.visits (gridWorld config mode) (member live target)
          length) (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
          time).1 with
      | none =>
        rw [before] at reached
        cases reached
      | some prior =>
        rw [before] at reached
        have moved : advance prior (actions time) = some here := reached
        obtain ⟨events, stepped, -⟩ := advance_some prior here (actions time) moved
        have tick := Host.World.step_clock prior.world here.world _ events stepped
        have earlier := ih prior before
        have wrap : (prior.world.time + 1).toNat ≤ prior.world.time.toNat + 1 := by
          rw [UInt64.toNat_add]
          exact Nat.mod_le _ _
        rw [tick]
        simp only
        omega
    · have reset : Kernel.path (Kernel.visits (gridWorld config mode) (member live target)
          length) (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
          (time + 1) = (member live target, ⟨0, Nat.succ_pos length⟩) := dite_eq_right within
      rw [reset] at reached ⊢
      have same : member live target = some here := reached
      obtain rfl := Option.some.inj same
      exact Nat.le_add_right _ _

/-- In the visits of a member, along every action sequence, every live state holds the member's
goal. -/
theorem visits_goal (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (length : ℕ) (actions : ℕ → Kernel.Act Grid.interface) :
    ∀ (time : ℕ) (here : Live config),
      (Kernel.path (Kernel.visits (gridWorld config mode) (member live target) length)
        (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
        time).1 = some here →
      here.world.goal = some (.find target) := by
  intro time
  induction time with
  | zero =>
    intro here reached
    have same : member live target = some here := reached
    obtain rfl := Option.some.inj same
    rfl
  | succ time ih =>
    intro here reached
    by_cases within : (Kernel.path (Kernel.visits (gridWorld config mode) (member live target)
        length) (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
        time).2.val < length
    · have taken : Kernel.path (Kernel.visits (gridWorld config mode) (member live target)
          length) (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
          (time + 1) =
          ((gridWorld config mode).step (Kernel.path (Kernel.visits (gridWorld config mode)
            (member live target) length) (Kernel.visitStart (gridWorld config mode)
            (member live target) length) actions time).1 (actions time),
            ⟨(Kernel.path (Kernel.visits (gridWorld config mode) (member live target) length)
              (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
              time).2.val + 1, by omega⟩) := dite_eq_left within
      rw [taken] at reached
      cases before : (Kernel.path (Kernel.visits (gridWorld config mode) (member live target)
          length) (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
          time).1 with
      | none =>
        rw [before] at reached
        cases reached
      | some prior =>
        rw [before] at reached
        have moved : advance prior (actions time) = some here := reached
        obtain ⟨events, stepped, -⟩ := advance_some prior here (actions time) moved
        exact (Host.World.step_goal _ _ _ _ stepped).1.trans (ih prior before)
    · have reset : Kernel.path (Kernel.visits (gridWorld config mode) (member live target)
          length) (Kernel.visitStart (gridWorld config mode) (member live target) length) actions
          (time + 1) = (member live target, ⟨0, Nat.succ_pos length⟩) := dite_eq_right within
      rw [reset] at reached
      have same : member live target = some here := reached
      obtain rfl := Option.some.inj same
      rfl

/-- **Every percept of a member's visits carries one day word.** Where the member's clock and a
visit's length together stay within the first eighth of the day, the percept at every time of the
member's visits, under every agent, carries the word of day phase zero: a live state's clock is
within that eighth (`visits_clock`), and the refused state shows the blank observation, whose
day is zero. -/
theorem visits_day_word (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (length : ℕ) (agent : Kernel.Agent Grid.interface)
    (early : live.world.time.toNat + length < config.raw.dayLength.toNat / 8) (time : ℕ) :
    (⟨0x41, 0⟩ : SensorWord) ∈ (Kernel.perceptAt (Kernel.visits (gridWorld config mode)
      (member live target) length) agent
      (Kernel.visitStart (gridWorld config mode) (member live target) length)
      time).frame.words := by
  unfold Kernel.perceptAt
  rw [Kernel.stateAt_eq_path]
  apply percept_day_word mode
  intro here reached
  have clock := visits_clock mode live target length _ time here reached
  have bound := (Kernel.path (Kernel.visits (gridWorld config mode) (member live target) length)
    (Kernel.visitStart (gridWorld config mode) (member live target) length)
    (Kernel.actionAt (Kernel.visits (gridWorld config mode) (member live target) length) agent
      (Kernel.visitStart (gridWorld config mode) (member live target) length)) time).2.isLt
  omega

/-! ## A member's visits and its first success -/

/-- The visits of a member of the rung's class: the member's world, run in visits of seven
steps. -/
abbrev rungVisits (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) : Kernel.World Grid.interface :=
  Kernel.visits (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
    (member witnessLive index.1.1) 7

/-- The state from which a member's visits start. -/
abbrev rungOrigin (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) : (rungVisits planning index).State :=
  Kernel.visitStart (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
    (member witnessLive index.1.1) 7

/-- **A member's first success.** In the visits of a member of the rung's class, an agent meets
the member's target for the first time at step `step` of visit `visit`: the step is one of the
visit's seven, the agent solves the member on no earlier visit, no earlier step of this visit
meets the target, and this step does. The time of that step's percept is `visit * 8 + step`. -/
def FirstSuccess (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (agent : Kernel.Agent Grid.interface) (visit step : ℕ) : Prop :=
  1 ≤ step ∧ step ≤ 7 ∧
    (∀ earlier, earlier < visit →
      ¬ Kernel.SolvesOnVisit
        (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
        (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
        agent earlier index) ∧
    (∀ sooner, 1 ≤ sooner → sooner < step →
      ¬ (completion witnessConfig (rungConstruction planning).profile.taskMode 7).satisfied
        (Kernel.stateAt (rungVisits planning index) agent (rungOrigin planning index)
          (visit * 8 + sooner)).1) ∧
    (completion witnessConfig (rungConstruction planning).profile.taskMode 7).satisfied
      (Kernel.stateAt (rungVisits planning index) agent (rungOrigin planning index)
        (visit * 8 + step)).1

/-- **A member that is solved has a first success.** A member of the rung's class that an agent
solves on a visit below a bound has a first success on a visit below that bound. -/
theorem rung_first_success (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (agent : Kernel.Agent Grid.interface) (bound : ℕ)
    (solved : ∃ visit, visit < bound ∧ Kernel.SolvesOnVisit
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
      (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
      agent visit index) :
    ∃ visit step, visit < bound ∧ FirstSuccess planning index agent visit step := by
  classical
  obtain ⟨some, before, once⟩ := solved
  have ever : ∃ visit, Kernel.SolvesOnVisit
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
      (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
      agent visit index := ⟨some, once⟩
  have least : Nat.find ever ≤ some := Nat.find_min' ever once
  have stepped : ∃ step, 1 ≤ step ∧ step ≤ 7 ∧
      (completion witnessConfig (rungConstruction planning).profile.taskMode 7).satisfied
        (Kernel.stateAt (rungVisits planning index) agent (rungOrigin planning index)
          (Nat.find ever * 8 + step)).1 := Nat.find_spec ever
  obtain ⟨low, high, met⟩ := Nat.find_spec stepped
  exact ⟨Nat.find ever, Nat.find stepped, by omega, low, high,
    fun earlier sooner => Nat.find_min ever sooner,
    fun sooner lowSooner early satisfied =>
      Nat.find_min stepped early ⟨lowSooner, by omega, satisfied⟩, met⟩

/-- **The reward words up to a member's first success.** At a member's first success by an
agent, every reward word the agent receives before the time of that step's percept is the zero
word, and that percept's is the word one. -/
theorem rung_first_rewards (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (agent : Kernel.Agent Grid.interface) (visit step : ℕ)
    (first : FirstSuccess planning index agent visit step) :
    (∀ time, time < visit * 8 + step →
        (Kernel.perceptAt (rungVisits planning index) agent (rungOrigin planning index)
          time).reward = Binary32.zero) ∧
      (Kernel.perceptAt (rungVisits planning index) agent (rungOrigin planning index)
        (visit * 8 + step)).reward = Binary32.one := by
  obtain ⟨low, high, unsolved, unmet, met⟩ := first
  constructor
  · intro time before
    obtain ⟨count, rest, rfl, small⟩ : ∃ count rest, time = count * (7 + 1) + rest ∧ rest < 8 :=
      ⟨time / 8, time % 8, by omega, Nat.mod_lt _ (by decide)⟩
    cases rest with
    | zero =>
      exact start_reward (rungConstruction planning).profile.taskMode witnessLive index.1.1 7
        agent count
    | succ rest =>
      have notMet :
          ¬ (completion witnessConfig (rungConstruction planning).profile.taskMode 7).satisfied
            (Kernel.stateAt (rungVisits planning index) agent (rungOrigin planning index)
              (count * (7 + 1) + (rest + 1))).1 := by
        by_cases earlierVisit : count < visit
        · intro satisfied
          exact unsolved count earlierVisit ⟨rest + 1, by omega, by omega, satisfied⟩
        · have same : count = visit := by omega
          subst same
          exact unmet (rest + 1) (by omega) (by omega)
      have unpaid : goalMet (Kernel.stateAt (rungVisits planning index) agent
          (rungOrigin planning index) (count * (7 + 1) + (rest + 1))).1 = false :=
        Bool.eq_false_iff.mpr (fun shown => notMet ((goalMet_iff _ 7 _).mp shown))
      rw [step_reward (rungConstruction planning).profile.taskMode witnessLive index.1.1 7 agent
        count (rest + 1) (by omega) (by omega), unpaid]
      rfl
  · have paid : goalMet (Kernel.stateAt (rungVisits planning index) agent
        (rungOrigin planning index) (visit * (7 + 1) + step)).1 = true :=
      (goalMet_iff _ 7 _).mpr met
    change (Kernel.perceptAt (rungVisits planning index) agent (rungOrigin planning index)
      (visit * (7 + 1) + step)).reward = _
    rw [step_reward (rungConstruction planning).profile.taskMode witnessLive index.1.1 7 agent
      visit step low high, paid]
    rfl

/-- Every step of the rung's agent in a member's visits lays a frame of at most 1712 slots. -/
theorem rung_laid (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (time : ℕ) :
    (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
      (rungOrigin planning index) time).features.indices.length ≤ 1712 :=
  rung_frame planning (rungConstruction planning).profile.taskMode .learnThenAct
    (Kernel.memoryAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      time)
    (Kernel.stateAt (rungVisits planning index) (rungAgent planning) (rungOrigin planning index)
      time).1

/-- Every percept of the rung's visits carries the word of day phase zero: the rung's world
starts at the day's first step, and a visit's seven steps stay within its first eighth, 256
steps. -/
theorem rung_day_word (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (time : ℕ) :
    (⟨0x41, 0⟩ : SensorWord) ∈ (Kernel.perceptAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) time).frame.words :=
  visits_day_word (rungConstruction planning).profile.taskMode witnessLive index.1.1 7
    (rungAgent planning) (by decide) time

/-! ## The first reward of a member reaches its visit's start -/

/-- **Credit is written at the start.** At a member's first success by the rung's agent, at step
`step` of visit `visit` and within the agent's first 1000 decisions: right after the agent's step
on the percept that carries that reward, every slot of the frame it laid at the visit's first
decision holds, in the row of the action it took there, a weight that reads at least a word that
bounds from below the trace a step lays, decayed once for each later step of the visit before the
reward (`AcornVerif.CurrentCreditHorizon.lowChain`); and that word is above the tie window of the
greedy choice. -/
theorem rung_credit (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (visit step : ℕ) (first : FirstSuccess planning index (rungAgent planning) visit step)
    (early : visit * 8 + step < 1000) :
    numerical32 tieWindow < numerical32 (lowChain .discounted (step - 1)) ∧
      ∀ slot ∈ (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
          (rungOrigin planning index) (visit * 8)).features.indices,
        numerical32 (lowChain .discounted (step - 1)) ≤
          numerical32 (((controlOf (Kernel.memoryAt (rungVisits planning index)
            (rungAgent planning) (rungOrigin planning index)
            (visit * 8 + step + 1))).learners.get
            (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
              (rungOrigin planning index) (visit * 8)).row).state.weights.get slot).value := by
  obtain ⟨quietBefore, paysAt⟩ := rung_first_rewards planning index (rungAgent planning) visit
    step first
  obtain ⟨low, high, -⟩ := first
  obtain ⟨gap, rfl⟩ : ∃ gap, step = gap + 1 := ⟨step - 1, by omega⟩
  have credited := loop_first_credit (interface := Grid.interface)
    (profile := (rungConstruction planning).profile)
    (config := (rungConstruction planning).config)
    (dimension := (rungConstruction planning).dimension) rfl rfl planning
    (rungVisits planning index) (rungOrigin planning index)
    (visit * 8) gap (by omega) (by change visit * 8 + gap + 2 ≤ 1000; omega)
    (fun time bound => quietBefore time (by omega))
    (by rw [show visit * 8 + 1 + gap = visit * 8 + (gap + 1) by omega]; exact paysAt)
    (fun time _ => Nat.le_trans (rung_laid planning index time) (by decide))
    (Nat.le_trans (rung_laid planning index (visit * 8)) (by decide))
  have time : visit * 8 + 1 + gap + 1 = visit * 8 + (gap + 1) + 1 := by omega
  rw [time] at credited
  exact ⟨lowChain_above_tie .discounted gap (by omega), credited⟩

/-- **At a member's first success, credit is written at the start of that visit.** Every member
of the rung's class that the rung's agent solves on one of its first 125 visits has a first
success on one of them; and right after the agent's step on the percept that carries that
reward, every slot of the frame laid at that visit's first decision holds, in the row of the
action taken there, a weight above the tie window of the greedy choice. -/
theorem rung_first_credit (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index)
    (bound : ℕ) (within : bound ≤ 125)
    (solved : ∃ visit, visit < bound ∧ Kernel.SolvesOnVisit
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
      (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
      (rungAgent planning) visit index) :
    ∃ visit step, visit < bound ∧ FirstSuccess planning index (rungAgent planning) visit step ∧
      ∀ slot ∈ (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
          (rungOrigin planning index) (visit * 8)).features.indices,
        numerical32 tieWindow <
          numerical32 (((controlOf (Kernel.memoryAt (rungVisits planning index)
            (rungAgent planning) (rungOrigin planning index)
            (visit * 8 + step + 1))).learners.get
            (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
              (rungOrigin planning index) (visit * 8)).row).state.weights.get slot).value := by
  obtain ⟨visit, step, before, first⟩ :=
    rung_first_success planning index (rungAgent planning) bound solved
  have credit := rung_credit planning index visit step first (by
    obtain ⟨-, high, -⟩ := first
    omega)
  exact ⟨visit, step, before, first,
    fun slot held => lt_of_lt_of_le credit.1 (credit.2 slot held)⟩

/-- **Each member the rung's agent is proved to find has its first reward's credit written at the
start of that visit.** There are 102 distinct members of the rung's class, those of
`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds`, each of which the agent first solves on
one of its first 72 visits, and for each of which the conclusion of `rung_first_credit` holds at
that first success. -/
theorem rung_found_credit (planning : PlanningSelection) :
    ∃ counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index,
      counted.Nodup ∧ counted.length = 102 ∧ ∀ index ∈ counted,
        ∃ visit step, visit < 72 ∧
          FirstSuccess planning index (rungAgent planning) visit step ∧
          ∀ slot ∈ (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
              (rungOrigin planning index) (visit * 8)).features.indices,
            numerical32 tieWindow <
              numerical32 (((controlOf (Kernel.memoryAt (rungVisits planning index)
                (rungAgent planning) (rungOrigin planning index)
                (visit * 8 + step + 1))).learners.get
                (laidAt (rungConstruction planning).initial.agent (rungVisits planning index)
                  (rungOrigin planning index) (visit * 8)).row).state.weights.get
                slot).value := by
  obtain ⟨counted, distinct, size, solved, -⟩ := rung_finds planning
  exact ⟨counted, distinct, size, fun index member =>
    rung_first_credit planning index 72 (by decide) (solved index member)⟩

end AcornVerif.CurrentConcealedTargetRungCredit
