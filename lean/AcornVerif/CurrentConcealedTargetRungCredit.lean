import AcornVerif.CurrentConcealedTargetRungFinds
import AcornVerif.CurrentFirstCredit

namespace AcornVerif.CurrentConcealedTargetRungCredit
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentConcealedTargetRungFinds AcornVerif.CurrentCreditHorizon
open AcornVerif.CurrentFirstCredit AcornVerif.CurrentFrameSize AcornVerif.CurrentFrameSlots

variable {config : Host.WorldConfig}

theorem start_percept (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (length : ℕ) (agent : Kernel.Agent Grid.interface) (count : ℕ) :
    Kernel.perceptAt (Kernel.visits (gridWorld config mode) (member live target) length) agent
      (Kernel.visitStart (gridWorld config mode) (member live target) length)
      (count * (length + 1)) = (gridWorld config mode).percept (member live target) := by
  unfold Kernel.perceptAt
  rw [Kernel.visits_period]
  rfl

theorem start_reward (mode : TaskFeatureMode) (live : Live config) (target : Host.Position)
    (length : ℕ) (agent : Kernel.Agent Grid.interface) (count : ℕ) :
    (Kernel.perceptAt (Kernel.visits (gridWorld config mode) (member live target) length) agent
      (Kernel.visitStart (gridWorld config mode) (member live target) length)
      (count * (length + 1))).reward = live.carried.reward :=
  congrArg (fun percept => percept.reward) (start_percept mode live target length agent count)

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

abbrev rungVisits (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) : Kernel.World Grid.interface :=
  Kernel.visits (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
    (member witnessLive index.1.1) 7

abbrev rungOrigin (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) : (rungVisits planning index).State :=
  Kernel.visitStart (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
    (member witnessLive index.1.1) 7

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

theorem rung_day_word (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (time : ℕ) :
    (⟨0x41, 0⟩ : SensorWord) ∈ (Kernel.perceptAt (rungVisits planning index) (rungAgent planning)
      (rungOrigin planning index) time).frame.words :=
  visits_day_word (rungConstruction planning).profile.taskMode witnessLive index.1.1 7
    (rungAgent planning) (by decide) time

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
