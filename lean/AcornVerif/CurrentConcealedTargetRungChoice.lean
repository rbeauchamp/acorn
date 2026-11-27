import AcornVerif.CurrentConcealedTargetRungCredit
import AcornVerif.CurrentTraceCounts

namespace AcornVerif.CurrentConcealedTargetRungChoice
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentConcealedTargetRungFinds AcornVerif.CurrentConcealedTargetRungCredit
open AcornVerif.CurrentCreditHorizon AcornVerif.CurrentExplorer AcornVerif.CurrentFirstChoice
open AcornVerif.CurrentFirstCredit AcornVerif.CurrentFrameSlots AcornVerif.CurrentPreReward
open AcornVerif.CurrentTraceCounts

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

theorem rung_codes : ((List.range 14).all fun block => (List.range 9).all fun code =>
    ((rungRows.flatten.drop (39 + 40 * block - 80)).take (min (39 + 40 * block) 80)).elem
      code) = true := by
  decide +kernel

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

theorem rung_step_state (planning : PlanningSelection)
    (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
      7).Index) (agent : Kernel.Agent Grid.interface) (time : ℕ) (within : time < 7) :
    (Kernel.stateAt (rungVisits planning index) agent (rungOrigin planning index) (time + 1)).1 =
      (gridWorld witnessConfig (rungConstruction planning).profile.taskMode).step
        (Kernel.stateAt (rungVisits planning index) agent (rungOrigin planning index) time).1
        (Kernel.actionAt (rungVisits planning index) agent (rungOrigin planning index) time) :=
  Kernel.visits_step (gridWorld witnessConfig (rungConstruction planning).profile.taskMode)
    (member witnessLive index.1.1) 7 agent time within

theorem rung_still_codes : ∀ time, time < 7 → time ≠ 1 → time ≠ 2 →
    (Host.Action.fromIndex (rungRows.flatten.getD time 0)).direction = none := by
  decide +kernel

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

theorem rung_calm (time : ℕ) (low : 3 ≤ time) (high : time ≤ 4) :
    (rungExplorer.after time).run.bind ExploratoryRun.serve = none ∧
      (beginExploration Grid.interface.actions declaredRate (rungExplorer.after time).rng).1 =
        none := by
  obtain rfl | rfl : time = 3 ∨ time = 4 := by omega
  all_goals decide +kernel

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
