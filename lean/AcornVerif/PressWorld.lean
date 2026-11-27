import AcornVerif.Capacity
import AcornVerif.MuteDoors
import Mathlib.Data.Fintype.Pigeonhole

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

abbrev pressWorld (interface : Interface) (shown : Percept interface) (wait : ℕ) :
    World interface where
  State := ℕ × Bool × Bool
  step := fun state action =>
    (state.1 + 1,
      state.2.1 || (decide (state.1 < wait) && decide (action.val = 1)),
      state.2.2 || (decide (state.1 = wait) && decide (action.val = 1) && !state.2.1))
  percept := fun _ => shown

def pressGoal (shown : Percept interface) (wait : ℕ) :
    AttemptGoal (pressWorld interface shown wait) :=
  ⟨fun (state : ℕ × Bool × Bool) => state.2.2 = true, wait + 1⟩

def pressStart : ℕ × Bool × Bool := (0, false, false)

theorem press_path (shown : Percept interface) (wait : ℕ) (actions : ℕ → Act interface)
    (time : ℕ) :
    (path (pressWorld interface shown wait) pressStart actions time).1 = time ∧
    ((path (pressWorld interface shown wait) pressStart actions time).2.1 = false →
      ∀ earlier, earlier < time → earlier < wait → (actions earlier).val ≠ 1) ∧
    ((path (pressWorld interface shown wait) pressStart actions time).2.2 = true →
      (actions wait).val = 1 ∧ ∀ earlier, earlier < wait → (actions earlier).val ≠ 1) := by
  induction time with
  | zero =>
    exact ⟨rfl, fun _ earlier before => absurd before (Nat.not_lt_zero _),
      fun done => absurd done Bool.false_ne_true⟩
  | succ time ih =>
    obtain ⟨clock, clean, done⟩ := ih
    refine ⟨congrArg Nat.succ clock, ?_, ?_⟩
    · intro spoiled earlier before small
      have split : ((path (pressWorld interface shown wait) pressStart actions time).2.1 ||
          (decide ((path (pressWorld interface shown wait) pressStart actions time).1 < wait) &&
            decide ((actions time).val = 1))) = false := spoiled
      obtain ⟨still, fresh⟩ := Bool.or_eq_false_iff.mp split
      rcases Nat.lt_succ_iff_lt_or_eq.mp before with older | same
      · exact clean still earlier older small
      · subst same
        intro press
        rw [clock, decide_eq_true small, decide_eq_true press] at fresh
        exact absurd fresh (by decide)
    · intro pressed
      have split : ((path (pressWorld interface shown wait) pressStart actions time).2.2 ||
          (decide ((path (pressWorld interface shown wait) pressStart actions time).1 = wait) &&
            decide ((actions time).val = 1) &&
            !(path (pressWorld interface shown wait) pressStart actions time).2.1)) = true :=
        pressed
      rcases Bool.or_eq_true_iff.mp split with old | fresh
      · exact done old
      · obtain ⟨both, unspoiled⟩ := Bool.and_eq_true_iff.mp fresh
        obtain ⟨due, press⟩ := Bool.and_eq_true_iff.mp both
        have here : time = wait := clock.symm.trans (of_decide_eq_true due)
        have still : (path (pressWorld interface shown wait) pressStart actions time).2.1 =
            false := by
          cases value : (path (pressWorld interface shown wait) pressStart actions time).2.1 with
          | false => rfl
          | true =>
            rw [value] at unspoiled
            exact absurd unspoiled (by decide)
        exact ⟨here ▸ of_decide_eq_true press, fun earlier before =>
          clean still earlier (here ▸ before) before⟩

theorem driven_shift (agent : Agent interface) (shown : Percept interface) {first second : ℕ}
    (equal : driven agent (fun _ => shown) first = driven agent (fun _ => shown) second)
    (more : ℕ) :
    driven agent (fun _ => shown) (first + more) =
      driven agent (fun _ => shown) (second + more) := by
  induction more with
  | zero => exact equal
  | succ more ih => exact congrArg (fun memory => (agent.act memory shown).2) ih

theorem press_beyond (shown : Percept interface) (bits : ℕ) (agent : Agent interface)
    (fits : MemoryWithin agent bits) :
    ¬ Achieves agent (pressGoal (interface := interface) shown (2 ^ bits)) pressStart := by
  rintro ⟨time, -, -, met⟩
  rw [stateAt_eq_path] at met
  obtain ⟨-, -, done⟩ := press_path shown (2 ^ bits)
    (actionAt (pressWorld interface shown (2 ^ bits)) agent pressStart) time
  obtain ⟨press, waits⟩ := done met
  have acts : ∀ moment, actionAt (pressWorld interface shown (2 ^ bits)) agent pressStart moment =
      (agent.act (driven agent (fun _ => shown) moment) shown).1 :=
    fun moment => actionAt_response (pressWorld interface shown (2 ^ bits)) agent pressStart moment
  rw [acts] at press
  have clash : ∀ first second, first < second → second ≤ 2 ^ bits →
      driven agent (fun _ => shown) first ≠ driven agent (fun _ => shown) second := by
    intro first second before within equal
    have shifted := driven_shift agent shown equal (2 ^ bits - second)
    rw [Nat.add_sub_cancel' within] at shifted
    have early := waits (first + (2 ^ bits - second)) (by omega)
    rw [acts, shifted] at early
    exact early press
  obtain ⟨embed⟩ := fits
  obtain ⟨first, second, differ, same⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun moment : Fin (2 ^ bits + 1) => embed (driven agent (fun _ => shown) moment.val))
    (by simp)
  have equal := embed.injective same
  rcases Nat.lt_or_gt_of_ne (fun values => differ (Fin.ext values)) with before | after
  · exact clash first.val second.val before (Nat.le_of_lt_succ second.isLt) equal
  · exact clash second.val first.val after (Nat.le_of_lt_succ first.isLt) equal.symm

def pressPlan (two : 2 ≤ interface.actions.word.toNat) (wait : ℕ) : ℕ → Act interface :=
  fun time => if time = wait then pick two true else pick two false

theorem pressPlan_path (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface)
    (wait time : ℕ) (within : time ≤ wait) :
    path (pressWorld interface shown wait) pressStart (pressPlan two wait) time =
      (time, false, false) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have early : time ≠ wait := by omega
    change (pressWorld interface shown wait).step
      (path (pressWorld interface shown wait) pressStart (pressPlan two wait) time)
      (pressPlan two wait time) = _
    rw [ih (Nat.le_of_succ_le within)]
    simp [pressWorld, pressPlan, early, pick]

theorem pressPlan_met (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface)
    (wait : ℕ) : (pressGoal shown wait).MetBy pressStart (pressPlan two wait) := by
  refine ⟨wait + 1, Nat.succ_le_succ (Nat.zero_le wait), Nat.le_refl _, ?_⟩
  change ((pressWorld interface shown wait).step
    (path (pressWorld interface shown wait) pressStart (pressPlan two wait) wait)
    (pressPlan two wait wait)).2.2 = true
  rw [pressPlan_path two shown wait wait (Nat.le_refl wait)]
  simp [pressPlan, pick]

theorem press_dependent (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface)
    (bits : ℕ) (positive : 1 ≤ bits) :
    CapacityDependent (fun width => ∀ agent : Agent interface, MemoryWithin agent width →
      ¬ Achieves agent (pressGoal (interface := interface) shown (2 ^ bits)) pressStart)
        bits (bits + 1) ∧
    ∃ agent : Agent interface, OpenLoop agent ∧ MemoryWithin agent (bits + 1) ∧
      Achieves agent (pressGoal (interface := interface) shown (2 ^ bits)) pressStart := by
  have small : 2 ^ 1 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) positive
  have double : 2 ^ (bits + 1) = 2 ^ bits * 2 := Nat.pow_succ 2 bits
  have fits : MemoryWithin (script interface (2 ^ bits + 1) (pressPlan two (2 ^ bits)))
      (bits + 1) := script_memoryWithin (2 ^ bits + 1) (bits + 1) _ (by omega)
  have achieves : Achieves (script interface (2 ^ bits + 1) (pressPlan two (2 ^ bits)))
      (pressGoal (interface := interface) shown (2 ^ bits)) pressStart :=
    script_achieves (Nat.le_refl _) (pressPlan_met two shown (2 ^ bits))
  exact ⟨⟨Nat.le_succ bits, fun agent narrow => press_beyond shown bits agent narrow,
    fun none => none _ fits achieves⟩, _, script_openLoop _ _, fits, achieves⟩

end AcornVerif.Kernel
