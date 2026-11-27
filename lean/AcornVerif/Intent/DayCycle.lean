import AcornVerif.LeanIntentBridge

namespace AcornVerif.Intent.DayCycle

open LeanIntent

structure DayWorld (Ctx Act Obs E : Type) where
  length : Nat
  night : Nat → Bool
  cost : Nat → Ctx → Act → E
  sees : Nat → Ctx → Obs

abbrev NightHalf (length start t : Nat) : Prop := (t + start) % length < length / 2

def quarter (length start t : Nat) : Nat := (t + start) % length * 4 / length

def halves (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"each day has a daytime half and a night half of equal length", fun w =>
    0 < w.length ∧ w.length % 2 = 0 ∧
      ∃ start, ∀ t, w.night t = true ↔ NightHalf w.length start t⟩

def nightCostsMore (Ctx Act Obs E : Type) [LT E] : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"at night every action costs more energy", fun w =>
    ∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c a⟩

def tellsDayFromNight (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"the agent can always tell day from night", fun w =>
    ∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t'⟩

def seesQuarter (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"the agent can always see where in the day it is, at least to a quarter of the day", fun w =>
    ∃ start, ∀ t t' c c', w.sees t c = w.sees t' c' →
      quarter w.length start t = quarter w.length start t'⟩

def dayCycleFor (Ctx Act Obs E : Type) [LT E] : IntentRecord (DayWorld Ctx Act Obs E) where
  shape := .value _
  dom := []
  props := [halves Ctx Act Obs E, nightCostsMore Ctx Act Obs E, tellsDayFromNight Ctx Act Obs E,
    seesQuarter Ctx Act Obs E]
  vocab := [⟨"night half", Nat × Nat × Nat, fun p => NightHalf p.1 p.2.1 p.2.2⟩,
    ⟨"costs less", E × E, fun p => p.1 < p.2⟩,
    ⟨"in quarter", Nat × Nat × Nat × Nat, fun p => quarter p.1 p.2.1 p.2.2.1 = p.2.2.2⟩]

variable {Ctx Act Obs E : Type} [LT E]

theorem dayCycle_meets {w : DayWorld Ctx Act Obs E} :
    (dayCycleFor Ctx Act Obs E).Meets w ↔
      (0 < w.length ∧ w.length % 2 = 0 ∧
        ∃ start, ∀ t, w.night t = true ↔ NightHalf w.length start t) ∧
      (∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c a) ∧
      (∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t') ∧
      (∃ start, ∀ t t' c c', w.sees t c = w.sees t' c' →
        quarter w.length start t = quarter w.length start t') := by
  constructor
  · intro h
    exact ⟨h.2 _ (List.mem_cons_self ..),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))⟩
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [dayCycleFor, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4

theorem quarter_lt {length : Nat} (hpos : 0 < length) (start t : Nat) :
    quarter length start t < 4 := by
  unfold quarter
  rw [Nat.div_lt_iff_lt_mul hpos]
  have := Nat.mod_lt (t + start) hpos
  omega

theorem nightHalf_iff_quarter {length : Nat} (hpos : 0 < length) (heven : length % 2 = 0)
    (start t : Nat) : NightHalf length start t ↔ quarter length start t < 2 := by
  unfold NightHalf quarter
  rw [Nat.div_lt_iff_lt_mul hpos]
  omega

def quarterIndex (length start t : Nat) : Fin 4 := ⟨min (quarter length start t) 3, by omega⟩

def clockWorld (length start : Nat) (lo hi : E) (sight : Fin 4 → Obs) : DayWorld Ctx Act Obs E where
  length := length
  night t := decide (NightHalf length start t)
  cost t _ _ := if NightHalf length start t then hi else lo
  sees t _ := sight (quarterIndex length start t)

theorem clockWorld_meets {length start : Nat} {lo hi : E} {sight : Fin 4 → Obs}
    (hpos : 0 < length) (heven : length % 2 = 0) (hlt : lo < hi)
    (hsight : ∀ i j, sight i = sight j → i = j) :
    (dayCycleFor Ctx Act Obs E).Meets (clockWorld length start lo hi sight) := by
  have hq : ∀ t t', sight (quarterIndex length start t) = sight (quarterIndex length start t') →
      quarter length start t = quarter length start t' := by
    intro t t' h
    have h0 := congrArg Fin.val (hsight _ _ h)
    simp only [quarterIndex] at h0
    have h1 := quarter_lt hpos start t
    have h2 := quarter_lt hpos start t'
    omega
  refine dayCycle_meets.mpr ⟨⟨hpos, heven, start, fun t => decide_eq_true_iff⟩,
    fun c a t t' ht ht' => ?_, fun t t' c c' h => ?_, start, fun t t' c c' h => hq t t' h⟩
  · have hn : NightHalf length start t :=
      of_decide_eq_true (show decide (NightHalf length start t) = true from ht)
    have hd : ¬ NightHalf length start t' :=
      of_decide_eq_false (show decide (NightHalf length start t') = false from ht')
    show (if NightHalf length start t' then hi else lo) <
      (if NightHalf length start t then hi else lo)
    rw [ite_eq_right hd, ite_eq_left hn]
    exact hlt
  · show decide (NightHalf length start t) = decide (NightHalf length start t')
    rw [decide_eq_decide, nightHalf_iff_quarter hpos heven, nightHalf_iff_quarter hpos heven,
      hq t t' h]

def dayOrNightOnly (lo hi : E) (o₁ o₂ : Obs) : DayWorld Ctx Act Obs E :=
  { clockWorld (Ctx := Ctx) (Act := Act) 4 0 lo hi (fun _ => o₁) with
    sees := fun t _ => if NightHalf 4 0 t then o₁ else o₂ }

theorem dayCycle_refutes_dayOrNightOnly (c : Ctx) (lo hi : E) (o₁ o₂ : Obs) :
    ¬ (dayCycleFor Ctx Act Obs E).Meets (dayOrNightOnly lo hi o₁ o₂) := by
  intro h
  obtain ⟨-, -, -, s, hs⟩ := dayCycle_meets.mp h
  have n0 : NightHalf 4 0 0 := by decide
  have n1 : NightHalf 4 0 1 := by decide
  have same : (dayOrNightOnly (Ctx := Ctx) (Act := Act) lo hi o₁ o₂).sees 0 c =
      (dayOrNightOnly (Ctx := Ctx) (Act := Act) lo hi o₁ o₂).sees 1 c := by
    show (if NightHalf 4 0 0 then o₁ else o₂) = (if NightHalf 4 0 1 then o₁ else o₂)
    rw [ite_eq_left n0, ite_eq_left n1]
  have := hs 0 1 c c same
  simp only [dayOrNightOnly, clockWorld, quarter] at this
  omega

theorem dayCycle_o2 {lo hi : E} (hlt : lo < hi) (sight : Fin 4 → Obs) :
    O2 (dayCycleFor Ctx Act Obs E) := by
  refine (o2_correct _).mpr ⟨⟨clockWorld 2 0 lo hi sight, fun _ h => nomatch h⟩, ?_⟩
  intro p hp
  simp only [dayCycleFor, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨(2, 0, 0), show (0 + 0) % 2 < 2 / 2 by decide⟩
  · exact ⟨(lo, hi), hlt⟩
  · exact ⟨(4, 0, 0, 0), show quarter 4 0 0 = 0 by decide⟩

theorem dayCycle_o2Run {lo hi : E} (hlt : lo < hi) {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) : O2Run (dayCycleFor Ctx Act Obs E) :=
  o2Run_of_meets (clockWorld_meets (length := 2) (start := 0) (by decide) (by decide) hlt hsight)

theorem dayCycle_o3 (c : Ctx) (a : Act) {lo hi : E} (hirr : ¬ lo < lo) (sight : Fin 4 → Obs) :
    O3 (dayCycleFor Ctx Act Obs E) := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [dayCycleFor, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨{ clockWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi sight with length := 0 },
      fun h => Nat.lt_irrefl 0 h.1⟩
  · exact ⟨{ clockWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi sight with
      cost := fun _ _ _ => lo }, fun h => hirr (h c a 0 1 rfl rfl)⟩
  · exact ⟨{ clockWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi sight with
      sees := fun _ _ => sight 0 }, fun h => Bool.noConfusion (h 0 1 c c rfl)⟩
  · refine ⟨{ clockWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi sight with
      sees := fun _ _ => sight 0 }, fun ⟨s, hs⟩ => ?_⟩
    have := hs 0 1 c c rfl
    change (0 + s) % 2 * 4 / 2 = (1 + s) % 2 * 4 / 2 at this
    omega

theorem dayCycle_o4 : O4 (dayCycleFor Ctx Act Obs E) := (o4_correct _).mpr trivial

theorem dayCycle_not_o5_eq {lo hi : E} (hlt : lo < hi) {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) : ¬ O5 (dayCycleFor Ctx Act Obs E) .eq :=
  not_o5_eq (clockWorld_meets (length := 2) (start := 0) (by decide) (by decide) hlt hsight)
    (clockWorld_meets (length := 4) (start := 0) (by decide) (by decide) hlt hsight)
    (fun h => absurd (congrArg DayWorld.length h) (show (2 : Nat) ≠ 4 by decide))

theorem dayCycle_o5_widest : O5 (dayCycleFor Ctx Act Obs E) .widest := o5_widest _

end AcornVerif.Intent.DayCycle
