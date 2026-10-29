/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.LeanIntentBridge

/-!
# Intent record: the world's day and night

The owner holds intent for Acorn at the level of what a world should be like, not per function.
Asked what the world's day phase is for, the owner did not know which purpose the agent that
wrote it had in mind, and adopted, on 2026-10-29, a world-level statement proposed by the
assistant supervising this work after it had read the function: each day has a daytime half and
a night half of equal length; at night every action costs more energy; the agent can always see
where in the day it is. That statement is this record's only source. The record's first revision
was written before the source of `Acorn.Host.World.dayPhase`, the energy cost or the agent's
observation was read, and it names none of them.

The subject, `DayWorld`, is the day as the statement speaks of it: how many ticks a day lasts,
which ticks are night, the energy each action costs at each tick in each situation, and what the
agent sees at each tick in each situation. It is generic in the world's situations, actions,
sights and energy amounts, so that the record says nothing about how a world represents them;
`AcornVerif.Intent.DayCycleWorld` links it to Acorn's world.

Each property is one clause of the statement:

* `halves`: a day is a fixed, even number of ticks; the night is one unbroken stretch of half of
  them and the daytime the other half; every day is alike.
* `nightCostsMore`: every action, in every situation, costs strictly more energy at every night
  tick than at every daytime tick.
* `tellsDayFromNight` and `seesQuarter`: what the agent sees always tells it whether it is day or
  night, and which quarter of the day it is in.

The details below the statement are design decisions made on the owner's behalf, under the
owner's decision of 2026-10-29 that an owner works at the level of intent; each is recorded with
its reason in `AcornVerif.Intent.Decisions`. In this revision "where in the day" is read as at
least the quarter of the day: more than day or night, which the words ask for, and coarser than
the exact tick, which a second, blind reading of the words chose and the words do not require.

The statement leaves open how long a day is, where the first day starts, how much more the night
costs, whether that extra changes during the night, and how much more finely than a quarter the
agent sees the time of day; those stay free here (`dayCycle_not_o5_eq`).
-/

namespace AcornVerif.Intent.DayCycle

open LeanIntent

/-- A world's day and night, over its situations `Ctx`, actions `Act`, what the agent sees `Obs`
and energy amounts `E`. Time is counted in ticks from the start of a run. -/
structure DayWorld (Ctx Act Obs E : Type) where
  /-- The number of ticks in one day. -/
  length : Nat
  /-- Whether tick `t` falls in the night. -/
  night : Nat → Bool
  /-- The energy that action `a` costs at tick `t` in situation `c`. -/
  cost : Nat → Ctx → Act → E
  /-- What the agent sees at tick `t` in situation `c`. -/
  sees : Nat → Ctx → Obs

/-- Tick `t` lies in the night half of a day of `length` ticks whose night begins `start` ticks
before tick 0, counted around the day: the first `length / 2` ticks of each day so placed. -/
abbrev NightHalf (length start t : Nat) : Prop := (t + start) % length < length / 2

/-- The quarter, from 0 to 3, of a day of `length` ticks that tick `t` lies in, counted around the
day from `start` ticks before tick 0. -/
def quarter (length start t : Nat) : Nat := (t + start) % length * 4 / length

/-- A day is a fixed number of ticks, even and positive, whose night is one unbroken stretch of
half of them, placed alike in every day. -/
def halves (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"each day has a daytime half and a night half of equal length", fun w =>
    0 < w.length ∧ w.length % 2 = 0 ∧
      ∃ start, ∀ t, w.night t = true ↔ NightHalf w.length start t⟩

/-- Every action, in every situation, costs more energy at any night tick than at any daytime
tick. -/
def nightCostsMore (Ctx Act Obs E : Type) [LT E] : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"at night every action costs more energy", fun w =>
    ∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c a⟩

/-- What the agent sees always tells it whether it is day or night: two moments it sees alike
are both night or both day. -/
def tellsDayFromNight (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"the agent can always tell day from night", fun w =>
    ∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t'⟩

/-- What the agent sees always tells it which quarter of the day it is in: for some placing of
the quarters, two moments it sees alike lie in the same quarter. -/
def seesQuarter (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"the agent can always see where in the day it is, at least to a quarter of the day", fun w =>
    ∃ start, ∀ t t' c c', w.sees t c = w.sees t' c' →
      quarter w.length start t = quarter w.length start t'⟩

/-- The intent record of the world's day and night. -/
def dayCycle (Ctx Act Obs E : Type) [LT E] : IntentRecord (DayWorld Ctx Act Obs E) where
  shape := .value _
  dom := []
  props := [halves Ctx Act Obs E, nightCostsMore Ctx Act Obs E, tellsDayFromNight Ctx Act Obs E,
    seesQuarter Ctx Act Obs E]
  vocab := [⟨"night half", Nat × Nat × Nat, fun p => NightHalf p.1 p.2.1 p.2.2⟩,
    ⟨"costs less", E × E, fun p => p.1 < p.2⟩,
    ⟨"in quarter", Nat × Nat × Nat × Nat, fun p => quarter p.1 p.2.1 p.2.2.1 = p.2.2.2⟩]

variable {Ctx Act Obs E : Type} [LT E]

/-- A world meets the record exactly when its day has two equal halves, every action costs more
by night, and its sights tell day from night and the quarter of the day. -/
theorem dayCycle_meets {w : DayWorld Ctx Act Obs E} :
    (dayCycle Ctx Act Obs E).Meets w ↔
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
    simp only [dayCycle, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4

/-- A quarter lies below 4 in a day of positive length. -/
theorem quarter_lt {length : Nat} (hpos : 0 < length) (start t : Nat) :
    quarter length start t < 4 := by
  unfold quarter
  rw [Nat.div_lt_iff_lt_mul hpos]
  have := Nat.mod_lt (t + start) hpos
  omega

/-- In a day of even length, a tick is in the night half exactly when it lies in the first two
quarters. -/
theorem nightHalf_iff_quarter {length : Nat} (hpos : 0 < length) (heven : length % 2 = 0)
    (start t : Nat) : NightHalf length start t ↔ quarter length start t < 2 := by
  unfold NightHalf quarter
  rw [Nat.div_lt_iff_lt_mul hpos]
  omega

/-- The quarter of tick `t` as one of four indices. -/
def quarterIndex (length start t : Nat) : Fin 4 := ⟨min (quarter length start t) 3, by omega⟩

/-- The world whose day lasts `length` ticks with its night beginning `start` ticks before tick
0, where a night action costs `hi` and a daytime one `lo`, and the agent sees `sight q` in quarter
`q`, whatever the situation. -/
def clockWorld (length start : Nat) (lo hi : E) (sight : Fin 4 → Obs) : DayWorld Ctx Act Obs E where
  length := length
  night t := decide (NightHalf length start t)
  cost t _ _ := if NightHalf length start t then hi else lo
  sees t _ := sight (quarterIndex length start t)

/-- `clockWorld` meets the record for every positive even day length and every start, wherever
night costs more and the four sights differ. -/
theorem clockWorld_meets {length start : Nat} {lo hi : E} {sight : Fin 4 → Obs}
    (hpos : 0 < length) (heven : length % 2 = 0) (hlt : lo < hi)
    (hsight : ∀ i j, sight i = sight j → i = j) :
    (dayCycle Ctx Act Obs E).Meets (clockWorld length start lo hi sight) := by
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

/-- A world in which the agent sees only whether it is day or night, in a day of four ticks. The
record rules it out by reading "where in the day" as at least the quarter of the day. -/
def dayOrNightOnly (lo hi : E) (o₁ o₂ : Obs) : DayWorld Ctx Act Obs E :=
  { clockWorld (Ctx := Ctx) (Act := Act) 4 0 lo hi (fun _ => o₁) with
    sees := fun t _ => if NightHalf 4 0 t then o₁ else o₂ }

/-- Ticks 0 and 1 of `dayOrNightOnly` are both night and seen alike, yet lie in different
quarters of the day however the quarters are placed. -/
theorem dayCycle_refutes_dayOrNightOnly (c : Ctx) (lo hi : E) (o₁ o₂ : Obs) :
    ¬ (dayCycle Ctx Act Obs E).Meets (dayOrNightOnly lo hi o₁ o₂) := by
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

/-! ## Adequacy

The obligations need witnesses from the world's types: a situation and an action, four different
sights, and two energy amounts of which the first is less than the second and not less than
itself. Acorn's world has all of them; a world with no action, or with fewer than four sights,
could not meet the record, and its obligations O2 and O3 are stated under those witnesses. -/

/-- O2: the record has a model of its (empty) domain hypotheses and an instance of each
predicate of its vocabulary. -/
theorem dayCycle_o2 {lo hi : E} (hlt : lo < hi) (sight : Fin 4 → Obs) :
    O2 (dayCycle Ctx Act Obs E) := by
  refine (o2_correct _).mpr ⟨⟨clockWorld 2 0 lo hi sight, fun _ h => nomatch h⟩, ?_⟩
  intro p hp
  simp only [dayCycle, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨(2, 0, 0), show (0 + 0) % 2 < 2 / 2 by decide⟩
  · exact ⟨(lo, hi), hlt⟩
  · exact ⟨(4, 0, 0, 0), show quarter 4 0 0 = 0 by decide⟩

/-- O2 before running: a world meets the whole record. -/
theorem dayCycle_o2Run {lo hi : E} (hlt : lo < hi) {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) : O2Run (dayCycle Ctx Act Obs E) :=
  o2Run_of_meets (clockWorld_meets (length := 2) (start := 0) (by decide) (by decide) hlt hsight)

/-- O3: each property fails of some world. A day of no ticks fails `halves`; a world where every
action costs the same at every tick fails `nightCostsMore`; a world where the agent always sees
the same thing fails `tellsDayFromNight` and `seesQuarter`. -/
theorem dayCycle_o3 (c : Ctx) (a : Act) {lo hi : E} (hirr : ¬ lo < lo) (sight : Fin 4 → Obs) :
    O3 (dayCycle Ctx Act Obs E) := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [dayCycle, List.mem_cons, List.not_mem_nil, or_false] at hp
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

/-- O4: the subject is a description of the world's day with no state carried from one call to
the next, declared `.value`, of which O4 asks nothing. -/
theorem dayCycle_o4 : O4 (dayCycle Ctx Act Obs E) := (o4_correct _).mpr trivial

/-- O5 does not hold with equality: a day of two ticks and a day of four both meet the record. -/
theorem dayCycle_not_o5_eq {lo hi : E} (hlt : lo < hi) {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) : ¬ O5 (dayCycle Ctx Act Obs E) .eq :=
  not_o5_eq (clockWorld_meets (length := 2) (start := 0) (by decide) (by decide) hlt hsight)
    (clockWorld_meets (length := 4) (start := 0) (by decide) (by decide) hlt hsight)
    (fun h => absurd (congrArg DayWorld.length h) (show (2 : Nat) ≠ 4 by decide))

/-- O5 with the widest freedom, which every record meets: the freedoms are decided on the owner's
behalf in `AcornVerif.Intent.Decisions`. -/
theorem dayCycle_o5_widest : O5 (dayCycle Ctx Act Obs E) .widest := o5_widest _

end AcornVerif.Intent.DayCycle
