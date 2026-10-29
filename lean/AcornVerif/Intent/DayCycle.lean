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
where in the day it is. That statement is this record's only source. The record was written
before the source of `Acorn.Host.World.dayPhase`, the energy cost or the agent's observation was
read, and it names none of them.

The subject, `DayWorld`, is the day as the statement speaks of it: how many ticks a day lasts,
which ticks are night, the energy each action costs at each tick in each situation, and what the
agent sees at each tick in each situation. It is generic in the world's situations, actions,
sights and energy amounts, so that the record says nothing about how a world represents them; the
link to Acorn's world is a mapping proved in a later module.

Each property is one clause of the statement:

* `halves`: a day is a fixed number of ticks, the night is one unbroken stretch of half of them
  and the daytime the other half, and every day is alike. Reading "half" as one unbroken stretch
  and "each day" as every day alike are interpretations, shown to the owner as consequences.
* `nightCostsMore`: every action, in every situation, costs strictly more energy at every night
  tick than at every daytime tick.
* `seesTimeOfDay`: what the agent sees always tells it whether it is day or night. The statement
  leaves open how finely the agent sees where in the day it is; the record requires the coarsest
  reading, day or night, and shows the owner that a finer one is allowed and not required.

The statement leaves open how long a day is, where the first day starts, how much more the night
costs, and how finely the agent sees the time of day; those stay free here (`not_o5_eq`).
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
def seesTimeOfDay (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"the agent can always see where in the day it is, at least whether it is day or night",
    fun w => ∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t'⟩

/-- The intent record of the world's day and night. -/
def dayCycle (Ctx Act Obs E : Type) [LT E] : IntentRecord (DayWorld Ctx Act Obs E) where
  shape := .value _
  dom := []
  props := [halves Ctx Act Obs E, nightCostsMore Ctx Act Obs E, seesTimeOfDay Ctx Act Obs E]
  vocab := [⟨"night half", Nat × Nat × Nat, fun p => NightHalf p.1 p.2.1 p.2.2⟩,
    ⟨"costs less", E × E, fun p => p.1 < p.2⟩]

variable {Ctx Act Obs E : Type} [LT E]

/-- A world meets the record exactly when its day has two equal halves, every action costs more
by night, and its sights tell day from night. -/
theorem dayCycle_meets {w : DayWorld Ctx Act Obs E} :
    (dayCycle Ctx Act Obs E).Meets w ↔
      (0 < w.length ∧ w.length % 2 = 0 ∧
        ∃ start, ∀ t, w.night t = true ↔ NightHalf w.length start t) ∧
      (∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c a) ∧
      (∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t') := by
  constructor
  · intro h
    exact ⟨h.2 _ (List.mem_cons_self ..),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  · intro ⟨h1, h2, h3⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [dayCycle, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3

/-- The world whose day lasts `length` ticks with its night beginning `start` ticks before tick
0, where a night action costs `hi` and a daytime one `lo`, and the agent sees `o₁` by night and
`o₂` by day, whatever the situation. -/
def halfWorld (length start : Nat) (lo hi : E) (o₁ o₂ : Obs) : DayWorld Ctx Act Obs E where
  length := length
  night t := decide (NightHalf length start t)
  cost t _ _ := if NightHalf length start t then hi else lo
  sees t _ := if NightHalf length start t then o₁ else o₂

/-- `halfWorld` meets the record for every positive even day length and every start, wherever
night costs more and the two sights differ. -/
theorem halfWorld_meets {length start : Nat} {lo hi : E} {o₁ o₂ : Obs} (hpos : 0 < length)
    (heven : length % 2 = 0) (hlt : lo < hi) (ho : o₁ ≠ o₂) :
    (dayCycle Ctx Act Obs E).Meets (halfWorld length start lo hi o₁ o₂) := by
  refine dayCycle_meets.mpr ⟨⟨hpos, heven, start, fun t => decide_eq_true_iff⟩, ?_, ?_⟩
  · intro c a t t' ht ht'
    simp only [halfWorld, decide_eq_true_eq, decide_eq_false_iff_not] at ht ht' ⊢
    simp only [ht, ht', ↓reduceIte]
    exact hlt
  · intro t t' c c' hs
    simp only [halfWorld] at hs ⊢
    by_cases h : NightHalf length start t <;> by_cases h' : NightHalf length start t' <;>
      simp only [h, h', ↓reduceIte] at hs <;> simp [h, h']
    · exact absurd hs ho
    · exact absurd hs.symm ho

/-! ## Adequacy

The obligations need witnesses from the world's types: a situation and an action, two different
sights, and two energy amounts of which the first is less than the second and not less than
itself. Acorn's world has all of them; a world with no action, or with a single sight, could not
meet the record, and its obligations O2 and O3 are stated under those witnesses. -/

/-- O2: the record has a model of its (empty) domain hypotheses and an instance of each
predicate of its vocabulary. -/
theorem dayCycle_o2 {lo hi : E} (hlt : lo < hi) (o : Obs) : O2 (dayCycle Ctx Act Obs E) := by
  refine (o2_correct _).mpr ⟨⟨halfWorld 2 0 lo hi o o, fun _ h => nomatch h⟩, ?_⟩
  intro p hp
  simp only [dayCycle, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨(2, 0, 0), show (0 + 0) % 2 < 2 / 2 by decide⟩
  · exact ⟨(lo, hi), hlt⟩

/-- O2 before running: a world meets the whole record. -/
theorem dayCycle_o2Run {lo hi : E} (hlt : lo < hi) {o₁ o₂ : Obs} (ho : o₁ ≠ o₂) :
    O2Run (dayCycle Ctx Act Obs E) :=
  o2Run_of_meets (halfWorld_meets (length := 2) (start := 0) (by decide) (by decide) hlt ho)

/-- O3: each property fails of some world. A day of no ticks fails `halves`; a world where
every action costs the same at every tick fails `nightCostsMore`; a world where the agent always
sees the same thing fails `seesTimeOfDay`. -/
theorem dayCycle_o3 (c : Ctx) (a : Act) {lo hi : E} (hirr : ¬ lo < lo) (o₁ o₂ : Obs) :
    O3 (dayCycle Ctx Act Obs E) := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [dayCycle, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨{ halfWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi o₁ o₂ with length := 0 },
      fun h => Nat.lt_irrefl 0 h.1⟩
  · exact ⟨{ halfWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi o₁ o₂ with cost := fun _ _ _ => lo },
      fun h => hirr (h c a 0 1 rfl rfl)⟩
  · exact ⟨{ halfWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi o₁ o₂ with sees := fun _ _ => o₁ },
      fun h => Bool.noConfusion (h 0 1 c c rfl)⟩

/-- O4: the subject is a description of the world's day with no state carried from one call to
the next, declared `.value`, of which O4 asks nothing. -/
theorem dayCycle_o4 : O4 (dayCycle Ctx Act Obs E) := (o4_correct _).mpr trivial

/-- O5 does not hold with equality: a day of two ticks and a day of four both meet the record.
The record leaves free how long a day is, where the first night starts, how much more the night
costs, and how finely the agent sees the time of day. -/
theorem dayCycle_not_o5_eq {lo hi : E} (hlt : lo < hi) {o₁ o₂ : Obs} (ho : o₁ ≠ o₂) :
    ¬ O5 (dayCycle Ctx Act Obs E) .eq :=
  not_o5_eq (halfWorld_meets (length := 2) (start := 0) (by decide) (by decide) hlt ho)
    (halfWorld_meets (length := 4) (start := 0) (by decide) (by decide) hlt ho)
    (fun h => absurd (congrArg DayWorld.length h) (show (2 : Nat) ≠ 4 by decide))

/-- O5 with the widest freedom, which every record meets: the freedoms above are shown to the
owner as consequences. -/
theorem dayCycle_o5_widest : O5 (dayCycle Ctx Act Obs E) .widest := o5_widest _

end AcornVerif.Intent.DayCycle
