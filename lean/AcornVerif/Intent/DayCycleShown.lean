/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.DayCycle

/-!
# The day record's consequences, as shown to the owner

Each consequence the owner is asked to confirm or decline is a `LeanIntent.Consequence` with a
proof that it holds of the record as shown (`LeanIntent.Shown`), and `dayCycleExplained` glosses
every statement of the record in plain words. Three consequences come from a second, blind
formalization of the same words by a model of another provider, which read the agent's sight
of the time of day as its exact position in the day, let days differ in length, and priced every
night moment of a day alike: `seesOnlyDayOrNight`, `everyDayAlike` and `nightCostVaries` show
the owner where this record decides those points the other way.
-/

namespace AcornVerif.Intent.DayCycle

open LeanIntent

variable {Ctx Act Obs E : Type} [LT E]

/-- Every day lasts the same even number of ticks, at least two, and is placed alike. -/
def everyDayAlike : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"every day lasts the same even number of ticks, at least two, placed alike", .entailment,
    fun w => 2 ≤ w.length ∧ w.length % 2 = 0 ∧ ∀ t, w.night (t + w.length) = w.night t⟩

theorem everyDayAlike_holds : (everyDayAlike (Ctx := Ctx) (Act := Act) (Obs := Obs)
    (E := E)).HoldsOf (dayCycle Ctx Act Obs E) := by
  intro w hw
  obtain ⟨⟨hpos, heven, s, hs⟩, -, -⟩ := dayCycle_meets.mp hw
  refine ⟨by omega, heven, fun t => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [hs, hs]
  show (t + w.length + s) % w.length < _ ↔ (t + s) % w.length < _
  rw [Nat.add_right_comm, Nat.add_mod_right]

/-- Every action costs more at every night moment than at every daytime moment. -/
def nightAlwaysDearer : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"every action costs more at any night moment than at any daytime moment", .entailment,
    fun w => ∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c a⟩

theorem nightAlwaysDearer_holds : (nightAlwaysDearer (Ctx := Ctx) (Act := Act) (Obs := Obs)
    (E := E)).HoldsOf (dayCycle Ctx Act Obs E) :=
  fun _ hw => (dayCycle_meets.mp hw).2.1

/-- What the agent sees always tells day from night. -/
def tellsDayFromNight : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"what the agent sees always tells day from night", .entailment,
    fun w => ∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t'⟩

theorem tellsDayFromNight_holds : (tellsDayFromNight (Ctx := Ctx) (Act := Act) (Obs := Obs)
    (E := E)).HoldsOf (dayCycle Ctx Act Obs E) :=
  fun _ hw => (dayCycle_meets.mp hw).2.2

/-- A day of 1000 ticks is allowed. -/
def longDay : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"a day may last 1000 ticks", .possibility, fun w => w.length = 1000⟩

theorem longDay_holds {lo hi : E} (hlt : lo < hi) {o₁ o₂ : Obs} (ho : o₁ ≠ o₂) :
    (longDay (Ctx := Ctx) (Act := Act) (Obs := Obs) (E := E)).HoldsOf
      (dayCycle Ctx Act Obs E) :=
  ⟨halfWorld 1000 0 lo hi o₁ o₂, halfWorld_meets (by decide) (by decide) hlt ho, rfl⟩

/-- The agent may see only whether it is day or night, in a day longer than two ticks. -/
def seesOnlyDayOrNight : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"the agent may see only whether it is day or night, not where in the day", .possibility,
    fun w => 2 < w.length ∧ ∀ t t' c, w.night t = w.night t' → w.sees t c = w.sees t' c⟩

theorem seesOnlyDayOrNight_holds {lo hi : E} (hlt : lo < hi) {o₁ o₂ : Obs} (ho : o₁ ≠ o₂) :
    (seesOnlyDayOrNight (Ctx := Ctx) (Act := Act) (Obs := Obs) (E := E)).HoldsOf
      (dayCycle Ctx Act Obs E) := by
  refine ⟨halfWorld 4 0 lo hi o₁ o₂, halfWorld_meets (by decide) (by decide) hlt ho,
    show 2 < 4 by decide, fun t t' c h => ?_⟩
  simp only [halfWorld, decide_eq_decide] at h ⊢
  simp only [h]

/-- The world of `halfWorld 4 0` whose night action costs `hi` in the first night tick of each
day and `hi'` in the second. -/
def varyingNight (lo hi hi' : E) (o₁ o₂ : Obs) : DayWorld Ctx Act Obs E :=
  { halfWorld (Ctx := Ctx) (Act := Act) 4 0 lo hi o₁ o₂ with
    cost := fun t _ _ => if NightHalf 4 0 t then (if t % 4 = 0 then hi else hi') else lo }

theorem varyingNight_meets {lo hi hi' : E} (hlt : lo < hi) (hlt' : lo < hi') {o₁ o₂ : Obs}
    (ho : o₁ ≠ o₂) : (dayCycle Ctx Act Obs E).Meets (varyingNight lo hi hi' o₁ o₂) := by
  have base := dayCycle_meets.mp
    (halfWorld_meets (Ctx := Ctx) (Act := Act) (length := 4) (start := 0) (by decide)
      (by decide) hlt ho)
  refine dayCycle_meets.mpr ⟨base.1, fun c a t t' ht ht' => ?_, base.2.2⟩
  have hn : NightHalf 4 0 t := of_decide_eq_true (show decide (NightHalf 4 0 t) = true from ht)
  have hd : ¬ NightHalf 4 0 t' :=
    of_decide_eq_false (show decide (NightHalf 4 0 t') = false from ht')
  show (if NightHalf 4 0 t' then (if t' % 4 = 0 then hi else hi') else lo) <
    (if NightHalf 4 0 t then (if t % 4 = 0 then hi else hi') else lo)
  rw [ite_eq_right hd, ite_eq_left hn]
  split
  · exact hlt
  · exact hlt'

/-- Night costs may differ between two moments of the same night. -/
def nightCostVaries : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"an action may cost more at one night moment than at another", .possibility,
    fun w => ∃ c a t t', w.night t = true ∧ w.night t' = true ∧ w.cost t c a ≠ w.cost t' c a⟩

theorem nightCostVaries_holds (c : Ctx) (a : Act) {lo hi hi' : E} (hlt : lo < hi)
    (hlt' : lo < hi') (hne : hi ≠ hi') {o₁ o₂ : Obs} (ho : o₁ ≠ o₂) :
    (nightCostVaries (Ctx := Ctx) (Act := Act) (Obs := Obs) (E := E)).HoldsOf
      (dayCycle Ctx Act Obs E) :=
  ⟨varyingNight lo hi hi' o₁ o₂, varyingNight_meets hlt hlt' ho, c, a, 0, 1,
    (by decide : decide (NightHalf 4 0 0) = true), (by decide : decide (NightHalf 4 0 1) = true),
    by
      have h0 : NightHalf 4 0 0 := by decide
      have h1 : NightHalf 4 0 1 := by decide
      have z0 : (0 : Nat) % 4 = 0 := by decide
      have z1 : ¬ (1 : Nat) % 4 = 0 := by decide
      show (if NightHalf 4 0 0 then (if 0 % 4 = 0 then hi else hi') else lo) ≠
        (if NightHalf 4 0 1 then (if 1 % 4 = 0 then hi else hi') else lo)
      rw [ite_eq_left h0, ite_eq_left z0, ite_eq_left h1, ite_eq_right z1]
      exact hne⟩

/-! ## The record explained -/

/-- The plain words for the record's shape. -/
def dayWorldShape : Gloss where
  requires := "The subject is a description of a world's day: how many ticks a day lasts, which \
    ticks are night, what each action costs at each tick in each situation, and what the agent \
    sees at each tick in each situation. Time is counted in whole ticks from the start of a run, \
    and one clock serves the whole world."
  rulesOut := "Nothing by itself; it fixes only what the statements below talk about."
  allows := "Any world's situations, actions, sights and energy amounts: the record does not \
    say how a world represents them."
  freedom := "None of its own. It carries no state from one tick to the next, so it is declared \
    a plain value, of which obligation O4 asks nothing."

/-- The plain words for `halves`. -/
def halvesGloss : Gloss where
  requires := "A day lasts a fixed, even number of ticks, at least two. The night is one \
    unbroken stretch of exactly half of them and the daytime the other half, and every day is \
    the same."
  rulesOut := "A world with no night or no daytime; a day of an odd number of ticks; a night \
    broken into several stretches; days of different lengths or with the night in different \
    places."
  allows := "Any even day length, and a night that starts at any tick of the day."
  freedom := "How long a day is and where in it the night starts."

/-- The plain words for `nightCostsMore`. -/
def nightCostsMoreGloss : Gloss where
  requires := "For every action and every situation, the action costs strictly more energy at \
    every night tick than at every daytime tick, actions such as waiting included."
  rulesOut := "Any action that, in some situation, costs as much or less at some night tick \
    than at some daytime tick."
  allows := "Any amount more at night, and a night cost that changes from one night tick to \
    another, as long as it stays above every daytime cost."
  freedom := "How much more the night costs, and whether that extra changes during the night."

/-- The plain words for `seesTimeOfDay`. -/
def seesTimeOfDayGloss : Gloss where
  requires := "Whatever the agent sees always tells it whether it is day or night: two moments \
    it sees the same way are both night or both day."
  rulesOut := "An agent that, at some day moment and some night moment, sees exactly the same."
  allows := "An agent that sees only day or night, one that sees which part of the day it is \
    in, and one that sees the exact tick of the day."
  freedom := "How finely the agent sees where in the day it is: the record reads 'where in the \
    day' as at least day or night."

/-- The plain words for the predicate `night half`. -/
def nightHalfGloss : Gloss where
  requires := "Tick t is in the night when, counted around a day of the given length from where \
    the night starts, it falls in the first half."
  rulesOut := "Tick 1 in a day of two ticks whose night starts at tick 0."
  allows := "Tick 0 in that day."
  freedom := "None: it is a definition."

/-- The plain words for the predicate `costs less`. -/
def costsLessGloss : Gloss where
  requires := "The world's own order on energy amounts: the first amount is less than the second."
  rulesOut := "Whatever the world's order rules out."
  allows := "Whatever the world's order allows."
  freedom := "None of its own: it is the world's order on energy."

/-- The day record explained for its owner. The consequences need a situation `c`, an action
`a`, three energy amounts with `lo` below the two different amounts `hi` and `hi'`, and two
different sights. -/
def dayCycleExplained (c : Ctx) (a : Act) {lo hi hi' : E} (hlt : lo < hi) (hlt' : lo < hi')
    (hne : hi ≠ hi') {o₁ o₂ : Obs} (ho : o₁ ≠ o₂) : Explanation (dayCycle Ctx Act Obs E) where
  shape := dayWorldShape
  dom := []
  props := [halvesGloss, nightCostsMoreGloss, seesTimeOfDayGloss]
  vocab := [nightHalfGloss, costsLessGloss]
  consequences := [
    ⟨everyDayAlike, everyDayAlike_holds,
      { requires := "Every day lasts the same even number of ticks, at least two, and each day's \
          night falls at the same ticks of the day."
        rulesOut := "Days of different lengths. A second, blind reading of your words allowed \
          them."
        allows := "Any one day length shared by all days."
        freedom := "The length itself." }⟩,
    ⟨nightAlwaysDearer, nightAlwaysDearer_holds,
      { requires := "Even the cheapest action, waiting included, costs more at any night moment \
          than at any daytime moment, in the same situation."
        rulesOut := "Any action that is free, or no dearer, at some night moment."
        allows := "Any extra amount."
        freedom := "How much more." }⟩,
    ⟨tellsDayFromNight, tellsDayFromNight_holds,
      { requires := "From what it sees, the agent can always tell whether it is day or night."
        rulesOut := "An agent that cannot tell day from night at some moment."
        allows := "An agent that sees more than that."
        freedom := "How much more it sees." }⟩,
    ⟨longDay, longDay_holds hlt ho,
      { requires := "Nothing more: a world whose day lasts 1000 ticks can meet the record."
        rulesOut := "Nothing."
        allows := "Short days and long days alike: the record does not fix the day's length."
        freedom := "The day's length." }⟩,
    ⟨seesOnlyDayOrNight, seesOnlyDayOrNight_holds hlt ho,
      { requires := "Nothing more: an agent that sees only whether it is day or night, and \
          nothing of where in the day it is, can meet the record."
        rulesOut := "Nothing."
        allows := "Seeing only day or night. A second, blind reading of your words required the \
          agent to read its exact position in the day."
        freedom := "Whether the agent must see more than day or night." }⟩,
    ⟨nightCostVaries, nightCostVaries_holds c a hlt hlt' hne ho,
      { requires := "Nothing more: an action may cost more at one night moment than at another, \
          as long as every night cost is above every daytime cost."
        rulesOut := "Nothing."
        allows := "A night that is dearer at midnight than at dusk. A second, blind reading of \
          your words priced every night moment of a day alike."
        freedom := "Whether the night's extra may change during the night." }⟩]

end AcornVerif.Intent.DayCycle
