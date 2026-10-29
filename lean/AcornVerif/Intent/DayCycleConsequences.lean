/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.DayCycle

/-!
# The day record's consequences

Each consequence of the record that a design decision settles is a `LeanIntent.Consequence` with
a proof that it holds of the record, and `dayCycleExplained` glosses every statement of the record
in plain words. The decisions themselves, made on the owner's behalf, are recorded in
`AcornVerif.Intent.Decisions`. Three consequences answer where a second, blind formalization of
the same words by a model of another provider read them differently: it let days differ in
length (`everyDayAlike`), required the agent to read its exact position in the day
(`seesQuarterOfDay`, `dayOrNightOnlyWorld`) and priced every night moment of a day alike
(`nightCostVaries`).
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
  obtain ⟨⟨hpos, heven, s, hs⟩, -, -, -⟩ := dayCycle_meets.mp hw
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
def tellsDayFromNightAlways : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"what the agent sees always tells day from night", .entailment,
    fun w => ∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t'⟩

theorem tellsDayFromNightAlways_holds : (tellsDayFromNightAlways (Ctx := Ctx) (Act := Act)
    (Obs := Obs) (E := E)).HoldsOf (dayCycle Ctx Act Obs E) :=
  fun _ hw => (dayCycle_meets.mp hw).2.2.1

/-- What the agent sees always tells it the quarter of the day. -/
def seesQuarterOfDay : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"what the agent sees always tells it which quarter of the day it is in", .entailment,
    fun w => ∃ start, ∀ t t' c c', w.sees t c = w.sees t' c' →
      quarter w.length start t = quarter w.length start t'⟩

theorem seesQuarterOfDay_holds : (seesQuarterOfDay (Ctx := Ctx) (Act := Act) (Obs := Obs)
    (E := E)).HoldsOf (dayCycle Ctx Act Obs E) :=
  fun _ hw => (dayCycle_meets.mp hw).2.2.2

/-- A day of 1000 ticks is allowed. -/
def longDay : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"a day may last 1000 ticks", .possibility, fun w => w.length = 1000⟩

theorem longDay_holds {lo hi : E} (hlt : lo < hi) {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) :
    (longDay (Ctx := Ctx) (Act := Act) (Obs := Obs) (E := E)).HoldsOf
      (dayCycle Ctx Act Obs E) :=
  ⟨clockWorld 1000 0 lo hi sight, clockWorld_meets (by decide) (by decide) hlt hsight, rfl⟩

/-- The world in which the agent sees only whether it is day or night. -/
def dayOrNightOnlyWorld (lo hi : E) (o₁ o₂ : Obs) : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"the agent may see only whether it is day or night", .possibility,
    fun w => w = dayOrNightOnly lo hi o₁ o₂⟩

/-- The world of `clockWorld 4 0` whose night action costs `hi` in the first night tick of each
day and `hi'` in the second. -/
def varyingNight (lo hi hi' : E) (sight : Fin 4 → Obs) : DayWorld Ctx Act Obs E :=
  { clockWorld (Ctx := Ctx) (Act := Act) 4 0 lo hi sight with
    cost := fun t _ _ => if NightHalf 4 0 t then (if t % 4 = 0 then hi else hi') else lo }

theorem varyingNight_meets {lo hi hi' : E} (hlt : lo < hi) (hlt' : lo < hi')
    {sight : Fin 4 → Obs} (hsight : ∀ i j, sight i = sight j → i = j) :
    (dayCycle Ctx Act Obs E).Meets (varyingNight lo hi hi' sight) := by
  have base := dayCycle_meets.mp
    (clockWorld_meets (Ctx := Ctx) (Act := Act) (length := 4) (start := 0) (by decide)
      (by decide) hlt hsight)
  refine dayCycle_meets.mpr ⟨base.1, fun c a t t' ht ht' => ?_, base.2.2.1, base.2.2.2⟩
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
    (hlt' : lo < hi') (hne : hi ≠ hi') {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) :
    (nightCostVaries (Ctx := Ctx) (Act := Act) (Obs := Obs) (E := E)).HoldsOf
      (dayCycle Ctx Act Obs E) :=
  ⟨varyingNight lo hi hi' sight, varyingNight_meets hlt hlt' hsight, c, a, 0, 1,
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

/-- The day record explained in plain words, with its consequences. The consequences need a
situation `c`, an action `a`, three energy amounts with `lo` below the two different amounts `hi`
and `hi'`, and four different sights. -/
def dayCycleExplained (c : Ctx) (a : Act) {lo hi hi' : E} (hlt : lo < hi) (hlt' : lo < hi')
    (hne : hi ≠ hi') {sight : Fin 4 → Obs} (hsight : ∀ i j, sight i = sight j → i = j) :
    Explanation (dayCycle Ctx Act Obs E) where
  shape :=
    { requires := "The subject is a description of a world's day: how many ticks a day lasts, \
        which ticks are night, what each action costs at each tick in each situation, and what \
        the agent sees at each tick in each situation. Time is counted in whole ticks from the \
        start of a run, and one clock serves the whole world."
      rulesOut := "Nothing by itself; it fixes only what the statements below talk about."
      allows := "Any world's situations, actions, sights and energy amounts."
      freedom := "None of its own. It carries no state from one tick to the next, so it is \
        declared a plain value, of which obligation O4 asks nothing." }
  dom := []
  props := [
    { requires := "A day lasts a fixed, even number of ticks, at least two. The night is one \
        unbroken stretch of exactly half of them and the daytime the other half, and every day \
        is the same."
      rulesOut := "A world with no night or no daytime; a day of an odd number of ticks; a \
        night broken into several stretches; days of different lengths."
      allows := "Any even day length, and a night that starts at any tick of the day."
      freedom := "How long a day is and where in it the night starts." },
    { requires := "For every action and every situation, the action costs strictly more energy \
        at every night tick than at every daytime tick, waiting included."
      rulesOut := "Any action that, in some situation, costs as much or less at some night tick \
        than at some daytime tick."
      allows := "Any amount more at night, and a night cost that changes during the night, as \
        long as it stays above every daytime cost."
      freedom := "How much more the night costs, and whether that extra changes during the \
        night." },
    { requires := "Whatever the agent sees always tells it whether it is day or night."
      rulesOut := "An agent that sees a day moment and a night moment alike."
      allows := "An agent that sees more than that."
      freedom := "How much more it sees." },
    { requires := "Whatever the agent sees always tells it which quarter of the day it is in."
      rulesOut := "An agent that sees only whether it is day or night, in a day longer than \
        two ticks."
      allows := "An agent that sees the quarter, a finer part of the day, or the exact tick."
      freedom := "How much more finely than a quarter the agent sees the time of day." }]
  vocab := [
    { requires := "Tick t is in the night when, counted around a day of the given length from \
        where the night starts, it falls in the first half."
      rulesOut := "Tick 1 in a day of two ticks whose night starts at tick 0."
      allows := "Tick 0 in that day."
      freedom := "None: it is a definition." },
    { requires := "The world's own order on energy amounts."
      rulesOut := "Whatever that order rules out."
      allows := "Whatever that order allows."
      freedom := "None of its own." },
    { requires := "Tick t lies in the given quarter of a day of the given length, counted from \
        the given start."
      rulesOut := "Tick 0 in quarter 1 of a day of four ticks counted from tick 0."
      allows := "Tick 0 in quarter 0 of that day."
      freedom := "None: it is a definition." }]
  consequences := [
    ⟨everyDayAlike, everyDayAlike_holds,
      { requires := "Every day lasts the same even number of ticks, at least two, and each \
          day's night falls at the same ticks of the day."
        rulesOut := "Days of different lengths."
        allows := "Any one day length shared by all days."
        freedom := "The length itself." }⟩,
    ⟨nightAlwaysDearer, nightAlwaysDearer_holds,
      { requires := "Even the cheapest action costs more at any night moment than at any \
          daytime moment, in the same situation."
        rulesOut := "Any action that is no dearer at some night moment."
        allows := "Any extra amount."
        freedom := "How much more." }⟩,
    ⟨tellsDayFromNightAlways, tellsDayFromNightAlways_holds,
      { requires := "From what it sees, the agent can always tell whether it is day or night."
        rulesOut := "An agent that cannot tell day from night at some moment."
        allows := "An agent that sees more than that."
        freedom := "How much more it sees." }⟩,
    ⟨seesQuarterOfDay, seesQuarterOfDay_holds,
      { requires := "From what it sees, the agent can always tell which quarter of the day it \
          is in."
        rulesOut := "An agent that sees only day or night."
        allows := "Seeing a finer part of the day, or the exact tick."
        freedom := "How much finer than a quarter." }⟩,
    ⟨longDay, longDay_holds hlt hsight,
      { requires := "Nothing more: a world whose day lasts 1000 ticks can meet the record."
        rulesOut := "Nothing."
        allows := "Short days and long days alike."
        freedom := "The day's length." }⟩,
    ⟨nightCostVaries, nightCostVaries_holds c a hlt hlt' hne hsight,
      { requires := "Nothing more: an action may cost more at one night moment than at another, \
          as long as every night cost is above every daytime cost."
        rulesOut := "Nothing."
        allows := "A night that is dearer at midnight than at dusk."
        freedom := "Whether the night's extra changes during the night." }⟩]

end AcornVerif.Intent.DayCycle
