/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Metrics

/-!
# Goal achievement over the admitted curriculum

The operational outcome is the fraction of assigned goals achieved within the
campaign's existing attempt and step budgets. Each resolved goal contributes
once. The latest complete pass remains the headline while the next pass unfolds;
the first incomplete pass is explicitly provisional. No trajectory is retained.

Research rationale: Richard S. Sutton, Michael Bowling and Patrick M. Pilarski,
The Alberta Plan for AI Research, arXiv:2208.11173v3 (2023), section "Designing
around a base agent", pp. 4–5: learning and planning serve the primary policy's
reward objective. Khurram Javed and Richard S. Sutton, The Big World Hypothesis
and its Ramifications for Artificial Intelligence, Oak Lab research article
(2024), sections "The Big World Hypothesis" and "Benchmarking Algorithms in Big
Worlds": limited understanding is judged by decisions in a specified environment.
Acorn defines the curriculum fraction above for the admitted goals and budgets.
-/
namespace Acorn.Host.Viewer.GoalAchievement

/-- Counts retain the success/resolution/population relation at every write. -/
structure Pass (goals : Nat) where
  /-- Number of goals whose success or attempt exhaustion has been observed. -/
  resolved : Fin (goals + 1)
  /-- Successful resolutions, at most one per goal. -/
  achieved : Fin (resolved.val + 1)

/-- Unobserved goals receive no success credit and are not declared failures. -/
def Pass.empty (goals : Nat) : Pass goals := ⟨0, 0⟩

/-- Record exactly one resolved goal; the population cannot grow. -/
def Pass.resolve {goals : Nat} (pass : Pass goals) (room : pass.resolved.val < goals)
    (success : Bool) : Pass goals :=
  ⟨⟨pass.resolved.val + 1, by omega⟩,
    ⟨pass.achieved.val + (if success then 1 else 0), by
      change pass.achieved.val + (if success then 1 else 0) < pass.resolved.val + 1 + 1
      have := pass.achieved.isLt
      split <;> omega⟩⟩

/-- Goal accounting is exact, including unsuccessful resolutions. -/
theorem Pass.resolve_counts {goals : Nat} (pass : Pass goals) (room : pass.resolved.val < goals)
    (success : Bool) :
    (pass.resolve room success).resolved.val = pass.resolved.val + 1 ∧
    (pass.resolve room success).achieved.val = pass.achieved.val + (if success then 1 else 0) :=
  ⟨rfl, rfl⟩

/-- A completed result cannot contain unresolved assigned goals. -/
structure Complete (goals : Nat) where
  /-- Actual zero-based campaign pass. -/
  cycle : UInt64
  /-- Counts for that pass. -/
  pass : Pass goals
  /-- All assigned goals have a resolution. -/
  complete : pass.resolved.val = goals

/-- Compact evidence for one goal, bounded by its admitted attempt budget. -/
structure GoalResult (attempts : Nat) where
  /-- Exact completed unsuccessful attempts. -/
  failures : Fin (attempts + 1)
  /-- Actual action count of the successful attempt, including legitimate zero. -/
  successSteps : Option UInt64
  /-- A success consumes an attempt beyond its preceding failures. -/
  successRoom : successSteps.isSome = true → failures.val < attempts

/-- No outcomes have occurred for a newly admitted goal. -/
def GoalResult.empty (attempts : Nat) : GoalResult attempts := ⟨0, none, by simp⟩

/-- Ordered attempt indices count preceding failures exactly; no trajectory is retained. -/
def GoalResult.ofOutcome {attempts : Nat} (outcome : GoalOutcome)
    (room : outcome.attempt.toNat < attempts) : GoalResult attempts :=
  if success : outcome.achieved then
    ⟨⟨outcome.attempt.toNat, by omega⟩, some outcome.steps, fun _ => room⟩
  else ⟨⟨outcome.attempt.toNat + 1, by omega⟩, none, by simp⟩

/-- Compact rows preserve the exact failure count and success action count. -/
theorem GoalResult.ofOutcome_counts {attempts : Nat} (outcome : GoalOutcome)
    (room : outcome.attempt.toNat < attempts) :
    (ofOutcome outcome room).failures.val =
      outcome.attempt.toNat + (if outcome.achieved then 0 else 1) ∧
    (ofOutcome outcome room).successSteps =
      (if outcome.achieved then some outcome.steps else none) := by
  unfold ofOutcome
  split <;> simp_all

/-- Fixed-size, process-local sufficient state; no checkpoint imports an old pass. -/
structure State (goals attempts : Nat) where
  /-- Actual zero-based campaign pass. -/
  cycle : UInt64
  /-- Current pass, including a completed one before the next begins. -/
  current : Pass goals
  /-- The only next legal attempt within the current goal. -/
  nextAttempt : Fin (attempts + 1)
  /-- Latest complete pass, retained throughout an incomplete successor. -/
  latest : Option (Complete goals)
  /-- One compact result for every admitted goal in the current pass. -/
  results : Vector (GoalResult attempts) goals
  /-- Sticky refusal for missing, repeated or out-of-order boundary evidence. -/
  invalid : Bool

/-- Every process, including a resumed learner, begins without outcome evidence. -/
def State.empty (goals attempts : Nat) : State goals attempts :=
  ⟨0, Pass.empty goals, 0, none, Vector.replicate goals (GoalResult.empty attempts), false⟩

/-- Begin only the immediate successor of a fully resolved pass. A saturated
cycle counter refuses another indistinguishable pass instead of merging it. -/
def State.begin {goals attempts : Nat} (state : State goals attempts) (cycle : UInt64) :
    State goals attempts :=
  if cycle == state.cycle then state
  else if state.current.resolved.val = goals ∧ cycle.toNat = state.cycle.toNat + 1 then
    { state with cycle, current := Pass.empty goals, nextAttempt := 0, results := Vector.replicate goals (GoalResult.empty attempts) }
  else { state with invalid := true }

/-- Resolve an admitted outcome only after success or exhaustion of the same
attempt budget used by campaign progression. Earlier failures only advance the
expected attempt index; they neither reweight nor finish a goal. -/
def State.observe {goals attempts : Nat} (state : State goals attempts) (outcome : GoalOutcome) :
    State goals attempts :=
  if state.invalid then state
  else if badOrder : outcome.index.toNat ≠ state.current.resolved.val ∨
      outcome.attempt.toNat ≠ state.nextAttempt.val then { state with invalid := true }
  else if room : state.current.resolved.val < goals then
    if attemptRoom : state.nextAttempt.val < attempts then
      let results := state.results.set state.current.resolved.val
        (GoalResult.ofOutcome outcome (by
          have : outcome.attempt.toNat = state.nextAttempt.val := by omega
          omega)) room
      if outcome.achieved || state.nextAttempt.val + 1 == attempts then
        let current := state.current.resolve room outcome.achieved
        let latest := if complete : current.resolved.val = goals then
          some ⟨state.cycle, current, complete⟩ else state.latest
        { state with current, nextAttempt := 0, latest, results }
      else { state with nextAttempt := ⟨state.nextAttempt.val + 1, by omega⟩, results }
    else { state with invalid := true }
  else { state with invalid := true }

/-- Every admitted outcome replaces precisely its indexed compact result. -/
theorem State.observe_results {goals attempts : Nat} (state : State goals attempts)
    (outcome : GoalOutcome) (valid : state.invalid = false)
    (goalOrder : outcome.index.toNat = state.current.resolved.val)
    (attemptOrder : outcome.attempt.toNat = state.nextAttempt.val)
    (room : state.current.resolved.val < goals) (attemptRoom : state.nextAttempt.val < attempts) :
    (state.observe outcome).results = state.results.set state.current.resolved.val
      (GoalResult.ofOutcome outcome (by omega)) room := by
  by_cases resolution : (outcome.achieved || state.nextAttempt.val + 1 == attempts) = true
  all_goals simp [observe, valid, goalOrder, attemptOrder, room, attemptRoom, resolution]

/-- A successor starts every compact goal result without prior-pass evidence. -/
theorem State.begin_results {goals attempts : Nat} (state : State goals attempts) (cycle : UInt64)
    (different : (cycle == state.cycle) = false)
    (complete : state.current.resolved.val = goals)
    (successor : cycle.toNat = state.cycle.toNat + 1) :
    (state.begin cycle).results = Vector.replicate goals (GoalResult.empty attempts) := by
  simp [begin, different, complete, successor]

/-- Ordered successful or exhausted outcomes resolve exactly one goal. -/
theorem State.observe_resolution {goals attempts : Nat} (state : State goals attempts)
    (outcome : GoalOutcome) (valid : state.invalid = false)
    (goalOrder : outcome.index.toNat = state.current.resolved.val)
    (attemptOrder : outcome.attempt.toNat = state.nextAttempt.val)
    (room : state.current.resolved.val < goals) (attemptRoom : state.nextAttempt.val < attempts)
    (resolution : (outcome.achieved || state.nextAttempt.val + 1 == attempts) = true) :
    (state.observe outcome).current.resolved.val = state.current.resolved.val + 1 ∧
    (state.observe outcome).current.achieved.val =
      state.current.achieved.val + (if outcome.achieved then 1 else 0) ∧
    (state.observe outcome).invalid = false := by
  have current : (state.observe outcome).current = state.current.resolve room outcome.achieved := by
    simp [observe, valid, goalOrder, attemptOrder, room, attemptRoom, resolution]
  refine ⟨congrArg (fun pass => pass.resolved.val) current,
    congrArg (fun pass => pass.achieved.val) current, ?_⟩
  simp [observe, valid, goalOrder, attemptOrder, room, attemptRoom, resolution]

/-- An unsuccessful non-final retry keeps both goal counts and the last complete pass. -/
theorem State.observe_retry {goals attempts : Nat} (state : State goals attempts)
    (outcome : GoalOutcome) (valid : state.invalid = false)
    (goalOrder : outcome.index.toNat = state.current.resolved.val)
    (attemptOrder : outcome.attempt.toNat = state.nextAttempt.val)
    (room : state.current.resolved.val < goals) (attemptRoom : state.nextAttempt.val < attempts)
    (retry : (outcome.achieved || state.nextAttempt.val + 1 == attempts) = false) :
    (state.observe outcome).current = state.current ∧
    (state.observe outcome).latest = state.latest ∧
    (state.observe outcome).nextAttempt.val = state.nextAttempt.val + 1 := by
  simp [observe, valid, goalOrder, attemptOrder, room, attemptRoom, retry]

/-- A repeated resolved goal or skipped goal is refused at the accumulation boundary. -/
theorem State.observe_wrong_goal {goals attempts : Nat} (state : State goals attempts)
    (outcome : GoalOutcome) (wrong : outcome.index.toNat ≠ state.current.resolved.val) :
    (state.observe outcome).invalid = true := by
  unfold observe
  split
  · assumption
  · simp [wrong]

/-- The headline prefers the latest complete population, otherwise names the
current partial evidence. Invalid accounting never supplies a numeric score. -/
def State.headline {goals attempts : Nat} (state : State goals attempts) : Option (Pass goals) :=
  if state.invalid || goals == 0 then none else
    some (state.latest.map (·.pass) |>.getD state.current)

/-- A valid headline selects the complete population without blending current evidence. -/
theorem State.headline_latest {goals attempts : Nat} (state : State goals attempts)
    (complete : Complete goals) (latest : state.latest = some complete)
    (valid : state.invalid = false) (positive : 0 < goals) :
    state.headline = some complete.pass := by
  simp [headline, latest, valid, Nat.ne_of_gt positive]

/-- Tenths of a percent, rounded down from the exact goal fraction. -/
def Pass.permille {goals : Nat} (pass : Pass goals) : Nat :=
  1000 * pass.achieved.val / goals

/-- Every displayed fraction lies within its defined 0–100 percent range. -/
theorem Pass.permille_bounded {goals : Nat} (pass : Pass goals) : pass.permille ≤ 1000 := by
  have successes := pass.achieved.isLt
  have population := pass.resolved.isLt
  unfold permille
  by_cases positive : 0 < goals
  · apply (Nat.div_le_iff_le_mul_add_pred positive).mpr
    have bound : pass.achieved.val ≤ goals := by omega
    have := Nat.mul_le_mul_left 1000 bound
    omega
  · have : goals = 0 := by omega
    simp [this]

/-- The exact fraction is enclosed within one display quantum. -/
theorem Pass.permille_precision {goals : Nat} (pass : Pass goals) (positive : 0 < goals) :
    pass.permille * goals ≤ 1000 * pass.achieved.val ∧
      1000 * pass.achieved.val < (pass.permille + 1) * goals := by
  exact ⟨Nat.div_mul_le_self _ _, (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_self _)⟩

/-- A partial successor preserves the last complete result without blending populations. -/
theorem State.begin_latest {goals attempts : Nat} (state : State goals attempts) (cycle : UInt64) :
    (state.begin cycle).latest = state.latest := by
  unfold begin
  split <;> first | rfl | (split <;> rfl)

/-- Sticky faults suppress the headline rather than manufacturing zero performance. -/
theorem State.invalid_no_headline {goals attempts : Nat} (state : State goals attempts)
    (invalid : state.invalid = true) : state.headline = none := by
  simp [headline, invalid]

end Acorn.Host.Viewer.GoalAchievement
