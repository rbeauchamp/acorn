import Acorn.Host.Metrics

namespace Acorn.Host.Viewer.GoalAchievement

structure Pass (goals : Nat) where
  resolved : Fin (goals + 1)
  achieved : Fin (resolved.val + 1)

def Pass.empty (goals : Nat) : Pass goals := ⟨0, 0⟩

def Pass.resolve {goals : Nat} (pass : Pass goals) (room : pass.resolved.val < goals)
    (success : Bool) : Pass goals :=
  ⟨⟨pass.resolved.val + 1, by omega⟩,
    ⟨pass.achieved.val + (if success then 1 else 0), by
      change pass.achieved.val + (if success then 1 else 0) < pass.resolved.val + 1 + 1
      have := pass.achieved.isLt
      split <;> omega⟩⟩

theorem Pass.resolve_counts {goals : Nat} (pass : Pass goals) (room : pass.resolved.val < goals)
    (success : Bool) :
    (pass.resolve room success).resolved.val = pass.resolved.val + 1 ∧
    (pass.resolve room success).achieved.val = pass.achieved.val + (if success then 1 else 0) :=
  ⟨rfl, rfl⟩

structure Complete (goals : Nat) where
  cycle : UInt64
  pass : Pass goals
  complete : pass.resolved.val = goals

structure GoalResult (attempts : Nat) where
  failures : Fin (attempts + 1)
  successSteps : Option UInt64
  successRoom : successSteps.isSome = true → failures.val < attempts

def GoalResult.empty (attempts : Nat) : GoalResult attempts := ⟨0, none, by simp⟩

def GoalResult.ofOutcome {attempts : Nat} (outcome : GoalOutcome)
    (room : outcome.attempt.toNat < attempts) : GoalResult attempts :=
  if success : outcome.achieved then
    ⟨⟨outcome.attempt.toNat, by omega⟩, some outcome.steps, fun _ => room⟩
  else ⟨⟨outcome.attempt.toNat + 1, by omega⟩, none, by simp⟩

theorem GoalResult.ofOutcome_counts {attempts : Nat} (outcome : GoalOutcome)
    (room : outcome.attempt.toNat < attempts) :
    (ofOutcome outcome room).failures.val =
      outcome.attempt.toNat + (if outcome.achieved then 0 else 1) ∧
    (ofOutcome outcome room).successSteps =
      (if outcome.achieved then some outcome.steps else none) := by
  unfold ofOutcome
  split <;> simp_all

structure State (goals attempts : Nat) where
  cycle : UInt64
  current : Pass goals
  nextAttempt : Fin (attempts + 1)
  latest : Option (Complete goals)
  results : Vector (GoalResult attempts) goals
  invalid : Bool

def State.empty (goals attempts : Nat) : State goals attempts :=
  ⟨0, Pass.empty goals, 0, none, Vector.replicate goals (GoalResult.empty attempts), false⟩

def State.begin {goals attempts : Nat} (state : State goals attempts) (cycle : UInt64) :
    State goals attempts :=
  if cycle == state.cycle then state
  else if state.current.resolved.val = goals ∧ cycle.toNat = state.cycle.toNat + 1 then
    { state with cycle, current := Pass.empty goals, nextAttempt := 0, results := Vector.replicate goals (GoalResult.empty attempts) }
  else { state with invalid := true }

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

theorem State.observe_results {goals attempts : Nat} (state : State goals attempts)
    (outcome : GoalOutcome) (valid : state.invalid = false)
    (goalOrder : outcome.index.toNat = state.current.resolved.val)
    (attemptOrder : outcome.attempt.toNat = state.nextAttempt.val)
    (room : state.current.resolved.val < goals) (attemptRoom : state.nextAttempt.val < attempts) :
    (state.observe outcome).results = state.results.set state.current.resolved.val
      (GoalResult.ofOutcome outcome (by omega)) room := by
  by_cases resolution : (outcome.achieved || state.nextAttempt.val + 1 == attempts) = true
  all_goals simp [observe, valid, goalOrder, attemptOrder, room, attemptRoom, resolution]

theorem State.begin_results {goals attempts : Nat} (state : State goals attempts) (cycle : UInt64)
    (different : (cycle == state.cycle) = false)
    (complete : state.current.resolved.val = goals)
    (successor : cycle.toNat = state.cycle.toNat + 1) :
    (state.begin cycle).results = Vector.replicate goals (GoalResult.empty attempts) := by
  simp [begin, different, complete, successor]

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

theorem State.observe_wrong_goal {goals attempts : Nat} (state : State goals attempts)
    (outcome : GoalOutcome) (wrong : outcome.index.toNat ≠ state.current.resolved.val) :
    (state.observe outcome).invalid = true := by
  unfold observe
  split
  · assumption
  · simp [wrong]

def State.headline {goals attempts : Nat} (state : State goals attempts) : Option (Pass goals) :=
  if state.invalid || goals == 0 then none else
    some (state.latest.map (·.pass) |>.getD state.current)

theorem State.headline_latest {goals attempts : Nat} (state : State goals attempts)
    (complete : Complete goals) (latest : state.latest = some complete)
    (valid : state.invalid = false) (positive : 0 < goals) :
    state.headline = some complete.pass := by
  simp [headline, latest, valid, Nat.ne_of_gt positive]

def Pass.permille {goals : Nat} (pass : Pass goals) : Nat :=
  1000 * pass.achieved.val / goals

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

theorem Pass.permille_precision {goals : Nat} (pass : Pass goals) (positive : 0 < goals) :
    pass.permille * goals ≤ 1000 * pass.achieved.val ∧
      1000 * pass.achieved.val < (pass.permille + 1) * goals := by
  exact ⟨Nat.div_mul_le_self _ _, (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_self _)⟩

theorem State.begin_latest {goals attempts : Nat} (state : State goals attempts) (cycle : UInt64) :
    (state.begin cycle).latest = state.latest := by
  unfold begin
  split <;> first | rfl | (split <;> rfl)

theorem State.invalid_no_headline {goals attempts : Nat} (state : State goals attempts)
    (invalid : state.invalid = true) : state.headline = none := by
  simp [headline, invalid]

end Acorn.Host.Viewer.GoalAchievement
