/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Ansi
import Acorn.Host.Baseline
import AcornVerif.CurrentWorld

/-!
# Current attempt and supervision invariants

The same prepared-action and commit definitions are called by the native
runner. Callbacks supply the full agent; no learned transition is modeled or
invented here. IO event order is linked through the native call gate and source
review, while these universal claims own the pure admission and progression.
-/
namespace AcornVerif.CurrentRunner
open Acorn Acorn.Host

/-- Every successful commit consumes exactly one of the prepared remaining steps. -/
theorem commit_steps {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (prepared : PreparedStep config α β goal cap) (callbacks : AgentCallbacks α β)
    (next : Attempt config α goal cap) (h : prepared.commit callbacks = .ok next) :
    next.steps.val = prepared.before.steps.val + 1 := by
  unfold PreparedStep.commit PreparedStep.environment at h
  split at h
  · contradiction
  · cases Except.ok.inj h
    rfl

/-- The world phase of a prepared commit advances exactly one physical clock tick. -/
theorem commit_clock {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (prepared : PreparedStep config α β goal cap) (callbacks : AgentCallbacks α β)
    (next : Attempt config α goal cap) (h : prepared.commit callbacks = .ok next) :
    next.run.world.time = prepared.before.run.world.time + 1 := by
  unfold PreparedStep.commit PreparedStep.environment at h
  split at h
  · contradiction
  · rename_i world result hs
    cases Except.ok.inj h
    exact World.step_clock _ _ _ _ hs

/-- Every admitted attempt state preserves its receiving task and finite step budget. -/
theorem attempt_bounds {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) :
    attempt.run.world.goal = some goal ∧ attempt.steps.val ≤ cap.toNat :=
  ⟨attempt.installed, by have := attempt.steps.isLt; omega⟩

/-- A non-stopping boundary never produces the stopped outcome. -/
theorem boundary_running {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (achieved : Bool) : atAttemptBoundary cursor achieved false ≠ .stopped := by
  unfold atAttemptBoundary atAttemptBoundary.nextGoal
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · split
    · intro h; cases h
    · split
      · intro h; cases h
      · split <;> intro h <;> cases h
  · split
    · intro h; cases h
    · split <;> intro h <;> cases h

/-- A refused image cannot yield a writable destination, even at a stop boundary. -/
theorem checkpoint_refusal (path : System.FilePath) (interval : UInt32) :
    WritableCheckpoint.admit path interval .refused = none := rfl

/-- Empty unbounded input has no campaign plan, for every curriculum size. -/
theorem empty_unbounded_refused (size : Nat) (steps attempts : UInt64) :
    CampaignPlan.admit size ⟨steps, attempts, 0, 0⟩ =
      .error (if 0 < steps.toNat then .emptyUnbounded else .stepCapZero) := by
  by_cases h : 0 < steps.toNat <;> simp [CampaignPlan.admit, h]

/-- Positive survival-length and two-goal requests are actually admitted for
any curriculum containing two goals. Attempts and cycles need no extra premise. -/
theorem survival_plan_exists (size : Nat) (spec : CampaignSpec)
    (population : 2 ≤ size) (steps : 200 ≤ spec.steps.toNat)
    (goals : 2 ≤ spec.goals.toNat) :
    ∃ plan, CampaignPlan.admit size spec = .ok plan ∧
      200 ≤ plan.stepCap.toNat ∧ 2 ≤ plan.goals.val := by
  have positive : 0 < spec.steps.toNat := by omega
  have productive : spec.cycles.toNat ≠ 0 ∨ 0 < min spec.goals.toNat size := by
    right; omega
  simp only [CampaignPlan.admit, positive, ↓reduceDIte, productive]
  exact ⟨_, rfl, steps, by dsimp; omega⟩

/-- A nonempty admitted plan constructs its actual first cursor at goal zero. -/
theorem initial_cursor_exists {size : Nat} (plan : CampaignPlan size)
    (nonempty : 0 < plan.goals.val) :
    ∃ cursor, plan.initial = .continue cursor ∧ cursor.goal.val = 0 := by
  simp only [CampaignPlan.initial, nonempty, ↓reduceDIte]
  exact ⟨_, rfl, rfl⟩

/-- Achievement with another admitted goal advances the actual cursor,
regardless of attempts per goal. This is a boundary fact, not achievement existence. -/
theorem achieved_next_goal {size : Nat} {plan : CampaignPlan size}
    (cursor : CampaignCursor plan) (room : cursor.goal.val + 1 < plan.goals.val) :
    ∃ next, atAttemptBoundary cursor true false = .continue next ∧
      next.goal.val = cursor.goal.val + 1 ∧ next.attempt.val = 0 ∧ next.cycle = cursor.cycle := by
  simp only [atAttemptBoundary, Bool.false_eq_true, Bool.not_true, ↓reduceIte,
    atAttemptBoundary.nextGoal, room, ↓reduceDIte]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- Every standard native curriculum begins with survival, then wood collection;
seed and geometry do not select a repeated successful survival attempt. -/
theorem standard_first_goals (config : WorldConfig) (seed : UInt64) :
    (standardCurriculum config seed)[0]? = some (.survive 200, 0) ∧
      (standardCurriculum config seed)[1]? = some (.collect .wood 2, 0) := by
  exact ⟨rfl, rfl⟩

/-- An unfinished standard-world attempt admits its actual next observation
and owned decision input. Strict capacity follows from typed steps and the
executed finished predicate, rather than an assumed successful sensing guard. -/
theorem standard_sense_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    {α : Type} {goal : Goal} {cap : UInt64} (attempt : Attempt config α goal cap)
    (unfinished : attempt.finished = false) :
    ∃ input, attempt.sense = .ok (some input) ∧ input.before = attempt := by
  have room : attempt.steps.val < cap.toNat := by
    have bounded := attempt.steps.isLt
    have unequal : attempt.steps.val ≠ cap.toNat := by
      intro equal
      simp only [Attempt.finished, equal, beq_self_eq_true, Bool.true_or] at unfinished
      cases unfinished
    omega
  obtain ⟨observation, observed⟩ := CurrentWorld.standard_observe_success
    seed side config standard attempt.run.world
  refine ⟨⟨attempt, room, observation, observed⟩, ?_, rfl⟩
  simp only [Attempt.sense, unfinished, Bool.false_eq_true, ↓reduceIte, room, ↓reduceDIte]
  split
  · rename_i error failed
    rw [failed] at observed
    cases observed
  · rename_i actual sensed
    have same := Except.ok.inj (sensed.symm.trans observed)
    cases same
    rfl

/-- Starting any positive-cap attempt in a standard world admits its first
owned observation, including when the carried result ends the previous goal. -/
theorem standard_start_sense_success (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    {α : Type} (run : RunState config α) (goal : Goal) (cap : UInt64)
    (positive : 0 < cap.toNat) :
    ∃ input, (Attempt.start run goal cap).sense = .ok (some input) ∧
      input.before = Attempt.start run goal cap := by
  apply standard_sense_success seed side config standard
  have nonzero : cap.toNat ≠ 0 := by omega
  simp [Attempt.finished, Attempt.start, Ne.symm nonzero]

end AcornVerif.CurrentRunner
