/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Ansi
import Acorn.Host.Baseline

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

end AcornVerif.CurrentRunner
