/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-! # Shared retained study opportunity limits

These immutable protocol dimensions are shared by current explicit execution,
historical schemas and preserved-data reduction. This leaf has no evaluator.
-/
namespace AcornSpec

/-- `agent_baseline::STEPS_PER_ATTEMPT`. -/
def stepsPerAttempt : UInt64 := 4000
/-- `agent_baseline::ATTEMPTS_PER_GOAL`. -/
def attemptsPerGoal : Nat := 3
/-- `agent_baseline::CYCLES`. -/
def studyCycles : Nat := 3
/-- `agent_baseline::GOALS`. -/
def studyGoals : Nat := 13
/-- `agent_baseline::WORLD_SIDE`. -/
def studyWorldSide : Int := 1024

end AcornSpec
