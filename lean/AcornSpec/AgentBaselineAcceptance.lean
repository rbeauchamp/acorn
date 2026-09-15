/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.IntraOptionCredit

/-!
# Executable baseline acceptance adapter

The baseline report exposes seven named conjuncts as well as their conjunction.
This core-only adapter makes the conjunction depend on those same flags. The
proof-layer bridge in `AcornVerif.AgentBaselineSemantics` binds the flags to
`AcornVerif.AgentBaselineAcceptance` and its model thresholds without
linking the proof library into the native analysis calculator.
-/

namespace AcornSpec

/-- The seven conjuncts exposed by the registered baseline report. -/
structure BaselineAcceptance where
  /-- Final versus random reaches the point-probability threshold. -/
  controlRandom : Bool
  /-- Final versus random exceeds the interval threshold. -/
  controlRandomInterval : Bool
  /-- Final versus frozen reaches the point-probability threshold. -/
  learningFrozen : Bool
  /-- Final versus frozen exceeds the interval threshold. -/
  learningFrozenInterval : Bool
  /-- Pooled Reach success reaches the registered minimum. -/
  reachSuccess : Bool
  /-- The lower bound on random-minus-final Reach time is positive. -/
  reachTime : Bool
  /-- The lower bound on later-minus-first efficiency is positive. -/
  continualImprovement : Bool

/-- The verdict is the conjunction of exactly the seven reported flags. -/
def BaselineAcceptance.all (flags : BaselineAcceptance) : Bool :=
  flags.controlRandom && flags.controlRandomInterval &&
    flags.learningFrozen && flags.learningFrozenInterval &&
    flags.reachSuccess && flags.reachTime && flags.continualImprovement

/-- The registered baseline acceptance conditions. The paired thresholds are
shared with the later studies; the baseline additionally thresholds Reach
success at 3/5 and both effect lower bounds strictly above zero. -/
def baselineAcceptance (r : Result7) : BaselineAcceptance :=
  { controlRandom := decide (poiThreshold ≤ r.randomPoi)
    controlRandomInterval := decide (probLowerThreshold < r.randomProbLower)
    learningFrozen := decide (poiThreshold ≤ r.frozenPoi)
    learningFrozenInterval := decide (probLowerThreshold < r.frozenProbLower)
    reachSuccess := decide ((3 / 5 : Rat) ≤ r.reachSuccess)
    reachTime := decide (0 < r.reachTimeLower)
    continualImprovement := decide (0 < r.continualLower) }

end AcornSpec
