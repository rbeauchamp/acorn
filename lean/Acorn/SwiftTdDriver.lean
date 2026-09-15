/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.SwiftTd

/-!
# Native current-learner driver

A small command-line consumer of the admitted learner and its actual TD entry.
The tail-recursive traversal retains only the current learner. It does not
retain a trajectory, compare sampled answers with Rust, or measure learning
benefit. Its output is an execution observation, not a correctness oracle.
The learner's citations and mathematical/implementation boundaries are owned
by `Acorn.SwiftTd` and `AcornVerif.CurrentLearner`.
-/

namespace Acorn.SwiftTdDriver

/-- The driver's finite feature space; the learner itself remains generic
over every admitted dimension. -/
def dimension : Dimension := ⟨8, by decide, ⟨3, rfl⟩, by decide⟩

/-- One chosen control criterion for a native execution receipt. Both
criterion families remain available through the generic driver function. -/
def config : Config := ⟨.control, .differential⟩

/-- Consume a finite number of actual learner steps without retaining old
states. Feature construction uses the existing dimension-indexed hash admission. -/
def run {config : Config} {dimension : Dimension} :
    Nat → SwiftTd.Learner config dimension → SwiftTd.Learner config dimension
  | 0, learner => learner
  | count + 1, learner =>
    let idx := FeatIdx.fromHash dimension count.toUInt64
    let features : SwiftTd.ActiveSet dimension := ⟨[idx], by simp⟩
    run count (learner.apply (.step features Binary32.one))

/-- Initialize within a non-inlined generic call so the compiler cannot
hoist the complete initial learner into a permanently shared global snapshot. -/
@[noinline] def execute (config : Config) (dimension : Dimension) (steps : Nat) :
    SwiftTd.Learner config dimension := run steps (SwiftTd.Learner.initial config dimension)

end Acorn.SwiftTdDriver

/-- Run the current native learner for the requested nonnegative step count
(one by default), printing only integral observation encodings. -/
def main (arguments : List String) : IO UInt32 := do
  let count := match arguments with
    | [] => some 1
    | [word] => word.toNat?
    | _ => none
  match count with
  | none =>
    IO.eprintln "usage: swifttd-native [nonnegative-step-count]"
    return 2
  | some steps =>
    let learner := Acorn.SwiftTdDriver.execute
      Acorn.SwiftTdDriver.config Acorn.SwiftTdDriver.dimension steps
    let checksum := learner.val.stateChecksum
    IO.println s!"steps={steps} eligible={learner.val.eligibleCount} checksum={checksum}"
    return 0
