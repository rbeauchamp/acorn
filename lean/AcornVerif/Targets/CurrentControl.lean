/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentControl

/-! # Targets of mission #197

Mission #197 landed before its statements were held as targets. Each target below is the
statement of one theorem that the mission names as its result, as that theorem stands in
`AcornVerif.CurrentControl`. The statement is not typed again here: `type_of%` takes the
type of the theorem Lean elaborated, so a target and its theorem cannot differ, and
`AcornVerif.landings` records the theorem as the target's proof.

Registering these statements after the mission landed was decided by the agent supervising
Acorn's research, on the owner's behalf; the owner has not confirmed them one by one.

Because a target here follows its theorem, the build does not notice a change to the theorem's
statement. The frame check does: `Landed.registered` in this directory pins each of these
targets, its theorem and the project's declarations their statement reads
(`lean/AcornTools/Frame.lean`).
-/

namespace AcornVerif.Targets.CurrentControl

/-- The statement of `AcornVerif.CurrentControl.candidates_of_gap`. -/
def candidates_of_gap : Prop :=
  type_of% @AcornVerif.CurrentControl.candidates_of_gap

/-- The statement of `AcornVerif.CurrentControl.candidates_of_resting`. -/
def candidates_of_resting : Prop :=
  type_of% @AcornVerif.CurrentControl.candidates_of_resting

end AcornVerif.Targets.CurrentControl
