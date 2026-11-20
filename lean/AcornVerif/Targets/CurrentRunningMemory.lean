/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentRunningMemory

/-! # Targets of mission #195

Mission #195 landed before its statements were held as targets. Each target below is the
statement of one theorem that the mission names as its result, as that theorem stands in
`AcornVerif.CurrentRunningMemory`. The statement is not typed again here: `type_of%` takes the
type of the theorem Lean elaborated, so a target and its theorem cannot differ, and
`AcornVerif.landings` records the theorem as the target's proof.

Registering these statements after the mission landed was decided by the agent supervising
Acorn's research, on the owner's behalf; the owner has not confirmed them one by one.

Because a target here follows its theorem, the build does not notice a change to the theorem's
statement. The frame check does: `Landed.registered` in this directory pins each of these
targets, its theorem and the project's declarations their statement reads
(`lean/AcornTools/Frame.lean`).
-/

namespace AcornVerif.Targets.CurrentRunningMemory

/-- The statement of `AcornVerif.CurrentRunningMemory.running_naturals_allowed`. -/
def running_naturals_allowed : Prop :=
  type_of% @AcornVerif.CurrentRunningMemory.running_naturals_allowed

/-- The statement of `AcornVerif.CurrentRunningMemory.running_snapshot_size`. -/
def running_snapshot_size : Prop :=
  type_of% @AcornVerif.CurrentRunningMemory.running_snapshot_size

/-- The statement of `AcornVerif.CurrentRunningMemory.running_memory_bits`. -/
def running_memory_bits : Prop :=
  type_of% @AcornVerif.CurrentRunningMemory.running_memory_bits

end AcornVerif.Targets.CurrentRunningMemory
