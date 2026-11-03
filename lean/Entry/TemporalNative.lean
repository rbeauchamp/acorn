/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.TemporalDriver

/-! # `temporal-native` executable

The root of the `temporal-native` executable: its `main` applies `Acorn.TemporalDriver.main`,
which the proof claim covers. Lean's compiler starts an executable at the top-level `main` of
its root module, and the claimed modules can hold only one such declaration, so this root,
outside the claim, holds that declaration and nothing else.
-/

/-- The `temporal-native` executable: `Acorn.TemporalDriver.main` on the command line. -/
def main (arguments : List String) : IO UInt32 :=
  Acorn.TemporalDriver.main arguments
