/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.ControlDriver

/-! # `control-native` executable

The root of the `control-native` executable: its `main` applies `Acorn.ControlDriver.main`,
which the proof claim covers. Lean's compiler starts an executable at the top-level `main` of
its root module, and the claimed modules can hold only one such declaration, so this root,
outside the claim, holds that declaration and nothing else.
-/

/-- The `control-native` executable: `Acorn.ControlDriver.main` on the command line. -/
def main (arguments : List String) : IO UInt32 :=
  Acorn.ControlDriver.main arguments
