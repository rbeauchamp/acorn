/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.WorldDriver

/-! # `world-native` executable

The root of the `world-native` executable: its `main` applies `Acorn.WorldDriver.main`, which
the proof claim covers. Lean's compiler starts an executable at the top-level `main` of its root
module, and the claimed modules can hold only one such declaration, so this root, outside the
claim, holds that declaration and nothing else.
-/

/-- The `world-native` executable: `Acorn.WorldDriver.main` on the command line. -/
def main (arguments : List String) : IO UInt32 :=
  Acorn.WorldDriver.main arguments
