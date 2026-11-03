/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.Main

/-! # `acorn-core` executable

The root of the `acorn-core` executable: its `main` applies `NativeApp.Main.main`, which the
proof claim covers. Lean's compiler starts an executable at the top-level `main` of its root
module, and the claimed modules can hold only one such declaration, so this root, outside the
claim, holds that declaration and nothing else.
-/

/-- The `acorn-core` executable: `NativeApp.Main.main` on the command line. -/
def main (arguments : List String) : IO UInt32 :=
  NativeApp.Main.main arguments
