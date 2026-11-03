/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.Viewer

/-! # `acorn-viewer` executable

The root of the `acorn-viewer` executable: its `main` applies `NativeApp.Viewer.main`, which the
proof claim covers. Lean's compiler starts an executable at the top-level `main` of its root
module, and the claimed modules can hold only one such declaration, so this root, outside the
claim, holds that declaration and nothing else.
-/

/-- The `acorn-viewer` executable: `NativeApp.Viewer.main` on the command line. -/
def main (arguments : List String) : IO UInt32 :=
  NativeApp.Viewer.main arguments
