/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.BrowserKernel

/-! # `browser-kernel` executable

The root of the `browser-kernel` executable: its `main` applies `NativeApp.BrowserKernel.main`,
which the proof claim covers. Lean's compiler starts an executable at the top-level `main` of
its root module, and the claimed modules can hold only one such declaration, so this root,
outside the claim, holds that declaration and nothing else.
-/

/-- The `browser-kernel` executable: `NativeApp.BrowserKernel.main`. -/
def main : IO Unit :=
  NativeApp.BrowserKernel.main
