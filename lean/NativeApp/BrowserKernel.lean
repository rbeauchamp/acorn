/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.BrowserSchema

/-! # Deterministic browser kernel emission for the native viewer resource host -/

/-- Emit exactly the source used by the native resource owner. -/
def main : IO Unit := do
  (← IO.getStdout).putStr Acorn.Host.Viewer.browserKernelJavascript
