/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.BrowserKernel

/-! # Deterministic browser kernel emission for the native viewer resource host

`NativeApp.BrowserKernel.main` is the entry function of the `browser-kernel` executable, which its
root `Entry.BrowserKernel` applies. -/

/-- Emit exactly the source used by the native resource owner. -/
def _root_.NativeApp.BrowserKernel.main : IO Unit := do
  (← IO.getStdout).putStr Acorn.Host.Viewer.browserKernelJavascript
