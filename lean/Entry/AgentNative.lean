/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.AgentDriver

/-! # `agent-native` executable

The root of the `agent-native` executable: its `main` applies `Acorn.AgentDriver.main`, which
the proof claim covers. Lean's compiler starts an executable at the top-level `main` of its root
module, and the claimed modules can hold only one such declaration, so this root, outside the
claim, holds that declaration and nothing else.
-/

/-- The `agent-native` executable: `Acorn.AgentDriver.main` on the command line. -/
def main (arguments : List String) : IO UInt32 :=
  Acorn.AgentDriver.main arguments
