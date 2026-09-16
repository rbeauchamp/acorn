/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.Theorems

/-- Print scoped theorem counts from the compiled project environments. -/
unsafe def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: theorem-count"
    return 1
  let counts ← AcornTheoremCount.inventory
  counts.report
  return 0
