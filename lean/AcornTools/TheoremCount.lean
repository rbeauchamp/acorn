/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.Theorems

/-! # `theorem-count` executable

Command-line entry point that prints the scoped theorem counts of the compiled
project environments via `AcornTheoremCount.inventory`. It takes no arguments.
-/

/-- Print scoped theorem counts from the compiled project environments. -/
unsafe def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: theorem-count"
    return 1
  let counts ← AcornTheoremCount.inventory
  counts.report
  return 0
