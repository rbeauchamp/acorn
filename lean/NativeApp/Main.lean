/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.Core

/-- Native admission and IO failures remain visible to the supervising process. -/
def main (arguments : List String) : IO UInt32 := do
  try NativeApp.runCore arguments
  catch error =>
    try IO.eprintln s!"acorn-core: {error}" catch _ => pure ()
    return 1
