/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.Boundary.Audit

/-! # Native source/compiled admission entry -/

/-- Initializer access belongs only to this reviewed verification boundary. -/
unsafe def main (args : List String) : IO UInt32 :=
  AcornBoundaryAudit.command args
