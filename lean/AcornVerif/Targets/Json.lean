/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Json

/-! # Target of mission #163: `Json.parse` accepts every JSON text of its grammar

A *target* is a statement that a mission is to prove, held as a definition of type `Prop`. This
module holds the proposition of the contract of mission
[#163](https://github.com/rbeauchamp/acorn/issues/163), which concerns the executed parser
`Acorn.Json.parse` and the grammar `Acorn.Json.Grammar.Text`. The issue names no theorem;
`parse_complete` is the name given here, beside `Acorn.Json.parse_sound`. Nothing here is proved;
the mission is to prove the target. `AcornVerif.Targets.registry` lists it.

The contract's other part, the change of decision kinds in `lean/Acorn/Decisions.lean`, is not a
proposition and stays in the issue.
-/

namespace AcornVerif.Targets.Json
open Acorn Acorn.Json

/-- Completeness of the executed parser, the converse of `Acorn.Json.parse_sound`: `Json.parse`
accepts every text of the grammar, with the value of its derivation. -/
def parse_complete : Prop :=
  ∀ text v, Grammar.Text text.toList v → Json.parse text = .ok v

end AcornVerif.Targets.Json
