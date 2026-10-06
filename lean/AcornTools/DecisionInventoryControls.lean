/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Controls of the decision inventory

Three written declarations that a name pattern would take for compiler output. The
ownership audit checks, through `AcornDecisionInventory.controls`, that the inventory keeps
the first in its domain, counts the second as a written theorem and refuses the reason
`derived` for the third. They are read by that check and by nothing else.
-/
namespace AcornDecisionInventory.Control

/-- A type with two constructors. -/
inductive T where
  /-- The first value. -/
  | a
  /-- The second value. -/
  | b

/-- A written definition whose name is `match_` followed by digits. -/
def T.match_37 : Nat → Bool := fun count => count == 0

/-- A written theorem below a constructor. -/
theorem T.a.refused : T.match_37 1 = false := rfl

/-- A handwritten comparison with the name of a derived one. -/
def instBEqT.beq : T → T → Bool := fun _ _ => true

/-- A declared instance of the handwritten comparison. -/
instance instBEqT : BEq T := ⟨instBEqT.beq⟩

end AcornDecisionInventory.Control
