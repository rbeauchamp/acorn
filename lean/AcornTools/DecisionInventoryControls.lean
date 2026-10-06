/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Controls of the decision inventory

Five written declarations that a name or a source range would take for compiler output.
The ownership audit checks, through `AcornDecisionInventory.controls`, that no generator
certificate removes the definition named like a matcher, the opaque constant or the field
default, that the theorem below a constructor counts as written, that the handwritten
comparison is not `derived`, and that the field default with an argument is not a stored
value. They are read by that check and by nothing else.
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

/-- A written opaque constant with an executable body. -/
opaque sealed (count : Nat) : Bool := count == 0

/-- A structure whose field default is a written predicate. -/
structure Guard where
  /-- The predicate, with a default that the source writes. -/
  accepts : Nat → Bool := fun count => count == 0

end AcornDecisionInventory.Control
