/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Controls of the decision inventory

Written declarations that a name, a flag, a count of written binders or the presence of a
marker would decide wrongly. The ownership audit checks them through
`AcornDecisionInventory.controls`:

* no companion relationship removes the definition named like a matcher, the opaque constant,
  the unsafe definition or a field default that is a function;
* the theorem below a constructor counts as written;
* the handwritten comparison is not `derived`;
* neither field default that is a function is a stored value, the one behind a reducible
  definition included;
* a witness marker counts only as a closed fact at the top level of a condition, with a
  standard acceptance predicate, about the function that the condition binds.

They are read by that check and by nothing else.
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

/-- A written definition with the unsafe flag and no parent declaration. -/
unsafe def gate (count : Nat) : Bool := count == 0

/-- A function type behind a reducible definition. -/
abbrev Verdict := Nat → Bool

/-- A structure whose field default is a written predicate behind a reducible definition. -/
structure Veiled where
  /-- The predicate, with a default that the source writes. -/
  accepts : Verdict := id (α := Verdict) fun count => count == 0

/-- The marker of an accepted input, as each registry declares it. -/
def Accepts.{u} {ρ : Sort u} (accepts : ρ → Prop) (result : ρ) : Prop := accepts result

/-- A closed fact at the top level of a condition: it is counted. -/
def closedFact : (Nat → Bool) → Prop := fun test => True ∧ Accepts (· = true) (test 0)

/-- A marker below a hypothesis: it is not counted. -/
def hypothetical : (Nat → Bool) → Prop := fun test => False → Accepts (· = true) (test 0)

/-- A marker over a quantified input: it is not counted. -/
def quantified : (Nat → Bool) → Prop := fun test => ∀ count, Accepts (· = true) (test count)

/-- A marker with a predicate that every result satisfies: it is not counted. -/
def unconditional : (Nat → Bool) → Prop := fun test => Accepts (fun _ => True) (test 0)

/-- A marker about a function that the condition does not bind: it is not counted. -/
def foreign : (Nat → Bool) → Prop := fun _ => Accepts (· = true) (T.match_37 0)

end AcornDecisionInventory.Control
