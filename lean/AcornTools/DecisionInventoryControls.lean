/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

import Regula.Contract

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
  standard acceptance predicate, about the function that the condition binds, with an input
  that does not name that function and does not reach it through a definition;
* a kind counts only when it is stated about the function that the condition binds;
* a proof that every input is accepted states the fact at exactly the quantified inputs;
* a statement whose every claim is below a hypothesis about the function is `conditional`,
  and a statement in a structure that the audit does not read completely is not recognized.

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

/-- A marker whose input is built from the function that the condition binds: it is not
counted. -/
def selfBuilt : (Nat → Bool) → Prop :=
  fun test => Accepts (· = true) (test (if test 0 then 0 else 1))

/-- A kind about the function that the condition binds: it is a kind of that function. -/
def ownKind : (Nat → Bool) → Prop :=
  fun test => Regula.Decides (· = true) (fun count : Nat => count = 0) test

/-- A kind about another function: it is not a kind of the function that the condition
binds. -/
def foreignKind : (Nat → Bool) → Prop :=
  fun _ => Regula.Decides (· = true) (fun count : Nat => count = 0) T.match_37

/-- A claim below a hypothesis about the function that the condition binds: a function that
accepts nothing satisfies it. -/
def guarded : (Nat → Bool) → Prop := fun test => ∀ count, test count = true → count = 0

/-- An equivalence about the function that the condition binds. -/
def exact : (Nat → Bool) → Prop := fun test => ∀ count, test count = true ↔ count = 0

/-- A value that a definition builds from the written function `T.match_37`. -/
def chosen : Nat := if T.match_37 0 then 0 else 1

/-- A marker at an input that a definition builds from the decided function: its input
reaches that function, so it is not counted. -/
def viaDefinition : (Nat → Bool) → Prop := fun test => Accepts (· = true) (test chosen)

/-- A fact for every input of the function: it proves that no input is refused. -/
def everyAccepted : (Nat → Bool) → Prop := fun test => ∀ count, Accepts (· = true) (test count)

/-- A fact at one input below a quantifier: it is not a fact for every input. -/
def someAccepted : (Nat → Bool) → Prop := fun test => ∀ _count : Nat, Accepts (· = true) (test 0)

/-- A fact for every input that satisfies a hypothesis: it is not a fact for every input. -/
def guardedAccepted : (Nat → Bool) → Prop :=
  fun test => ∀ count, count = 0 → Accepts (· = true) (test count)

/-- An equivalence whose side is a conditional claim: its form is not recognized. -/
def veiled : (Nat → Bool) → Prop := fun test => (∀ count, test count = true → count = 0) ↔ True

/-- A conditional claim inside a disjunction: its form is not recognized. -/
def wrapped : (Nat → Bool) → Prop :=
  fun test => (∀ count, test count = true → count = 0) ∨ False

end AcornDecisionInventory.Control
