/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-! # A sealed type for the controls of the ownership audit

The sealed-constant rule of `AcornTools.OwnershipAudit` seals each definition of an
owning module that references a sealed constant, unless it is an entry of the declared
interface. A control of that part needs such a definition inside an owning module, and
no application module gets one. This module is the owner of a sealed type of its own and
of six definitions that make a value of it. None has a constructor in its name, and five
have a type that hides the sealed type from a reader of types: a type variable with an
equality, a recursor on a list, abbreviations, a projection of an opaque constant, and a
value packed with its own type. The rule reads no type, so each is sealed by its
reference to the constructor. The audit adds this module and this type to the rule's
inputs for its control run only; nothing else uses them.
-/
namespace AcornSealedControl

/-- A sealed type of the controls: its values are made in this module only. -/
structure Token (tag : Bool) where
  private mk ::
  /-- The content; no control reads it. -/
  value : Nat

/-- A maker that is an instance: it gives a default value to a caller that holds no
token. -/
instance defaultToken (tag : Bool) : Inhabited (Token tag) := ⟨⟨0⟩⟩

/-- The sealed type behind one abbreviation. -/
abbrev Hidden (tag : Bool) : Type := Token tag

/-- The sealed type behind a second abbreviation. -/
abbrev HiddenTwice (tag : Bool) : Type := Hidden tag

/-- A maker whose result is a type variable that an equality identifies with the sealed
type. Its type does not name the sealed type as written, and its result is not
resolved. -/
def tokenByCast (tag : Bool) (target : Type) (same : HiddenTwice tag = target) : target :=
  cast same (⟨0⟩ : Token tag)

/-- A maker whose result type is a recursor on a list that holds the sealed type behind
abbreviations. The type reduces to the sealed type only with the actual list. -/
def tokenByRecursor (tag : Bool) :
    List.rec (motive := fun _ => Type) Nat (fun head _ _ => head) [HiddenTwice tag] :=
  (⟨0⟩ : Token tag)

/-- A maker whose result type is the sealed type behind abbreviations. -/
def tokenByAbbreviation (tag : Bool) : HiddenTwice tag := (⟨0⟩ : Token tag)

/-- An opaque constant that holds the sealed type behind abbreviations, with the proof
that it does. -/
opaque box (tag : Bool) : { carrier : Type // carrier = HiddenTwice tag } := ⟨HiddenTwice tag, rfl⟩

/-- A maker whose result type is a projection of an opaque constant. No reduction shows
the sealed type. -/
def tokenByOpaque (tag : Bool) : (box tag).val :=
  cast (box tag).property.symm (⟨0⟩ : Token tag)

/-- A maker whose result packs the value with its own type: the result type names no
sealed type. -/
def tokenByPack (tag : Bool) : (carrier : Type) × carrier := ⟨Token tag, ⟨0⟩⟩

/-- A second sealed structure of this module, which holds a token. It is not one of the
types that the control run names. -/
structure Wrap (tag : Bool) where
  private mk ::
  /-- The token inside. -/
  token : Token tag

/-- A definition that nests the token's constructor in the constructor of the wrapper. Its
body is an alias of the wrapper's constructor, so it is sealed for that reason too. -/
def wrap (tag : Bool) (value : Nat) : Wrap tag := ⟨⟨value⟩⟩

/-- A definition that references no constructor: it calls `wrap`. -/
def exposed (tag : Bool) (value : Nat) : Wrap tag := wrap tag value

end AcornSealedControl
