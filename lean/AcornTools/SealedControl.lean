/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-! # A sealed type for the controls of the ownership audit

The sealed-constant rule of `AcornTools.OwnershipAudit` gives each declaration that
reaches a constructor of a sealed type the modules of the sealed constants that it
references. A control of that rule needs such a declaration inside an owning module, and
no application module gets one. This module is the owner of types of its own and of the
definitions below that make a value of them. None has a constructor in its name, five
have a type that hides the sealed type from a reader of types, one reaches a constructor
through a second definition, and one references two sealed constants with different
modules. The rule reads no type. The audit adds this module and two of its types to the
rule's inputs for its control run only; nothing else uses them.
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

/-- A definition that nests the token's constructor in the constructor of the wrapper. It
references the constructor of the token, so it is a site. -/
def wrap (tag : Bool) (value : Nat) : Wrap tag := ⟨⟨value⟩⟩

/-- A definition that references no constructor: it calls `wrap`, so it is in the reach
through `wrap` and gets the modules of `wrap`. -/
def exposed (tag : Bool) (value : Nat) : Wrap tag := wrap tag value

/-- A third structure of this module, with a private constructor. It is not one of the
types that the control run names: only this module may reference its constructor. -/
structure Secret where
  private mk ::
  /-- The content; no control reads it. -/
  value : Nat

/-- A type with a public constructor that the control run names, with a row that also
permits the audit module. -/
structure Shared where
  /-- The content; no control reads it. -/
  value : Nat

/-- A definition that references two sealed constants with different modules: the
constructor of `Shared`, which the audit module may reference, and the constructor of
`Secret`, which it may not. -/
def bundle (value : Nat) : Secret × Shared := (⟨value⟩, ⟨value⟩)

end AcornSealedControl
