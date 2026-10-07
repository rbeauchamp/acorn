/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-! # A sealed type for the controls of the ownership audit

The sealed-constant rule of `AcornTools.OwnershipAudit` seals each definition of an
owning module that references a sealed constant, unless its type is proved free of every
sealed type. A control of that part needs such a definition inside an owning module, and
no application module gets one. This module is the owner of a sealed type of its own and
of four definitions that make a value of it. None has a constructor in its name, and
three have a type that hides the sealed type. The audit adds this module and this type to
the rule's inputs for its control run only; nothing else uses them.
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

end AcornSealedControl
