/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-! # A sealed type for the controls of the ownership audit

The sealed-constant rule of `AcornTools.OwnershipAudit` finds a maker of a sealed type by
its type, in the modules that own the type. A control of that part needs a maker inside
an owning module, and no application module gets one. This module is the owner of a
sealed type of its own, with one maker whose name has no constructor in it. The audit
adds this module and this type to the rule's inputs for its control run only; nothing
else uses them.
-/
namespace AcornSealedControl

/-- A sealed type of the controls: its values are made in this module only. -/
structure Token (tag : Bool) where
  private mk ::
  /-- The content; no control reads it. -/
  value : Nat

/-- A maker of the control type that is not a constructor and not a constructor alias: an
instance that gives a default value to a caller that holds no token. -/
instance defaultToken (tag : Bool) : Inhabited (Token tag) := ⟨⟨0⟩⟩

end AcornSealedControl
