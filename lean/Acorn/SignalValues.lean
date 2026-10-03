/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Provenance
import Acorn.State

/-!
# One signal value per declared question

A frame's prediction signals are evaluated once and read by every learner that asks
about them: the on-policy demons of `Acorn.Demon` and each option's off-policy
questions of `Acorn.OffPolicy`. The list of discounts in the type is the layout of
the bank that consumes the values, so a value cannot reach a question with another
horizon.
-/
namespace Acorn.Features

/-- A bank input has exactly one raw cumulant per immutable discount slot. -/
inductive Cumulants : List Discount → Type where
  /-- Empty tail. -/
  | nil : Cumulants []
  /-- One raw signal value with its mandatory declared origin, in channel order. -/
  | cons {discount : Discount} {rest : List Discount} (origin : Option Departure)
      (value : Binary32) (tail : Cumulants rest) : Cumulants (discount :: rest)

end Acorn.Features
