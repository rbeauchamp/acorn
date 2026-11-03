/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# The host's unbounded loops

A host effect that runs until something outside the program happens, such as the end of a stream,
a stop request or a child's exit, iterates with `for _ in forever do`. The loop runs its body
until the body leaves it, by `break` or `return`, exactly as Lean's `repeat` does: `repeat` is
`for _ in Lean.Loop.mk do` (`Lean.Elab.BuiltinDo.Repeat` at Lean v4.35.0), and `Lean.Loop.forIn`
runs the body and recurses on `.yield` (`Init/While.lean`). The difference is the definition of
the iteration. Lean's goes through `repeatM`, whose computational core is a private `partial`
definition of the toolchain, so Regula's RG1006 refuses a claimed definition that mentions it.
Here each iteration is a `partial_fixpoint` definition, the least fixed point of the same
one-step unfolding (`forIn_io`, `forIn_baseIO`), which Lean's kernel checks, and Lean compiles
it from that same equation. Nothing here states that a loop ends: a body that never leaves runs
forever, as it would under `repeat`.

The iteration is defined for `IO` and `BaseIO`, the monads of the host's loops, rather than for
every monad with a `Lean.Order.MonadTail` instance: with the monad fixed, the compiler inlines its
bind, so the recursive call is a self tail call, which Lean's C emitter turns into a jump
(`isTailCall` and `emitTailCall`, `Lean/Compiler/LCNF/EmitC.lean:527-539` and `725-747` at
v4.35.0), and a loop that runs long does not grow the stack.
-/

namespace Acorn.Host

/-- What a host loop iterates over: one pass for each unit, with no end of its own. -/
structure Forever where

/-- The one value of `Forever`. -/
def forever : Forever := ⟨⟩

/-- Run `f` from `b` in `IO` until it returns `.done`, with each `.yield` value as the next
state. -/
def Forever.loopIO {β : Type} (f : Unit → β → IO (ForInStep β)) (b : β) : IO β := do
  match ← f () b with
  | .done b => pure b
  | .yield b => Forever.loopIO f b
partial_fixpoint

open Lean.Order in
/-- Run `f` from `b` in `BaseIO` until it returns `.done`, with each `.yield` value as the next
state. `BaseIO` has no bottom element at every result type, so the fixed point is taken in the
order that `Lean.Order.MonadTail` gives for an inhabited result, and its monotonicity is the
continuation's, as for `repeatM` (`Init/Internal/Order/While.lean`). -/
def Forever.loopBaseIO {β : Type} [Nonempty β] (f : Unit → β → BaseIO (ForInStep β)) (b : β) :
    BaseIO β := do
  match ← f () b with
  | .done b => pure b
  | .yield b => Forever.loopBaseIO f b
partial_fixpoint monotonicity fun _ _ recur _ =>
  MonadTail.bind_mono_right fun
    | .done _ => PartialOrder.rel_refl
    | .yield b => recur b

/-- `for _ in forever do` in `IO`. -/
instance : ForIn IO Forever Unit where
  forIn _ b f := Forever.loopIO f b

/-- `for _ in forever do` in `BaseIO`. -/
instance : ForIn BaseIO Forever Unit where
  forIn _ b f := haveI : Nonempty _ := ⟨b⟩; Forever.loopBaseIO f b

/-- A loop over `forever` in `IO` runs its body once and then stops with a `.done` value or runs
again from a `.yield` value: the one-step unfolding that `Lean.Loop.forIn_eq_of_monadTail`
states of `Lean.Loop.forIn`, the iteration of `repeat`. -/
theorem forIn_io {β : Type} (b : β) (f : Unit → β → IO (ForInStep β)) :
    forIn forever b f = (do
      match ← f () b with
      | .done val => pure val
      | .yield val => forIn forever val f) :=
  Forever.loopIO.eq_1 f b

/-- A loop over `forever` in `BaseIO` unfolds as `forIn_io` states for `IO`. -/
theorem forIn_baseIO {β : Type} (b : β) (f : Unit → β → BaseIO (ForInStep β)) :
    forIn forever b f = (do
      match ← f () b with
      | .done val => pure val
      | .yield val => forIn forever val f) :=
  haveI : Nonempty β := ⟨b⟩
  Forever.loopBaseIO.eq_1 f b

end Acorn.Host
