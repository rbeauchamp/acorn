namespace Acorn.Host

structure Forever where

def forever : Forever := ⟨⟩

def Forever.loopIO {β : Type} (f : Unit → β → IO (ForInStep β)) (b : β) : IO β := do
  match ← f () b with
  | .done b => pure b
  | .yield b => Forever.loopIO f b
partial_fixpoint

open Lean.Order in
def Forever.loopBaseIO {β : Type} [Nonempty β] (f : Unit → β → BaseIO (ForInStep β)) (b : β) :
    BaseIO β := do
  match ← f () b with
  | .done b => pure b
  | .yield b => Forever.loopBaseIO f b
partial_fixpoint monotonicity fun _ _ recur _ =>
  MonadTail.bind_mono_right fun
    | .done _ => PartialOrder.rel_refl
    | .yield b => recur b

instance : ForIn IO Forever Unit where
  forIn _ b f := Forever.loopIO f b

instance : ForIn BaseIO Forever Unit where
  forIn _ b f := haveI : Nonempty _ := ⟨b⟩; Forever.loopBaseIO f b

theorem forIn_io {β : Type} (b : β) (f : Unit → β → IO (ForInStep β)) :
    forIn forever b f = (do
      match ← f () b with
      | .done val => pure val
      | .yield val => forIn forever val f) :=
  Forever.loopIO.eq_1 f b

theorem forIn_baseIO {β : Type} (b : β) (f : Unit → β → BaseIO (ForInStep β)) :
    forIn forever b f = (do
      match ← f () b with
      | .done val => pure val
      | .yield val => forIn forever val f) :=
  haveI : Nonempty β := ⟨b⟩
  Forever.loopBaseIO.eq_1 f b

end Acorn.Host
