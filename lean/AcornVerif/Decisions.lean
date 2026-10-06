/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Regula.Contract
import AcornVerif.CurrentCertificates
import AcornVerif.CurrentCheckpoint

/-!
# Decision contracts proved in the proof library

`Acorn.Decisions` registers the decisions of the executing library whose contracts follow
from Lean core alone. A contract here states a direction whose proof needs this library. The
legality of every stored lifetime total rests on the real-valued bounds of
`CurrentLifetime.stored_sum_legal`. What an accepted certificate establishes is a statement
about runs of the executed world step, proved in `CurrentCertificates`.

No certificate checker is complete: each contract below states what an accepted certificate
establishes, and a refused certificate establishes nothing. The blocked checker is a function
between fixed types and carries the sound kind. The replay and stance checkers take an
argument whose type depends on the configuration, so their statements are ordinary
requirements with no kind.

Regula counts only a contract of the function's own library toward a decision registration,
so the functions below carry no registration. The ownership audit requires each contract by
name instead, with a statement that still refers to the executing definition.
-/

namespace AcornVerif.Decisions
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime

/-- Total admission accepts the words of every stored total of the receiving quantity and
returns that total (`CurrentCheckpoint.sum_roundtrip`). The result type depends on the
quantity, so the contract is an ordinary requirement with no kind.

**Not claimed:** that every accepted word pair is the word image of a stored total. -/
theorem sum_admit : Regula.ExecutableContract admitSum (fun admit =>
    ∀ (quantity : Quantity) (record : SumCount quantity),
      admit quantity (sumWords record) = some record) :=
  ⟨fun _ => CurrentCheckpoint.sum_roundtrip⟩

/-- An image whose overall reward total is a NaN word, with every other field zero. -/
def refusedLifetime : LifetimeWords :=
  ⟨(0, ⟨0x7ff8000000000000⟩), .replicate _ (0, ⟨0⟩), .replicate _ (0, ⟨0⟩),
    .replicate _ (0, ⟨0⟩), .replicate _ .zero, .replicate _ .zero, .replicate _ (0, ⟨0⟩),
    .replicate _ .initial, .replicate _ (0, 0, 0), .replicate _ (.replicate _ (0, 0, 0))⟩

/-- Lifetime admission accepts every word image of a durable lifetime record whose option
counters are valid with no active option (`CurrentCheckpoint.lifetime_roundtrip`), and it
refuses an image whose overall reward total is a NaN word.

**Not claimed:** that every accepted image is the word image of such a record. -/
theorem lifetime_admit : Regula.ExecutableContract admitLifetime
    (Regula.DecidesCompletely (·.isSome = true) (fun raw =>
      ∃ record : Durable demonLayout, OptionsValid record.options none ∧
        raw = lifetimeWords record)) :=
  ⟨{ complete := fun raw ⟨record, valid, written⟩ => by
       rw [written, CurrentCheckpoint.lifetime_roundtrip record valid]
       rfl
     refused := ⟨refusedLifetime, by
       have illegal : ¬LegalSum .reward 0 ⟨0x7ff8000000000000⟩ := by decide
       simp [admitLifetime, admitSum, SumCount.admit, refusedLifetime, illegal]⟩ }⟩

/-! ## Certificate checkers -/

/-- The replay checker accepts only an action list that shows its goal feasible from its
world within its cap (`CurrentCertificates.replay_feasible`): some run of at least one and at
most `cap` executed steps, from the world with the goal installed, ends in a world that
satisfies the goal. The world's type depends on the configuration, so the contract is an
ordinary requirement with no kind.

**Not claimed:** completeness. The checker refuses an action list that does not itself reach
the goal, whether or not the goal is feasible. -/
theorem replay_certified : Regula.ExecutableContract @Host.replayCertified (fun check =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (goal : Host.Goal) (cap : Nat)
      (actions : List Host.Action),
      @check config world goal cap actions = true →
        CurrentCertificates.Feasible world goal cap) :=
  ⟨fun _ _ _ _ _ => CurrentCertificates.replay_feasible⟩

/-- The goal box of a target is unreachable from a start tile: after any run of steps and goal
installations from a world whose body is on the start tile, the body is outside the goal box.
With `boat` false the statement covers only the runs that end without a boat. -/
def Unreachable (config : Host.WorldConfig) (boat : Bool) (target start : Host.Position) :
    Prop :=
  ∀ world final : Host.World config, world.body.position.position = start →
    CurrentGoals.Later world final → (boat = false → final.body.inventory.boat = false) →
      ¬CurrentGoals.InGoalBox target final.body.position.position

/-- The blocked checker accepts only a region that shows the goal box of its target
unreachable from its start tile (`CurrentCertificates.blocked_outside`), and it accepts the
empty region for a goal box that lies outside the box of the world.

**Not claimed:** completeness. The checker refuses every region that is not closed, whether or
not the goal box is reachable. -/
theorem region_blocked : Regula.ExecutableContract Host.regionBlocked (fun check =>
    Regula.DecidesSoundly (· = true)
      (fun input :
          (((Host.WorldConfig × Bool) × Host.Position) × List Host.Position) × Host.Position =>
        Unreachable input.1.1.1.1 input.1.1.1.2 input.1.1.2 input.2)
      (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry check))))) :=
  ⟨{ sound := fun input accepted world final located later boatless =>
       CurrentCertificates.blocked_outside (cells := input.1.2)
         (by rw [located]; exact accepted) later boatless
     accepted := ⟨((((⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩, true),
       ⟨⟨100, by decide⟩, ⟨100, by decide⟩⟩), []), ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩),
       by decide⟩ }⟩

/-- The stance checker accepts only a stance from which, in every world, a paid harvest
yields the item (`CurrentCertificates.stance_harvest`), which a paid move from the tile behind
it enters facing the resource (`stance_enter`), and whose tile behind is in the box and
walkable (`stance_approach`). A wood stance needs its tree standing. The stance's type depends
on the configuration, so the contract is an ordinary requirement with no kind.

**Not claimed:** completeness, or that a step succeeds: a successful step is a hypothesis. -/
theorem stance_certified : Regula.ExecutableContract Host.stanceCertified (fun check =>
    ∀ (config : Host.WorldConfig) (stance : Host.BoxPosition config)
      (direction : Host.Direction) (item : Host.Item),
      check config stance direction item = true →
        (∀ (world next : Host.World config) (events : Host.StepResult),
          world.body.position = stance → world.body.facing = direction →
          (item = .wood → world.tileKind (stance.facingPosition direction) = .ok .tree) →
          world.step .harvest = .ok (next, events) → events.exhausted = false →
            events.harvested = some item ∧
              next.body.inventory = world.body.inventory.add item
                (if item == .wood && world.body.inventory.axe then 3 else 1)) ∧
        (∀ (world next : Host.World config) (action : Host.Action) (events : Host.StepResult),
          action.direction = some direction →
          world.body.position.position.translate direction.delta.1 direction.delta.2 =
            some stance.position →
          world.step action = .ok (next, events) → events.exhausted = false →
            next.body.position = stance ∧ next.body.facing = direction) ∧
        ∃ approach : Host.BoxPosition config,
          approach.position.translate direction.delta.1 direction.delta.2 =
            some stance.position ∧ Host.walkableTile config approach.position = true) :=
  ⟨fun _ _ _ _ accepted =>
    ⟨CurrentCertificates.stance_harvest accepted, CurrentCertificates.stance_enter accepted,
      CurrentCertificates.stance_approach accepted⟩⟩

/-- The walkable test accepts only a tile that is enterable in every world of the
configuration, with or without a boat (`CurrentCertificates.walkable_enterable`).

The function is between fixed types, but the sound kind carries an input the function
accepts, which is the generated terrain of one tile, and no theorem states the terrain of a
tile. The statement is therefore an ordinary requirement with no kind.

**Not claimed:** completeness. The test refuses water, which a body with a boat enters. -/
theorem terrain_walkable : Regula.ExecutableContract Host.walkableTile (fun test =>
    ∀ (config : Host.WorldConfig) (tile : Host.Position), test config tile = true →
      ∀ world : Host.World config, world.enterable tile = .ok true) :=
  ⟨fun _ tile accepted world => CurrentCertificates.walkable_enterable world tile accepted⟩

end AcornVerif.Decisions
