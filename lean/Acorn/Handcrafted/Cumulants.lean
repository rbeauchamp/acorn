/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Demon
import Acorn.Handcrafted.Observation
import Acorn.Host.Terrain

/-!
# D5 prediction questions

The eleven current host signals retain their canonical order, raw sensory-byte
semantics and per-signal horizons. The target family declares D5; its reward
member observes the host-declared goal reward. This is the PAR-3 specialization
of Sutton, Modayil et al., *Horde*, AAMAS (2011), pp. 761–768, p. 764, not
learned question discovery or general off-policy prediction.
-/
namespace Acorn.Handcrafted
open Acorn.Features Acorn.Host

/-- The closed current signal set in canonical order. -/
abbrev Cumulant := Fin Acorn.FeatureConstants.demonCount

instance : Provenance Cumulant where
  origin := some .cumulants

/-- Boolean host predicates become the exact binary32 indicator words. -/
def indicator (value : Bool) : Binary32 := if value then .one else .zero

/-- One canonical signal, evaluated once; malformed sensory bytes stay raw. -/
def Cumulant.eval (signal : Cumulant) (obs : Observation) (reward : Binary32) : Binary32 :=
  indicator <| match signal.val with
  | 0 => Binary32.zero.less reward
  | 1 => obs.tiles.any (fun row => row.any (fun tile => tile.kind == TileKind.tree.code))
  | 2 => obs.tiles.any (fun row => row.any (fun tile => tile.kind == TileKind.stone.code))
  | 3 => obs.tiles.any (fun row => row.any (fun tile => tile.kind == TileKind.ore.code))
  | 4 => obs.tiles.any (fun row => row.any (fun tile => tile.kind == TileKind.water.code))
  | 5 => obs.tiles.any (fun row => row.any (fun tile => tile.food != 0))
  | 6 => obs.energy ≤ 3
  | 7 => obs.day ≥ 4
  | 8 => obs.inventory.wood ≥ 1
  | 9 => obs.inventory.stone ≥ 1
  | _ => obs.inventory.axe

instance : Signal Cumulant Observation Binary32 where
  discount := demonDiscount
  eval := Cumulant.eval

/-- Semantic names in canonical order, matching telemetry's current interface. -/
def Cumulant.name (signal : Cumulant) : String :=
  match signal.val with
  | 0 => "goal_reward"
  | 1 => "near_tree"
  | 2 => "near_stone"
  | 3 => "near_ore"
  | 4 => "near_water"
  | 5 => "near_food"
  | 6 => "energy_low"
  | 7 => "night"
  | 8 => "has_wood"
  | 9 => "has_stone"
  | _ => "has_axe"

/-- All signal identities are enumerated from their closed finite domain. -/
def cumulantOrder : List Cumulant := List.finRange Acorn.FeatureConstants.demonCount

/-- Horizon layout is derived from the same identities used to evaluate signals. -/
def demonLayout : List Discount := cumulantOrder.map demonDiscount

/-- Evaluate an arbitrary ordered signal family without losing its horizon indices. -/
def evaluateCumulants (signals : List Cumulant) (obs : Observation) (reward : Binary32) :
    Features.Cumulants (signals.map demonDiscount) :=
  match signals with
  | [] => .nil
  | signal :: rest => .cons (Provenance.origin (α := Cumulant))
      (signal.eval obs reward) (evaluateCumulants rest obs reward)

/-- Every current signal returns exactly an indicator, across all raw observations. -/
theorem Cumulant.indicator (signal : Cumulant) (obs : Observation) (reward : Binary32) :
    signal.eval obs reward = .zero ∨ signal.eval obs reward = .one := by
  have range (b : Bool) : Acorn.Handcrafted.indicator b = .zero ∨
      Acorn.Handcrafted.indicator b = .one := by
    cases b <;> simp [Acorn.Handcrafted.indicator]
  exact range _

/-- The prediction encoder's complete input derives from the typed feedback cache. -/
def feedbackPredictions (cache : PredictionCache demonLayout) : Predictions :=
  ⟨cache.words, by rw [cache.length]; simp [demonLayout, cumulantOrder]⟩

/-- Encoding receives the original temporal prediction words without recomputation. -/
theorem feedback_words (cache : PredictionCache demonLayout) :
    (feedbackPredictions cache).values = cache.words := rfl

end Acorn.Handcrafted
