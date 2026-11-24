import Acorn.Demon
import Acorn.Handcrafted.Observation
import Acorn.Host.Terrain

namespace Acorn.Handcrafted
open Acorn.Features Acorn.Host

abbrev Cumulant := Fin Acorn.FeatureConstants.demonCount

instance : Provenance Cumulant where
  origin := some .cumulants

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

def cumulantOrder : List Cumulant := List.finRange Acorn.FeatureConstants.demonCount

def signalLayout : List Discount := cumulantOrder.tail.map demonDiscount

abbrev demonLayout : List Discount := .g99 :: signalLayout

theorem demonLayout_signals : demonLayout = cumulantOrder.map demonDiscount := rfl

def evaluateCumulants (signals : List Cumulant) (obs : Observation) (reward : Binary32) :
    Features.Cumulants (signals.map demonDiscount) :=
  match signals with
  | [] => .nil
  | signal :: rest => .cons (Provenance.origin (α := Cumulant))
      (signal.eval obs reward) (evaluateCumulants rest obs reward)

theorem Cumulant.indicator (signal : Cumulant) (obs : Observation) (reward : Binary32) :
    signal.eval obs reward = .zero ∨ signal.eval obs reward = .one := by
  have range (b : Bool) : Acorn.Handcrafted.indicator b = .zero ∨
      Acorn.Handcrafted.indicator b = .one := by
    cases b <;> simp [Acorn.Handcrafted.indicator]
  exact range _

def feedbackPredictions (cache : PredictionCache demonLayout) : Predictions :=
  ⟨cache.words, by
    rw [cache.length, demonLayout_signals]
    simp [cumulantOrder]⟩

theorem feedback_words (cache : PredictionCache demonLayout) :
    (feedbackPredictions cache).values = cache.words := rfl

end Acorn.Handcrafted
