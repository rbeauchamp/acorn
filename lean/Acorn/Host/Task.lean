/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Terrain

/-! # Current action, inventory, energy and task transitions -/
namespace Acorn.Host

/-- Cardinal movement direction. -/
inductive Direction where
  /-- Negative y. -/
  | north
  /-- Positive y. -/
  | south
  /-- Positive x. -/
  | east
  /-- Negative x. -/
  | west
  deriving DecidableEq, BEq

/-- The signed displacement of one movement. -/
def Direction.delta : Direction → Int × Int
  | .north => (0, -1) | .south => (0, 1) | .east => (1, 0) | .west => (-1, 0)

/-- Canonical direction order used by placement and wandering. -/
def Direction.fromIndex (index : Fin 4) : Direction :=
  match index.val with | 0 => .north | 1 => .south | 2 => .east | _ => .west

/-- The complete primitive-action domain. -/
inductive Action where
  /-- North movement. -/
  | north
  /-- South movement. -/
  | south
  /-- East movement. -/
  | east
  /-- West movement. -/
  | west
  /-- Wait. -/
  | wait
  /-- Harvest the facing tile. -/
  | harvest
  /-- Attempt to craft an axe. -/
  | craftAxe
  /-- Attempt to craft a boat. -/
  | craftBoat
  /-- Eat one food item. -/
  | eat
  deriving DecidableEq, BEq

/-- Stable action code for audit and agent composition. -/
def Action.index : Action → Fin 9
  | .north => 0 | .south => 1 | .east => 2 | .west => 3 | .wait => 4
  | .harvest => 5 | .craftAxe => 6 | .craftBoat => 7 | .eat => 8

/-- Legacy world action conversion retains the eat fallback for any other index. -/
def Action.fromIndex (index : Nat) : Action :=
  match index with
  | 0 => .north | 1 => .south | 2 => .east | 3 => .west | 4 => .wait
  | 5 => .harvest | 6 => .craftAxe | 7 => .craftBoat | _ => .eat

/-- Every primitive survives the actual world code round trip. -/
theorem Action.index_roundtrip (action : Action) : fromIndex action.index.val = action := by
  cases action <;> rfl

/-- Movement capability, with no direction for a nonmovement action. -/
def Action.direction : Action → Option Direction
  | .north => some .north | .south => some .south
  | .east => some .east | .west => some .west
  | .wait | .harvest | .craftAxe | .craftBoat | .eat => none

/-- Recipe requirements in wood and stone units. -/
def Craftable.recipe : Craftable → Nat × Nat
  | .axe => (FeatureConstants.axeWood, FeatureConstants.axeStone)
  | .boat => (FeatureConstants.boatWood, FeatureConstants.boatStone)

/-- Count of the specified inventory item. -/
def Inventory.count (inventory : Inventory) : Item → UInt32
  | .wood => inventory.wood | .stone => inventory.stone
  | .food => inventory.food | .gold => inventory.gold

/-- Saturating unsigned item addition for every public count and amount. -/
def Inventory.add (inventory : Inventory) (item : Item) (amount : UInt32) : Inventory :=
  let total := (min (2 ^ 32 - 1) ((inventory.count item).toNat + amount.toNat)).toUInt32
  match item with
  | .wood => { inventory with wood := total } | .stone => { inventory with stone := total }
  | .food => { inventory with food := total } | .gold => { inventory with gold := total }

/-- Whether a tool is already owned. -/
def Inventory.owns (inventory : Inventory) : Craftable → Bool
  | .axe => inventory.axe | .boat => inventory.boat

/-- Refusal records preserve the existing ordered recipe checks. -/
inductive CraftError where
  /-- The requested tool is already in the inventory. -/
  | alreadyOwned
  /-- Wood admission failed. -/
  | notEnoughWood (available required : Nat)
  /-- Stone admission failed after wood admission succeeded. -/
  | notEnoughStone (available required : Nat)
  deriving DecidableEq

/-- Transactional crafting: material subtraction occurs only after all checks. -/
def Inventory.craft (inventory : Inventory) (tool : Craftable) : Except CraftError Inventory :=
  let (wood, stone) := tool.recipe
  if inventory.owns tool then .error .alreadyOwned
  else if inventory.wood.toNat < wood then .error (.notEnoughWood inventory.wood.toNat wood)
  else if inventory.stone.toNat < stone then .error (.notEnoughStone inventory.stone.toNat stone)
  else
    let paid : Inventory := { inventory with
      wood := (inventory.wood.toNat - wood).toUInt32
      stone := (inventory.stone.toNat - stone).toUInt32 }
    .ok (match tool with | .axe => { paid with axe := true } | .boat => { paid with boat := true })

/-- Every successful craft consumes exactly its recipe and owns the requested tool. -/
theorem Inventory.craft_exact (inventory next : Inventory) (tool : Craftable)
    (h : inventory.craft tool = .ok next) :
    next.wood.toNat + tool.recipe.1 = inventory.wood.toNat ∧
    next.stone.toNat + tool.recipe.2 = inventory.stone.toNat ∧ next.owns tool = true := by
  rcases hr : tool.recipe with ⟨wood, stone⟩
  by_cases ho : inventory.owns tool = true
  · simp [craft, ho] at h
  · by_cases hw : inventory.wood.toNat < wood
    · simp [craft, hr, ho, hw] at h
    · by_cases hs : inventory.stone.toNat < stone
      · simp [craft, hr, ho, hw, hs] at h
      · have hwb := inventory.wood.toNat_lt
        have hsb := inventory.stone.toNat_lt
        simp only [craft, hr, ho, hw, hs, ↓reduceIte] at h
        cases tool <;> cases Except.ok.inj h <;>
          simp only [owns, Craftable.recipe] at *
        all_goals
          simp only [Prod.mk.injEq] at hr
          simp only [Nat.toUInt32]
          rw [UInt32.toNat_ofNat_of_lt' (n := inventory.wood.toNat - wood)
            (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hwb),
            UInt32.toNat_ofNat_of_lt' (n := inventory.stone.toNat - stone)
            (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hsb)]
          exact ⟨Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), trivial⟩

/-- Stored energy carries the closed physical range at every write. -/
abbrev Energy := Fin (FeatureConstants.energyMax + 1)

/-- The complete set of energy inflows. -/
inductive EnergyGain where
  /-- Recovery when an action cannot be paid. -/
  | rest
  /-- Consumption of a food item. -/
  | eat

/-- The closed gain table in tenths of an energy unit. -/
def EnergyGain.amount : EnergyGain → Nat
  | .rest => FeatureConstants.energyRestRecover | .eat => FeatureConstants.energyEatRestore

/-- Saturating energy construction. -/
def Energy.new (units : Nat) : Energy := ⟨min units FeatureConstants.energyMax, by omega⟩

/-- A legal energy write cannot exceed the physical capacity. -/
def Energy.gain (energy : Energy) (source : EnergyGain) : Energy :=
  Energy.new (energy.val + source.amount)

/-- Spending returns an explicit refusal, without changing an insufficient balance. -/
def Energy.spend (energy : Energy) (cost : Nat) : Option Energy :=
  if cost ≤ energy.val then some ⟨energy.val - cost, by have := energy.isLt; omega⟩ else none

/-- Successful spending conserves the exact integer balance. -/
theorem Energy.spend_balance (energy next : Energy) (cost : Nat)
    (h : energy.spend cost = some next) : next.val + cost = energy.val := by
  unfold spend at h
  split at h
  · cases Option.some.inj h
    simp only
    omega
  · contradiction

/-- The ordinary world derives its multiplier from the closed day/night state. -/
def Action.energyCost (action : Action) (night : Bool) : Nat :=
  (if action == .harvest then FeatureConstants.harvestCost else 1) *
    (if night then FeatureConstants.nightMultiplier else FeatureConstants.dayMultiplier)

/-- Raw public multipliers preserve every representable product and refuse overflow. -/
def Action.rawEnergyCost (action : Action) (multiplier : UInt32) : Option UInt32 :=
  let cost := (if action == .harvest then FeatureConstants.harvestCost else 1) * multiplier.toNat
  if cost < 2 ^ 32 then some cost.toUInt32 else none

/-- Successful raw cost admission preserves the exact natural-number product. -/
theorem Action.rawEnergyCost_exact (action : Action) (multiplier result : UInt32)
    (h : action.rawEnergyCost multiplier = some result) :
    result.toNat = (if action == .harvest then FeatureConstants.harvestCost else 1) * multiplier.toNat := by
  unfold rawEnergyCost at h
  dsimp only at h
  generalize hc : (if action == .harvest then FeatureConstants.harvestCost else 1) * multiplier.toNat = cost at h ⊢
  split at h
  · cases Option.some.inj h
    exact Nat.mod_eq_of_lt (by assumption)
  · contradiction

/-- Every action has a positive cost affordable after one passive rest. -/
theorem Action.cost_bounds (action : Action) (night : Bool) :
    1 ≤ action.energyCost night ∧ action.energyCost night ≤ EnergyGain.rest.amount := by
  cases action <;> cases night <;> decide

/-- Closed task family used by curriculum and lifetime accounting. -/
inductive GoalFamily where
  /-- Coordinate attainment. -/
  | reach
  /-- Inventory count. -/
  | collect
  /-- Tool possession. -/
  | craft
  /-- Fixed duration. -/
  | survive
  deriving DecidableEq

/-- Public goal arguments retain every signed coordinate and unsigned quantity. -/
inductive Goal where
  /-- Reach a coordinate region. -/
  | reach (target : Position)
  /-- Collect at least the requested quantity. -/
  | collect (item : Item) (count : UInt32)
  /-- Own the requested tool. -/
  | craft (tool : Craftable)
  /-- Survive the requested duration since goal installation. -/
  | survive (steps : UInt64)

/-- A goal's family is derived from its constructor. -/
def Goal.family : Goal → GoalFamily
  | .reach _ => .reach | .collect _ _ => .collect | .craft _ => .craft | .survive _ => .survive

/-- Stable opaque cue, derived from the entire goal identity. -/
def Goal.cue : Goal → UInt64
  | .reach target => Rng.hash3 1 (coordinateWord target.x) (coordinateWord target.y)
  | .collect item count => Rng.hash3 2 item.code count.toUInt64
  | .craft tool => Rng.hash3 3 tool.code 0
  | .survive steps => Rng.hash3 4 steps 0

/-- World reward and task error read this same completion predicate. -/
def TaskObservation.satisfied : TaskObservation → Bool
  | .none => false
  | .reach _ relation => relation.distance == 0
  | .collect _ _ remaining => remaining == 0
  | .craft _ _ remaining => !remaining
  | .survive _ remaining => remaining == 0

/-- A goal's complete relation is derived from the current body and elapsed time. -/
def Goal.observe (goal : Goal) (position : Position) (inventory : Inventory) (elapsed : UInt64) :
    TaskObservation :=
  match goal with
  | .reach target => .reach goal.cue (ReachRelation.between position.x position.y target.x target.y)
  | .collect item required => .collect goal.cue item
      (required.toNat - (inventory.count item).toNat).toUInt32
  | .craft tool => .craft goal.cue tool (!(inventory.owns tool))
  | .survive required => .survive goal.cue (required.toNat - elapsed.toNat).toUInt64

/-- Independent step events; reward is derived from completion rather than stored twice. -/
structure StepResult where
  /-- The installed goal is satisfied after the world step. -/
  done : Bool := false
  /-- The body changed position. -/
  moved : Bool := false
  /-- Harvested item, if any. -/
  harvested : Option Item := none
  /-- A food item was consumed. -/
  ate : Bool := false
  /-- The tool successfully crafted. -/
  crafted : Option Craftable := none
  /-- The body could not pay for this action. -/
  exhausted : Bool := false
  /-- Ground-food items collected on movement. -/
  pickedFood : UInt32 := 0

/-- The only nonzero world reward is exactly one on completion. -/
def StepResult.reward (result : StepResult) : Binary32 :=
  if result.done then ⟨0x3f800000⟩ else ⟨0⟩

/-- Reward and the completion flag cannot disagree for any world-produced result. -/
theorem StepResult.reward_completion (result : StepResult) :
    result.reward.bits = if result.done then 0x3f800000 else 0 := by
  cases h : result.done <;> simp [reward, h]

/-- The public callback domain also admits arbitrary reward words independently
of event flags, as the original library's raw step-result argument does. -/
structure RawStepResult where
  /-- Independent public event fields. -/
  events : StepResult := {}
  /-- Raw public reward, including infinities and NaNs. -/
  reward : Binary32 := ⟨0⟩

/-- World-produced rewards enter the raw callback interface through this derivation. -/
def StepResult.raw (result : StepResult) : RawStepResult := ⟨result, result.reward⟩

end Acorn.Host
