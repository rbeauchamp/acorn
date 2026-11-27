import Acorn.Host.Terrain

namespace Acorn.Host

inductive Direction where
  | north
  | south
  | east
  | west
  deriving DecidableEq

def Direction.delta : Direction → Int × Int
  | .north => (0, -1) | .south => (0, 1) | .east => (1, 0) | .west => (-1, 0)

def Direction.fromIndex (index : Fin 4) : Direction :=
  match index.val with | 0 => .north | 1 => .south | 2 => .east | _ => .west

inductive Action where
  | north
  | south
  | east
  | west
  | wait
  | harvest
  | craftAxe
  | craftBoat
  | eat
  deriving DecidableEq

def Action.index : Action → Fin 9
  | .north => 0 | .south => 1 | .east => 2 | .west => 3 | .wait => 4
  | .harvest => 5 | .craftAxe => 6 | .craftBoat => 7 | .eat => 8

def Action.fromIndex (index : Nat) : Action :=
  match index with
  | 0 => .north | 1 => .south | 2 => .east | 3 => .west | 4 => .wait
  | 5 => .harvest | 6 => .craftAxe | 7 => .craftBoat | _ => .eat

theorem Action.index_roundtrip (action : Action) : fromIndex action.index.val = action := by
  cases action <;> rfl

def Action.direction : Action → Option Direction
  | .north => some .north | .south => some .south
  | .east => some .east | .west => some .west
  | .wait | .harvest | .craftAxe | .craftBoat | .eat => none

def Craftable.recipe : Craftable → Nat × Nat
  | .axe => (FeatureConstants.axeWood, FeatureConstants.axeStone)
  | .boat => (FeatureConstants.boatWood, FeatureConstants.boatStone)

def Inventory.count (inventory : Inventory) : Item → UInt32
  | .wood => inventory.wood | .stone => inventory.stone
  | .food => inventory.food | .gold => inventory.gold

def Inventory.add (inventory : Inventory) (item : Item) (amount : UInt32) : Inventory :=
  let total := (min (2 ^ 32 - 1) ((inventory.count item).toNat + amount.toNat)).toUInt32
  match item with
  | .wood => { inventory with wood := total } | .stone => { inventory with stone := total }
  | .food => { inventory with food := total } | .gold => { inventory with gold := total }

def Inventory.owns (inventory : Inventory) : Craftable → Bool
  | .axe => inventory.axe | .boat => inventory.boat

def Inventory.Owns (inventory : Inventory) (tool : Craftable) : Prop :=
  (tool = .axe ∧ inventory.axe = true) ∨ (tool = .boat ∧ inventory.boat = true)

theorem Inventory.owns_iff (inventory : Inventory) (tool : Craftable) :
    inventory.owns tool = true ↔ inventory.Owns tool := by
  cases tool <;> simp [Inventory.owns, Inventory.Owns]

instance (inventory : Inventory) (tool : Craftable) : Decidable (inventory.Owns tool) :=
  decidable_of_iff _ (inventory.owns_iff tool)

inductive CraftError where
  | alreadyOwned
  | notEnoughWood (available required : Nat)
  | notEnoughStone (available required : Nat)
  deriving DecidableEq

def Inventory.craft (inventory : Inventory) (tool : Craftable) : Except CraftError Inventory :=
  let (wood, stone) := tool.recipe
  if inventory.Owns tool then .error .alreadyOwned
  else if inventory.wood.toNat < wood then .error (.notEnoughWood inventory.wood.toNat wood)
  else if inventory.stone.toNat < stone then .error (.notEnoughStone inventory.stone.toNat stone)
  else
    let paid : Inventory := { inventory with
      wood := (inventory.wood.toNat - wood).toUInt32
      stone := (inventory.stone.toNat - stone).toUInt32 }
    .ok (match tool with | .axe => { paid with axe := true } | .boat => { paid with boat := true })

theorem Inventory.craft_exact (inventory next : Inventory) (tool : Craftable)
    (h : inventory.craft tool = .ok next) :
    next.wood.toNat + tool.recipe.1 = inventory.wood.toNat ∧
    next.stone.toNat + tool.recipe.2 = inventory.stone.toNat ∧ next.owns tool = true := by
  rcases hr : tool.recipe with ⟨wood, stone⟩
  by_cases ho : inventory.Owns tool
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

abbrev Energy := Fin (FeatureConstants.energyMax + 1)

inductive EnergyGain where
  | rest
  | eat

def EnergyGain.amount : EnergyGain → Nat
  | .rest => FeatureConstants.energyRestRecover | .eat => FeatureConstants.energyEatRestore

def Energy.new (units : Nat) : Energy := ⟨min units FeatureConstants.energyMax, by omega⟩

def Energy.gain (energy : Energy) (source : EnergyGain) : Energy :=
  Energy.new (energy.val + source.amount)

def Energy.spend (energy : Energy) (cost : Nat) : Option Energy :=
  if cost ≤ energy.val then some ⟨energy.val - cost, by have := energy.isLt; omega⟩ else none

theorem Energy.spend_balance (energy next : Energy) (cost : Nat)
    (h : energy.spend cost = some next) : next.val + cost = energy.val := by
  unfold spend at h
  split at h
  · cases Option.some.inj h
    simp only
    omega
  · contradiction

def Action.energyCost (action : Action) (night : Bool) : Nat :=
  (if action == .harvest then FeatureConstants.harvestCost else 1) *
    (if night then FeatureConstants.nightMultiplier else FeatureConstants.dayMultiplier)

def Action.rawEnergyCost (action : Action) (multiplier : UInt32) : Option UInt32 :=
  let cost := (if action == .harvest then FeatureConstants.harvestCost else 1) * multiplier.toNat
  if cost < 2 ^ 32 then some cost.toUInt32 else none

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

theorem Action.cost_bounds (action : Action) (night : Bool) :
    1 ≤ action.energyCost night ∧ action.energyCost night ≤ EnergyGain.rest.amount := by
  cases action <;> cases night <;> decide

inductive GoalFamily where
  | reach
  | collect
  | craft
  | survive
  deriving DecidableEq

inductive Goal where
  | reach (target : Position)
  | collect (item : Item) (count : UInt32)
  | craft (tool : Craftable)
  | survive (steps : UInt64)
  | find (target : Position)

def Goal.family : Goal → GoalFamily
  | .reach _ => .reach | .collect _ _ => .collect | .craft _ => .craft | .survive _ => .survive
  | .find _ => .reach

def Goal.cue : Goal → UInt64
  | .reach target => Rng.hash3 1 (coordinateWord target.x) (coordinateWord target.y)
  | .collect item count => Rng.hash3 2 item.code count.toUInt64
  | .craft tool => Rng.hash3 3 tool.code 0
  | .survive steps => Rng.hash3 4 steps 0
  | .find _ => Rng.hash3 5 0 0

def TaskObservation.satisfied : TaskObservation → Bool
  | .none => false
  | .reach _ relation => relation.distance == 0
  | .collect _ _ remaining => remaining == 0
  | .craft _ _ remaining => !remaining
  | .survive _ remaining => remaining == 0
  | .find _ here => here

def Goal.observe (goal : Goal) (position : Position) (inventory : Inventory) (elapsed : UInt64) :
    TaskObservation :=
  match goal with
  | .reach target => .reach goal.cue (ReachRelation.between position.x position.y target.x target.y)
  | .collect item required => .collect goal.cue item
      (required.toNat - (inventory.count item).toNat).toUInt32
  | .craft tool => .craft goal.cue tool (!(inventory.owns tool))
  | .survive required => .survive goal.cue (required.toNat - elapsed.toNat).toUInt64
  | .find target => .find goal.cue
      ((ReachRelation.between position.x position.y target.x target.y).distance == 0)

structure StepResult where
  done : Bool := false
  moved : Bool := false
  harvested : Option Item := none
  ate : Bool := false
  crafted : Option Craftable := none
  exhausted : Bool := false
  pickedFood : UInt32 := 0

def StepResult.reward (result : StepResult) : Binary32 :=
  if result.done then ⟨0x3f800000⟩ else ⟨0⟩

theorem StepResult.reward_completion (result : StepResult) :
    result.reward.bits = if result.done then 0x3f800000 else 0 := by
  cases h : result.done <;> simp [reward, h]

structure RawStepResult where
  events : StepResult := {}
  reward : Binary32 := ⟨0⟩

def StepResult.raw (result : StepResult) : RawStepResult := ⟨result, result.reward⟩

end Acorn.Host
