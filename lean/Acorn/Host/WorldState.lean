/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Task
import Std.Data.TreeMap.Lemmas

/-!
# Current bounded world storage

The harvest index is sparse and has a finite key type derived from the body
box plus its one-tile harvest margin. Deer retain signed coordinates outside
the box. Population lengths are bounded at construction and every write;
world time deliberately uses the source's wrapping UInt64 rule.
-/
namespace Acorn.Host

/-- A mutable population cannot outgrow its receiving capacity. -/
structure Population (α : Type) (capacity : Nat) where
  /-- Ordered current entries; no history is retained. -/
  entries : Array α
  /-- Every mutation carries its capacity invariant. -/
  bounded : entries.size ≤ capacity

/-- Empty legal population. -/
def Population.empty {α : Type} (capacity : Nat) : Population α capacity := ⟨#[], by simp⟩

/-- Capacity-admitted insertion; callers can distinguish fullness before drawing. -/
def Population.push {α : Type} {capacity : Nat} (population : Population α capacity) (entry : α) :
    Population α capacity :=
  if h : population.entries.size < capacity then
    ⟨population.entries.push entry, by simp; omega⟩
  else population

/-- Index-bearing replacement keeps the exact population length. -/
def Population.set {α : Type} {capacity : Nat} (population : Population α capacity)
    (index : Fin population.entries.size) (entry : α) : Population α capacity :=
  ⟨population.entries.set index.val entry index.isLt, by simpa using population.bounded⟩

/-- Removal preserves relative order and cannot increase storage. -/
def Population.filter {α : Type} {capacity : Nat} (population : Population α capacity)
    (keep : α → Bool) : Population α capacity :=
  ⟨population.entries.filter keep, Nat.le_trans Array.size_filter_le population.bounded⟩

/-- Every tree that can be harvested has one key in this finite extended box. -/
abbrev HarvestKey (config : WorldConfig) := Fin ((config.side + 2) * (config.side + 2))

/-- Row-major sparse-harvest admission, including the facing tile outside the box. -/
def harvestKey (config : WorldConfig) (position : Position) : Option (HarvestKey config) :=
  if hx : -1 ≤ position.x.val ∧ position.x.val ≤ config.side then
    if hy : -1 ≤ position.y.val ∧ position.y.val ≤ config.side then
      let column := (position.x.val + 1).toNat
      let row := (position.y.val + 1).toNat
      have hc : column < config.side + 2 := by dsimp [column]; omega
      have hr : row + 1 ≤ config.side + 2 := by dsimp [row]; omega
      some ⟨row * (config.side + 2) + column, by
        calc
          row * (config.side + 2) + column < row * (config.side + 2) + (config.side + 2) :=
            Nat.add_lt_add_left hc _
          _ = (row + 1) * (config.side + 2) := by simp [Nat.add_mul]
          _ ≤ (config.side + 2) * (config.side + 2) := Nat.mul_le_mul_right _ hr⟩
    else none
  else none

/-- Every successful key retains its column, row and signed-domain admission. -/
theorem harvestKey_decode (config : WorldConfig) (position : Position) (key : HarvestKey config)
    (h : harvestKey config position = some key) :
    key.val % (config.side + 2) = (position.x.val + 1).toNat ∧
    key.val / (config.side + 2) = (position.y.val + 1).toNat ∧
    -1 ≤ position.x.val ∧ -1 ≤ position.y.val := by
  unfold harvestKey at h
  split at h
  · rename_i hx
    split at h
    · rename_i hy
      cases Option.some.inj h
      have hc : (position.x.val + 1).toNat < config.side + 2 := by omega
      simp only
      constructor
      · simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
      constructor
      · simp [Nat.add_div, Nat.div_eq_of_lt hc, Nat.mod_lt _ (show 0 < config.side + 2 by omega)]
      · exact ⟨hx.1, hy.1⟩
    · contradiction
  · contradiction

/-- A sparse timestamp can never alias a different admitted coordinate. -/
theorem harvestKey_injective (config : WorldConfig) (first second : Position) (key : HarvestKey config)
    (hfirst : harvestKey config first = some key) (hsecond : harvestKey config second = some key) :
    first = second := by
  have hf := harvestKey_decode config first key hfirst
  have hs := harvestKey_decode config second key hsecond
  have hx : first.x = second.x := Subtype.ext (by omega)
  have hy : first.y = second.y := Subtype.ext (by omega)
  cases first
  cases second
  simp_all

/-- A facing neighbor of an in-box body fits signed coordinates without a dynamic refusal. -/
def BoxPosition.facingPosition {config : WorldConfig} (body : BoxPosition config)
    (direction : Direction) : Position :=
  let dx := direction.delta.1
  let dy := direction.delta.2
  have hs := config.raw.side.property
  have hp := config.positiveSide
  have hx := body.x.isLt
  have hy := body.y.isLt
  ⟨⟨(body.x.val : Int) + dx, by
      cases direction <;> dsimp [dx, dy, Direction.delta, WorldConfig.side] at * <;> omega⟩,
    ⟨(body.y.val : Int) + dy, by
      cases direction <;> dsimp [dx, dy, Direction.delta, WorldConfig.side] at * <;> omega⟩⟩

/-- Every facing target, including an outside-box target, has a harvest key. -/
theorem BoxPosition.facingKey_exists {config : WorldConfig} (body : BoxPosition config)
    (direction : Direction) : ∃ key, harvestKey config (body.facingPosition direction) = some key := by
  have hx := body.x.isLt
  have hy := body.y.isLt
  have hxb : -1 ≤ (body.facingPosition direction).x.val ∧
      (body.facingPosition direction).x.val ≤ config.side := by
    cases direction <;> simp [facingPosition, Direction.delta] <;> omega
  have hyb : -1 ≤ (body.facingPosition direction).y.val ∧
      (body.facingPosition direction).y.val ≤ config.side := by
    cases direction <;> simp [facingPosition, Direction.delta] <;> omega
  simp [harvestKey, hxb, hyb]

/-- The proved facing admission yields the key used at the tree write boundary. -/
def BoxPosition.facingKey {config : WorldConfig} (body : BoxPosition config)
    (direction : Direction) : HarvestKey config :=
  match h : harvestKey config (body.facingPosition direction) with
  | some key => key
  | none => False.elim (by obtain ⟨key, hk⟩ := body.facingKey_exists direction; simp [h] at hk)

/-- The body always belongs to its immutable receiving box. -/
structure Body (config : WorldConfig) where
  /-- Current in-box position. -/
  position : BoxPosition config
  /-- Last successful movement direction. -/
  facing : Direction
  /-- Proof-bearing energy balance. -/
  energy : Energy
  /-- Saturating unsigned inventory and possession flags. -/
  inventory : Inventory

/-- Current world state; it contains no action-selection or supervision capability. -/
structure World (config : WorldConfig) where
  /-- Wrapping physical-world clock. -/
  time : UInt64
  /-- Current body state. -/
  body : Body config
  /-- Installed goal; its cue is derived from the same value. -/
  goal : Option Goal
  /-- Wrapping clock value at goal installation. -/
  goalStart : UInt64
  /-- At most one timestamp per legal harvest site. -/
  harvested : Std.TreeMap (HarvestKey config) UInt64
  /-- Ordered deer population; wandering does not require in-box coordinates. -/
  deer : Population Position config.raw.deerCap.toNat
  /-- Ordered in-box food population, retaining duplicate sites. -/
  food : Population (BoxPosition config) config.raw.foodCap.toNat
  /-- One deterministic environment RNG stream. -/
  rng : Rng.Xoshiro256

/-- Goal installation preserves physical state and resets only the goal origin. -/
def World.setGoal {config : WorldConfig} (world : World config) (goal : Goal) : World config :=
  { world with goal := some goal, goalStart := world.time }

/-- Goal relation uses saturating age even after the physical clock wraps. -/
def World.taskObservation {config : WorldConfig} (world : World config) : TaskObservation :=
  match world.goal with
  | none => .none
  | some goal => goal.observe world.body.position.position world.body.inventory
      (world.time.toNat - world.goalStart.toNat).toUInt64

/-- The world and observer share exactly one completion predicate. -/
def World.goalSatisfied {config : WorldConfig} (world : World config) : Bool :=
  world.taskObservation.satisfied

/-- The inventory holds a count of an item: the stored field of that item is at least the
count. Stated by the constructor of the item, with no count reader. -/
def Inventory.Holds (inventory : Inventory) (item : Item) (count : UInt32) : Prop :=
  (item = .wood ∧ count.toNat ≤ inventory.wood.toNat) ∨
    (item = .stone ∧ count.toNat ≤ inventory.stone.toNat) ∨
    (item = .food ∧ count.toNat ≤ inventory.food.toNat) ∨
    (item = .gold ∧ count.toNat ≤ inventory.gold.toNat)

/-- A goal is attained in a world, on the stored fields of the world: the two box indices of
the body are within three tiles of the target of a reach goal or of a concealed target, the
inventory holds the count of a collect goal or owns the tool of a craft goal, and the clock is
at least the duration of a survive goal after the clock of the installation. The radius is the
literal three, and the elapsed time is a difference of natural numbers. -/
def World.Attained {config : WorldConfig} (world : World config) (goal : Goal) : Prop :=
  match goal with
  | .reach target =>
    (target.x.val - (world.body.position.x.val : Int)).natAbs ≤ 3 ∧
      (target.y.val - (world.body.position.y.val : Int)).natAbs ≤ 3
  | .collect item count => world.body.inventory.Holds item count
  | .craft tool => world.body.inventory.Owns tool
  | .survive required => required.toNat ≤ world.time.toNat - world.goalStart.toNat
  | .find target =>
    (target.x.val - (world.body.position.x.val : Int)).natAbs ≤ 3 ∧
      (target.y.val - (world.body.position.y.val : Int)).natAbs ≤ 3

/-- A goal is installed in the world and attained there. -/
def World.GoalSatisfied {config : WorldConfig} (world : World config) : Prop :=
  ∃ goal, world.goal = some goal ∧ world.Attained goal

/-- A natural number below the word size has the word zero exactly when it is zero. -/
private theorem toUInt32_eq_zero_iff (count : Nat) (bound : count < 2 ^ 32) :
    count.toUInt32 = 0 ↔ count = 0 := by
  constructor
  · intro zero
    have word := congrArg UInt32.toNat zero
    rw [show count.toUInt32 = UInt32.ofNat count from rfl, UInt32.toNat_ofNat_of_lt' bound] at word
    exact word
  · intro zero
    rw [zero]
    rfl

/-- A natural number below the word size has the word zero exactly when it is zero. -/
private theorem toUInt64_eq_zero_iff (count : Nat) (bound : count < 2 ^ 64) :
    count.toUInt64 = 0 ↔ count = 0 := by
  constructor
  · intro zero
    have word := congrArg UInt64.toNat zero
    rw [show count.toUInt64 = UInt64.ofNat count from rfl, UInt64.toNat_ofNat_of_lt' bound] at word
    exact word
  · intro zero
    rw [zero]
    rfl

/-- The completion predicate accepts the observation of a goal in a world exactly when the goal
is attained there. The observation embeds the box indices as coordinates, reads the count and
the ownership through their readers, and converts the elapsed time to a word. -/
theorem World.observe_satisfied_iff {config : WorldConfig} (world : World config) (goal : Goal) :
    (goal.observe world.body.position.position world.body.inventory
      (world.time.toNat - world.goalStart.toNat).toUInt64).satisfied = true ↔
      world.Attained goal := by
  cases goal with
  | reach target =>
    simp only [Goal.observe, TaskObservation.satisfied, ReachRelation.distance,
      ReachRelation.between, Attained, beq_iff_eq, BoxPosition.position,
      FeatureConstants.reachRadius, Nat.sub_eq_zero_iff_le, Nat.max_le]
  | collect item count =>
    simp only [Goal.observe, TaskObservation.satisfied, beq_iff_eq]
    rw [toUInt32_eq_zero_iff _ (by have := count.toNat_lt; omega)]
    cases item <;> simp only [Attained, Inventory.Holds, Inventory.count, Nat.sub_eq_zero_iff_le,
      reduceCtorEq, true_and, false_and, or_false, false_or]
  | craft tool =>
    simp only [Goal.observe, TaskObservation.satisfied, Attained, Bool.not_not]
    exact Inventory.owns_iff _ _
  | survive required =>
    simp only [Goal.observe, TaskObservation.satisfied, beq_iff_eq, Attained]
    rw [toUInt64_eq_zero_iff _ (by have := required.toNat_lt; omega)]
    have elapsed : ((world.time.toNat - world.goalStart.toNat).toUInt64).toNat =
        world.time.toNat - world.goalStart.toNat := by
      have bound := world.time.toNat_lt
      exact Nat.mod_eq_of_lt (by omega)
    rw [elapsed]
    exact ⟨fun zero => Nat.le_of_sub_eq_zero zero, fun le => Nat.sub_eq_zero_of_le le⟩
  | find target =>
    simp only [Goal.observe, TaskObservation.satisfied, ReachRelation.distance,
      ReachRelation.between, Attained, beq_iff_eq, BoxPosition.position,
      FeatureConstants.reachRadius, Nat.sub_eq_zero_iff_le, Nat.max_le]

/-- The completion flag is set exactly when a goal is installed and attained. -/
theorem World.goalSatisfied_iff {config : WorldConfig} (world : World config) :
    world.goalSatisfied = true ↔ world.GoalSatisfied := by
  unfold World.goalSatisfied World.taskObservation GoalSatisfied
  cases installed : world.goal with
  | none =>
    exact ⟨fun satisfied => absurd satisfied Bool.false_ne_true, fun ⟨_, same, _⟩ => nomatch same⟩
  | some goal =>
    exact (world.observe_satisfied_iff goal).trans
      ⟨fun attained => ⟨goal, rfl, attained⟩, fun ⟨_, same, attained⟩ => by
        cases same
        exact attained⟩

/-- The completion flag decides `GoalSatisfied`. -/
instance {config : WorldConfig} (world : World config) : Decidable world.GoalSatisfied :=
  decidable_of_iff _ world.goalSatisfied_iff

/-- The decision of `GoalSatisfied` is the completion flag. -/
theorem World.decide_goalSatisfied {config : WorldConfig} (world : World config) :
    decide world.GoalSatisfied = world.goalSatisfied := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, world.goalSatisfied_iff]

/-- The eight phase buckets preserve custom odd or short day periods. -/
def World.dayPhase {config : WorldConfig} (world : World config) : Fin FeatureConstants.dayPhases :=
  let slot := world.time.toNat % config.raw.dayLength.toNat
  let half := config.raw.dayLength.toNat / 2
  let eighth := max 1 (config.raw.dayLength.toNat / FeatureConstants.dayPhases)
  let phase := if slot < half then slot / eighth else FeatureConstants.dayPhases / 2 + (slot - half) / eighth
  ⟨min phase (FeatureConstants.dayPhases - 1), by change min phase 7 < 8; omega⟩

/-- Effective terrain reads the sparse timestamp of exactly the requested site. -/
def World.tileKind {config : WorldConfig} (world : World config) (position : Position) :
    Except WorldError TileKind := do
  let base ← terrain position config.raw.seed config.raw.baseScale
  if base == .tree then
    if let some key := harvestKey config position then
      if let some time := world.harvested[key]? then
        if world.time.toNat - time.toNat < config.raw.regrow.toNat then return .forest
  return base

/-- Boat permission affects body movement only; other kinds use their closed table. -/
def World.enterable {config : WorldConfig} (world : World config) (position : Position) :
    Except WorldError Bool := do
  let kind ← world.tileKind position
  return match kind with | .water => world.body.inventory.boat | other => decide other.Walkable

/-- Food pickup removes every duplicate at the body position, preserving survivor order. -/
def World.pickupFood {config : WorldConfig} (world : World config) : World config × UInt32 :=
  let remaining := world.food.filter (fun entry => entry != world.body.position)
  let picked := (world.food.entries.size - remaining.entries.size).toUInt32
  ({ world with
    food := remaining
    body := { world.body with inventory := world.body.inventory.add .food picked } }, picked)

/-- New world storage before bounded spawn selection and placement. -/
def World.empty (config : WorldConfig) : World config :=
  { time := 0
    body := ⟨BoxPosition.center config, .north, Energy.new FeatureConstants.energyMax, ⟨0, 0, 0, 0, false, false⟩⟩
    goal := none
    goalStart := 0
    harvested := ∅
    deer := Population.empty _
    food := Population.empty _
    rng := Rng.Xoshiro256.seed (Rng.streamKey config.raw.seed 1) }

end Acorn.Host
