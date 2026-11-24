import Acorn.Host.Task
import Std.Data.TreeMap.Lemmas

namespace Acorn.Host

structure Population (α : Type) (capacity : Nat) where
  entries : Array α
  bounded : entries.size ≤ capacity

def Population.empty {α : Type} (capacity : Nat) : Population α capacity := ⟨#[], by simp⟩

def Population.push {α : Type} {capacity : Nat} (population : Population α capacity) (entry : α) :
    Population α capacity :=
  if h : population.entries.size < capacity then
    ⟨population.entries.push entry, by simp; omega⟩
  else population

def Population.set {α : Type} {capacity : Nat} (population : Population α capacity)
    (index : Fin population.entries.size) (entry : α) : Population α capacity :=
  ⟨population.entries.set index.val entry index.isLt, by simpa using population.bounded⟩

def Population.filter {α : Type} {capacity : Nat} (population : Population α capacity)
    (keep : α → Bool) : Population α capacity :=
  ⟨population.entries.filter keep, Nat.le_trans Array.size_filter_le population.bounded⟩

abbrev HarvestKey (config : WorldConfig) := Fin ((config.side + 2) * (config.side + 2))

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

def BoxPosition.facingKey {config : WorldConfig} (body : BoxPosition config)
    (direction : Direction) : HarvestKey config :=
  match h : harvestKey config (body.facingPosition direction) with
  | some key => key
  | none => False.elim (by obtain ⟨key, hk⟩ := body.facingKey_exists direction; simp [h] at hk)

structure Body (config : WorldConfig) where
  position : BoxPosition config
  facing : Direction
  energy : Energy
  inventory : Inventory

structure World (config : WorldConfig) where
  time : UInt64
  body : Body config
  goal : Option Goal
  goalStart : UInt64
  harvested : Std.TreeMap (HarvestKey config) UInt64
  deer : Population Position config.raw.deerCap.toNat
  food : Population (BoxPosition config) config.raw.foodCap.toNat
  rng : Rng.Xoshiro256

def World.setGoal {config : WorldConfig} (world : World config) (goal : Goal) : World config :=
  { world with goal := some goal, goalStart := world.time }

def World.taskObservation {config : WorldConfig} (world : World config) : TaskObservation :=
  match world.goal with
  | none => .none
  | some goal => goal.observe world.body.position.position world.body.inventory
      (world.time.toNat - world.goalStart.toNat).toUInt64

def World.goalSatisfied {config : WorldConfig} (world : World config) : Bool :=
  world.taskObservation.satisfied

def Inventory.Holds (inventory : Inventory) (item : Item) (count : UInt32) : Prop :=
  (item = .wood ∧ count.toNat ≤ inventory.wood.toNat) ∨
    (item = .stone ∧ count.toNat ≤ inventory.stone.toNat) ∨
    (item = .food ∧ count.toNat ≤ inventory.food.toNat) ∨
    (item = .gold ∧ count.toNat ≤ inventory.gold.toNat)

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

def World.GoalSatisfied {config : WorldConfig} (world : World config) : Prop :=
  ∃ goal, world.goal = some goal ∧ world.Attained goal

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

instance {config : WorldConfig} (world : World config) : Decidable world.GoalSatisfied :=
  decidable_of_iff _ world.goalSatisfied_iff

theorem World.decide_goalSatisfied {config : WorldConfig} (world : World config) :
    decide world.GoalSatisfied = world.goalSatisfied := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, world.goalSatisfied_iff]

def World.dayPhase {config : WorldConfig} (world : World config) : Fin FeatureConstants.dayPhases :=
  let slot := world.time.toNat % config.raw.dayLength.toNat
  let half := config.raw.dayLength.toNat / 2
  let eighth := max 1 (config.raw.dayLength.toNat / FeatureConstants.dayPhases)
  let last := FeatureConstants.dayPhases / 2 - 1
  if slot < half then
    ⟨min (slot / eighth) last, Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)⟩
  else ⟨FeatureConstants.dayPhases / 2 + min ((slot - half) / eighth) last,
    Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.min_le_right _ _) _) (by decide)⟩

theorem World.dayPhase_night_iff {config : WorldConfig} (world : World config) :
    4 ≤ world.dayPhase.val ↔
      config.raw.dayLength.toNat / 2 ≤ world.time.toNat % config.raw.dayLength.toNat := by
  unfold World.dayPhase
  dsimp only
  split
  next first =>
    exact ⟨fun night => absurd night
        (Nat.not_le_of_lt (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide))),
      fun second => absurd first (Nat.not_lt_of_le second)⟩
  next second => exact ⟨fun _ => Nat.le_of_not_lt second, fun _ => Nat.le_add_right _ _⟩

theorem World.dayPhase_reaches {config : WorldConfig} (world : World config)
    (long : 8 ≤ config.raw.dayLength.toNat) (phase : Fin FeatureConstants.dayPhases) :
    ∃ time : UInt64, ({ world with time } : World config).dayPhase = phase := by
  have positive : 0 < config.raw.dayLength.toNat / 8 := by omega
  have below : phase.val < 8 := phase.isLt
  have scaled : ∀ count, count < 4 →
      count * (config.raw.dayLength.toNat / 8) ≤ 3 * (config.raw.dayLength.toNat / 8) :=
    fun count fewer => Nat.mul_le_mul_right _ (by omega)
  have atSlot : ∀ slot, slot < config.raw.dayLength.toNat →
      ({ world with time := slot.toUInt64 } : World config).dayPhase.val =
        if slot < config.raw.dayLength.toNat / 2 then
          min (slot / (config.raw.dayLength.toNat / 8)) 3
        else
          4 + min ((slot - config.raw.dayLength.toNat / 2) /
            (config.raw.dayLength.toNat / 8)) 3 := by
    intro slot inside
    have clock : slot.toUInt64.toNat % config.raw.dayLength.toNat = slot := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt'
        (Nat.lt_trans inside config.raw.dayLength.toNat_lt)]
      exact Nat.mod_eq_of_lt inside
    unfold World.dayPhase
    simp only [FeatureConstants.dayPhases, clock,
      show max 1 (config.raw.dayLength.toNat / 8) = config.raw.dayLength.toNat / 8 by omega]
    split <;> rfl
  by_cases day : phase.val < 4
  · have := scaled phase.val day
    refine ⟨(phase.val * (config.raw.dayLength.toNat / 8)).toUInt64, Fin.ext ?_⟩
    rw [atSlot _ (by omega), ite_eq_left (by omega), Nat.mul_div_cancel _ positive]
    omega
  · have := scaled (phase.val - 4) (by omega)
    refine ⟨(config.raw.dayLength.toNat / 2 +
      (phase.val - 4) * (config.raw.dayLength.toNat / 8)).toUInt64, Fin.ext ?_⟩
    rw [atSlot _ (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left,
      Nat.mul_div_cancel _ positive]
    omega

theorem World.dayPhase_of_dvd {config : WorldConfig} (world : World config)
    (eighths : 8 ∣ config.raw.dayLength.toNat) :
    world.dayPhase.val =
      world.time.toNat % config.raw.dayLength.toNat / (config.raw.dayLength.toNat / 8) := by
  obtain ⟨length, split⟩ := eighths
  have positive : 0 < length := by have := config.positiveDay; omega
  have inside : world.time.toNat % config.raw.dayLength.toNat < 8 * length :=
    split ▸ Nat.mod_lt _ config.positiveDay
  unfold World.dayPhase
  dsimp only
  simp only [FeatureConstants.dayPhases, split, show 8 * length / 8 = length by omega,
    show 8 * length / 2 = 4 * length by omega, show max 1 length = length by omega]
  rw [split] at inside
  have top := (Nat.div_lt_iff_lt_mul positive).mpr inside
  split
  next first =>
    have := (Nat.div_lt_iff_lt_mul positive).mpr first
    dsimp only
    omega
  next second =>
    have := (Nat.le_div_iff_mul_le positive).mpr (Nat.le_of_not_lt second)
    dsimp only
    rw [show 4 * length = length * 4 by omega, Nat.sub_mul_div]
    omega

theorem World.dayPhase_standard {seed : UInt64} {side : Coordinate} {config : WorldConfig}
    (built : WorldConfig.standard seed side = .ok config) (world : World config) :
    world.dayPhase.val = world.time.toNat % 2048 / 256 := by
  have length : config.raw.dayLength.toNat = 2048 := by
    unfold WorldConfig.standard at built
    split at built
    · cases built
    · split at built
      · cases built
      · cases built
        rfl
  rw [world.dayPhase_of_dvd (length ▸ by decide), length]

def World.tileKind {config : WorldConfig} (world : World config) (position : Position) :
    Except WorldError TileKind := do
  let base ← terrain position config.raw.seed config.raw.baseScale
  if base == .tree then
    if let some key := harvestKey config position then
      if let some time := world.harvested[key]? then
        if world.time.toNat - time.toNat < config.raw.regrow.toNat then return .forest
  return base

def World.enterable {config : WorldConfig} (world : World config) (position : Position) :
    Except WorldError Bool := do
  let kind ← world.tileKind position
  return match kind with | .water => world.body.inventory.boat | other => decide other.Walkable

def World.pickupFood {config : WorldConfig} (world : World config) : World config × UInt32 :=
  let remaining := world.food.filter (fun entry => entry != world.body.position)
  let picked := (world.food.entries.size - remaining.entries.size).toUInt32
  ({ world with
    food := remaining
    body := { world.body with inventory := world.body.inventory.add .food picked } }, picked)

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
