import Acorn.Host.WorldGeneration

namespace Acorn.Host

def wanderDeer {config : WorldConfig} (world : World config) (position : Position)
    (rng : Rng.Xoshiro256) : Except WorldError (Position × Rng.Xoshiro256) := do
  let (draw, rng) := rng.next
  if draw % 100 < 8 then
    let (directionWord, rng) := rng.nextBelow ⟨4, by decide⟩
    let direction := Direction.fromIndex ⟨directionWord.val.toNat, directionWord.property⟩
    let (dx, dy) := direction.delta
    match position.translate dx dy with
    | none => return (position, rng)
    | some candidate =>
      let kind ← world.tileKind candidate
      return (if kind.Walkable then candidate else position, rng)
  else return (position, rng)

def wanderPopulation {config : WorldConfig} (world : World config) :
    Except WorldError (Population Position config.raw.deerCap.toNat × Rng.Xoshiro256) := do
  let input : Vector Position world.deer.entries.size := ⟨world.deer.entries, rfl⟩
  let operation (position : Position) : StateT Rng.Xoshiro256 (Except WorldError) Position :=
    fun rng => wanderDeer world position rng
  let (moved, rng) ← (input.mapM operation).run world.rng
  return (⟨moved.toArray, by simpa using world.deer.bounded⟩, rng)

def foodTrials {config : WorldConfig} (world : World config) : Nat →
    Rng.Xoshiro256 → Except WorldError (Option (BoxPosition config) × Rng.Xoshiro256)
  | 0, rng => .ok (none, rng)
  | count + 1, rng => do
    let (position, rng) := drawBoxPosition config rng
    let kind ← world.tileKind position.position
    if kind == .grass then return (some position, rng)
    else foodTrials world count rng

def foodDue (time interval : UInt64) : Bool :=
  if interval == 0 then time == 0 else time.toNat % interval.toNat == 0

def FoodDue (time interval : UInt64) : Prop :=
  (interval = 0 ∧ time = 0) ∨ (interval ≠ 0 ∧ time.toNat % interval.toNat = 0)

theorem foodDue_iff (time interval : UInt64) :
    foodDue time interval = true ↔ FoodDue time interval := by
  unfold foodDue FoodDue
  by_cases zero : interval = 0
  · simp [zero]
  · simp [zero]

instance (time interval : UInt64) : Decidable (FoodDue time interval) :=
  decidable_of_iff _ (foodDue_iff time interval)

def spawnFood {config : WorldConfig} (world : World config) (rng : Rng.Xoshiro256) :
    Except WorldError (Population (BoxPosition config) config.raw.foodCap.toNat × Rng.Xoshiro256) := do
  if decide (FoodDue world.time config.raw.foodInterval) &&
      world.food.entries.size < config.raw.foodCap.toNat then
    let (position, rng) ← foodTrials world 8 rng
    return (match position with | none => world.food | some position => world.food.push position, rng)
  else return (world.food, rng)

structure ActionChange (config : WorldConfig) where
  body : Body config
  harvested : Std.TreeMap (HarvestKey config) UInt64
  food : Population (BoxPosition config) config.raw.foodCap.toNat
  events : StepResult

def ActionChange.unchanged {config : WorldConfig} (world : World config) : ActionChange config :=
  ⟨world.body, world.harvested, world.food, {}⟩

def performAction {config : WorldConfig} (world : World config) (action : Action) :
    Except WorldError (ActionChange config) := do
  let unchanged := ActionChange.unchanged world
  match action.direction with
  | some direction =>
    let (dx, dy) := direction.delta
    let some candidate := world.body.position.position.translate dx dy | .error .coordinateOverflow
    let some position := BoxPosition.checked config candidate.x.val candidate.y.val | return unchanged
    if !(← world.enterable candidate) then return unchanged
    let moved := { world with body := { world.body with position := position, facing := direction } }
    let (picked, count) := moved.pickupFood
    return ⟨picked.body, picked.harvested, picked.food, { moved := true, pickedFood := count }⟩
  | none =>
    match action with
    | .harvest =>
      let position := world.body.position.facingPosition world.body.facing
      let kind ← world.tileKind position
      let some item := kind.harvestYield | return unchanged
      let amount := if item == .wood && world.body.inventory.axe then 3 else 1
      let body := { world.body with inventory := world.body.inventory.add item amount }
      let harvested := if kind == .tree then
          world.harvested.insert (world.body.position.facingKey world.body.facing) world.time
        else world.harvested
      return ⟨body, harvested, world.food, { harvested := some item }⟩
    | .craftAxe | .craftBoat =>
      let tool := if action == .craftAxe then Craftable.axe else .boat
      match world.body.inventory.craft tool with
      | .error _ => return unchanged
      | .ok inventory => return { unchanged with
          body := { world.body with inventory := inventory }
          events := { crafted := some tool } }
    | .eat =>
      if world.body.inventory.food.toNat ≥ 1 then
        let inventory := { world.body.inventory with food := world.body.inventory.food - 1 }
        return { unchanged with
          body := { world.body with inventory := inventory, energy := world.body.energy.gain .eat }
          events := { ate := true } }
      else return unchanged
    | .wait | .north | .south | .east | .west => return unchanged

def payAndAct {config : WorldConfig} (world : World config) (action : Action) :
    Except WorldError (ActionChange config) :=
  match world.body.energy.spend (action.energyCost (world.dayPhase.val ≥ 4)) with
  | none => .ok { ActionChange.unchanged world with
      body := { world.body with energy := world.body.energy.gain .rest }
      events := { exhausted := true } }
  | some energy => performAction { world with body := { world.body with energy := energy } } action

structure PassiveChange (config : WorldConfig) where
  deer : Population Position config.raw.deerCap.toNat
  food : Population (BoxPosition config) config.raw.foodCap.toNat
  rng : Rng.Xoshiro256

def passiveChange {config : WorldConfig} (world : World config) :
    Except WorldError (PassiveChange config) := do
  let (deer, rng) ← wanderPopulation world
  let (food, rng) ← spawnFood world rng
  return ⟨deer, food, rng⟩

def World.applyActive {config : WorldConfig} (world : World config) (active : ActionChange config) :
    World config :=
  { world with body := active.body, harvested := active.harvested, food := active.food }

def World.applyPassive {config : WorldConfig} (world : World config) (passive : PassiveChange config) :
    World config :=
  { world with time := world.time + 1, deer := passive.deer, food := passive.food, rng := passive.rng }

def World.step {config : WorldConfig} (world : World config) (action : Action) :
    Except WorldError (World config × StepResult) := do
  let active ← payAndAct world action
  let acted := world.applyActive active
  let passive ← passiveChange { acted with time := acted.time + 1 }
  let next := acted.applyPassive passive
  return (next, { active.events with done := decide next.GoalSatisfied })

theorem World.step_clock {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events)) :
    next.time = world.time + 1 := by
  unfold step at h
  cases ha : payAndAct world action with
  | error error => simp [ha, bind, Except.bind] at h
  | ok active =>
    simp only [ha, bind, Except.bind] at h
    cases hp : passiveChange { world.applyActive active with time := (world.applyActive active).time + 1 } with
    | error error => simp [hp] at h
    | ok passive =>
      simp only [hp, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      rfl

theorem World.step_goal {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events)) :
    next.goal = world.goal ∧ next.goalStart = world.goalStart := by
  unfold step at h
  cases ha : payAndAct world action with
  | error error => simp [ha, bind, Except.bind] at h
  | ok active =>
    simp only [ha, bind, Except.bind] at h
    cases hp : passiveChange { world.applyActive active with time := (world.applyActive active).time + 1 } with
    | error error => simp [hp] at h
    | ok passive =>
      simp only [hp, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨rfl, rfl⟩

theorem World.step_completion {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events)) :
    events.done = next.goalSatisfied := by
  unfold step at h
  cases ha : payAndAct world action with
  | error error => simp [ha, bind, Except.bind] at h
  | ok active =>
    simp only [ha, bind, Except.bind] at h
    cases hp : passiveChange { world.applyActive active with time := (world.applyActive active).time + 1 } with
    | error error => simp [hp] at h
    | ok passive =>
      simp only [hp, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2, World.decide_goalSatisfied]

def World.advanceActions {config : WorldConfig} : World config → List Action →
    Except WorldError (World config)
  | world, [] => .ok world
  | world, action :: rest => do
    let (next, _) ← world.step action
    next.advanceActions rest

theorem World.advanceActions_clock {config : WorldConfig} (world next : World config)
    (actions : List Action) (h : world.advanceActions actions = .ok next) :
    next.time = world.time + actions.length.toUInt64 := by
  induction actions generalizing world with
  | nil => cases Except.ok.inj h; simp
  | cons action rest ih =>
    simp only [advanceActions] at h
    cases hs : world.step action with
    | error error => simp [hs, bind, Except.bind] at h
    | ok pair =>
      simp only [hs, bind, Except.bind] at h
      rw [ih pair.1 h, World.step_clock world pair.1 action pair.2 hs]
      simp [UInt64.add_assoc, UInt64.add_comm]

theorem World.advanceActions_goal {config : WorldConfig} (world next : World config)
    (actions : List Action) (h : world.advanceActions actions = .ok next) :
    next.goal = world.goal ∧ next.goalStart = world.goalStart := by
  induction actions generalizing world with
  | nil => cases Except.ok.inj h; exact ⟨rfl, rfl⟩
  | cons action rest ih =>
    simp only [advanceActions] at h
    cases hs : world.step action with
    | error error => simp [hs, bind, Except.bind] at h
    | ok pair =>
      simp only [hs, bind, Except.bind] at h
      have ht := ih pair.1 h
      have hp := World.step_goal world pair.1 action pair.2 hs
      exact ⟨ht.1.trans hp.1, ht.2.trans hp.2⟩

end Acorn.Host
