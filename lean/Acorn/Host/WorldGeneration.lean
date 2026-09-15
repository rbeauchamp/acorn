/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.WorldState

/-!
# Current bounded spawn selection and deer placement

The spiral retains the source's cardinal order, repeated corner visits,
strict-best tie rule and best-so-far selection after early exit. No walkable
spawn is promised when the complete search finds none: the legal center is
the explicit fallback. Deer placement makes exactly the configured number
of attempts, with two successive range draws per attempt.
-/
namespace Acorn.Host

/-- An admitted side has an exact positive unsigned range word. -/
def WorldConfig.sideCount (config : WorldConfig) : Word.Count :=
  have hs : config.side < 2 ^ 64 := by
    have := config.raw.side.property
    dsimp [WorldConfig.side]
    omega
  ⟨config.side.toUInt64, by
    change 0 < config.side % (2 ^ 64)
    rw [Nat.mod_eq_of_lt hs]
    exact config.side_pos⟩

/-- No narrowing occurs when converting the admitted side for an RNG draw. -/
theorem WorldConfig.sideCount_exact (config : WorldConfig) : config.sideCount.word.toNat = config.side := by
  change config.side % (2 ^ 64) = config.side
  apply Nat.mod_eq_of_lt
  have := config.raw.side.property
  dsimp [WorldConfig.side]
  omega

/-- Two ordered range draws produce an in-box position by construction. -/
def drawBoxPosition (config : WorldConfig) (rng : Rng.Xoshiro256) :
    BoxPosition config × Rng.Xoshiro256 :=
  let (x, rng) := rng.nextBelow config.sideCount
  let (y, rng) := rng.nextBelow config.sideCount
  (⟨⟨x.val.toNat, by have := x.property; have := config.sideCount_exact; omega⟩,
    ⟨y.val.toNat, by have := y.property; have := config.sideCount_exact; omega⟩⟩, rng)

/-- Count one kind in a square neighborhood, retaining terrain-overflow refusal. -/
def countKindNear {config : WorldConfig} (world : World config) (position : Position)
    (radius : Nat) (kind : TileKind) : Except WorldError Nat := do
  let mut count := 0
  for row in [:2 * radius + 1] do
    for column in [:2 * radius + 1] do
      let some tile := position.translate ((column : Int) - radius) ((row : Int) - radius)
        | .error .coordinateOverflow
      if (← world.tileKind tile) == kind then count := count + 1
  return count

/-- Current best spawn candidate, with its derived tree-plus-stone score. -/
structure SpawnCandidate (config : WorldConfig) where
  /-- Legal candidate body position. -/
  position : BoxPosition config
  /-- Count from the two radius-four neighborhoods. -/
  score : Nat

/-- A single candidate retains earlier candidates on ties and records early exit. -/
def considerSpawn {config : WorldConfig} (world : World config) (x y : Int)
    (best : Option (SpawnCandidate config)) : Except WorldError (Option (SpawnCandidate config) × Bool) := do
  let some position := BoxPosition.checked config x y | return (best, false)
  let trees ← countKindNear world position.position 4 .tree
  let stone ← countKindNear world position.position 4 .stone
  let walkable := (← world.tileKind position.position).walkable
  if !walkable then return (best, false)
  let score := trees + stone
  let selected := match best with
    | none => some ⟨position, score⟩
    | some old => if score > old.score then some ⟨position, score⟩ else best
  return (selected, trees ≥ 2)

/-- Complete bounded spiral, returning the best candidate seen at termination. -/
def selectSpawn {config : WorldConfig} (world : World config) :
    Except WorldError (BoxPosition config) := do
  let mut best : Option (SpawnCandidate config) := none
  for radius in [:config.side] do
    for directionIndex in [:4] do
      let direction := Direction.fromIndex ⟨directionIndex % 4, Nat.mod_lt _ (by decide)⟩
      let (dx, dy) := direction.delta
      for offset in [:2 * radius + 1] do
        let k : Int := (offset : Int) - radius
        let x := (config.side / 2 : Nat) + dx * radius + dy * k
        let y := (config.side / 2 : Nat) + dy * radius + dx * k
        let some x := Coordinate.checked x | .error .coordinateOverflow
        let some y := Coordinate.checked y | .error .coordinateOverflow
        let (candidate, finished) ← considerSpawn world x.val y.val best
        best := candidate
        if finished then return best.map (·.position) |>.getD (BoxPosition.center config)
  return best.map (·.position) |>.getD (BoxPosition.center config)

/-- One placement attempt consumes both draws even when terrain rejects the position. -/
def placeDeer {config : WorldConfig} (world : World config)
    (population : Population Position config.raw.deerCap.toNat) (rng : Rng.Xoshiro256) :
    Except WorldError (Population Position config.raw.deerCap.toNat × Rng.Xoshiro256) := do
  let (position, next) := drawBoxPosition config rng
  let kind ← world.tileKind position.position
  return (if kind.walkable then population.push position.position else population, next)

/-- Complete bounded deer placement, retaining only the population and current RNG. -/
def initializeDeer {config : WorldConfig} (world : World config) :
    Except WorldError (Population Position config.raw.deerCap.toNat × Rng.Xoshiro256) := do
  let mut deer := world.deer
  let mut rng := world.rng
  for _ in [:config.raw.deerCap.toNat] do
    let (nextDeer, nextRng) ← placeDeer world deer rng
    deer := nextDeer
    rng := nextRng
  return (deer, rng)

/-- Complete initialization through the actual spawn and population constructors. -/
def World.initial (config : WorldConfig) : Except WorldError (World config) := do
  let world := World.empty config
  let position ← selectSpawn world
  let (deer, rng) ← initializeDeer world
  return { world with body := { world.body with position := position }, deer := deer, rng := rng }

/-- Generation changes only spawn position, deer population and the placement RNG. -/
theorem World.initial_fields (config : WorldConfig) (world : World config)
    (h : initial config = .ok world) :
    world.time = 0 ∧ world.goal = none ∧ world.goalStart = 0 ∧
    world.body.energy = Energy.new FeatureConstants.energyMax ∧
    world.body.facing = .north ∧ world.food.entries = #[] ∧ world.harvested.size = 0 := by
  unfold initial at h
  cases hs : selectSpawn (World.empty config) with
  | error error => simp [hs, bind, Except.bind] at h
  | ok position =>
    simp only [hs, bind, Except.bind] at h
    cases hd : initializeDeer (World.empty config) with
    | error error => simp [hd] at h
    | ok pair =>
      simp only [hd, pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
      simp [World.empty, Population.empty]

end Acorn.Host
