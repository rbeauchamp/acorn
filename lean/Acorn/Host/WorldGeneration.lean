import Acorn.Host.WorldState

namespace Acorn.Host

def WorldConfig.sideCount (config : WorldConfig) : Word.Count :=
  have hs : config.side < 2 ^ 64 := by
    have := config.raw.side.property
    dsimp [WorldConfig.side]
    omega
  ⟨config.side.toUInt64, by
    change 0 < config.side % (2 ^ 64)
    rw [Nat.mod_eq_of_lt hs]
    exact config.side_pos⟩

theorem WorldConfig.sideCount_exact (config : WorldConfig) : config.sideCount.word.toNat = config.side := by
  change config.side % (2 ^ 64) = config.side
  apply Nat.mod_eq_of_lt
  have := config.raw.side.property
  dsimp [WorldConfig.side]
  omega

def drawBoxPosition (config : WorldConfig) (rng : Rng.Xoshiro256) :
    BoxPosition config × Rng.Xoshiro256 :=
  let (x, rng) := rng.nextBelow config.sideCount
  let (y, rng) := rng.nextBelow config.sideCount
  (⟨⟨x.val.toNat, by have := x.property; have := config.sideCount_exact; omega⟩,
    ⟨y.val.toNat, by have := y.property; have := config.sideCount_exact; omega⟩⟩, rng)

def countKindNear {config : WorldConfig} (world : World config) (position : Position)
    (radius : Nat) (kind : TileKind) : Except WorldError Nat := do
  let mut count := 0
  for row in [:2 * radius + 1] do
    for column in [:2 * radius + 1] do
      let some tile := position.translate ((column : Int) - radius) ((row : Int) - radius)
        | .error .coordinateOverflow
      if (← world.tileKind tile) == kind then count := count + 1
  return count

structure SpawnCandidate (config : WorldConfig) where
  position : BoxPosition config
  score : Nat

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
        let (candidate, finished) ← considerSpawn world x y best
        best := candidate
        if finished then return best.map (·.position) |>.getD (BoxPosition.center config)
  return best.map (·.position) |>.getD (BoxPosition.center config)

def placeDeer {config : WorldConfig} (world : World config)
    (population : Population Position config.raw.deerCap.toNat) (rng : Rng.Xoshiro256) :
    Except WorldError (Population Position config.raw.deerCap.toNat × Rng.Xoshiro256) := do
  let (position, next) := drawBoxPosition config rng
  let kind ← world.tileKind position.position
  return (if kind.walkable then population.push position.position else population, next)

def initializeDeer {config : WorldConfig} (world : World config) :
    Except WorldError (Population Position config.raw.deerCap.toNat × Rng.Xoshiro256) := do
  let mut deer := world.deer
  let mut rng := world.rng
  for _ in [:config.raw.deerCap.toNat] do
    let (nextDeer, nextRng) ← placeDeer world deer rng
    deer := nextDeer
    rng := nextRng
  return (deer, rng)

def World.initial (config : WorldConfig) : Except WorldError (World config) := do
  if !config.raw.admissible then .error .inadmissibleConfig
  let world := World.empty config
  let position ← selectSpawn world
  let (deer, rng) ← initializeDeer world
  return { world with body := { world.body with position := position }, deer := deer, rng := rng }

theorem World.initial_admissible (config : WorldConfig) (world : World config)
    (h : initial config = .ok world) : config.raw.admissible = true := by
  unfold initial at h
  cases hadm : config.raw.admissible with
  | false => simp [hadm, bind, Except.bind] at h
  | true => rfl

theorem World.initial_fields (config : WorldConfig) (world : World config)
    (h : initial config = .ok world) :
    world.time = 0 ∧ world.goal = none ∧ world.goalStart = 0 ∧
    world.body.energy = Energy.new FeatureConstants.energyMax ∧
    world.body.facing = .north ∧ world.food.entries = #[] ∧ world.harvested.size = 0 := by
  unfold initial at h
  cases hadm : config.raw.admissible with
  | false => simp [hadm, bind, Except.bind] at h
  | true =>
    simp only [hadm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
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
