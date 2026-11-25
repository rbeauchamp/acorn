import Acorn.Host.WorldDynamics

namespace Acorn.Host

def Direction.all : List Direction := [.north, .south, .east, .west]

def Direction.action : Direction → Action
  | .north => .north | .south => .south | .east => .east | .west => .west

def replayCertified {config : WorldConfig} (world : World config) (goal : Goal) (cap : Nat)
    (actions : List Action) : Bool :=
  !actions.isEmpty && decide (actions.length ≤ cap) &&
    match (world.setGoal goal).advanceActions actions with
    | .ok final => final.goalSatisfied
    | .error _ => false

structure ReplayCertificate {config : WorldConfig} (world : World config) (goal : Goal)
    (cap : Nat) where
  actions : List Action
  accepted : replayCertified world goal cap actions = true

def ReplayCertificate.check {config : WorldConfig} (world : World config) (goal : Goal)
    (cap : Nat) (actions : List Action) : Option (ReplayCertificate world goal cap) :=
  if accepted : replayCertified world goal cap actions = true then some ⟨actions, accepted⟩
  else none

def inRegion (cells : List Position) (tile : Position) : Bool :=
  cells.any fun cell => decide (cell = tile)

def inBox (config : WorldConfig) (tile : Position) : Bool :=
  (BoxPosition.checked config tile.x.val tile.y.val).isSome

def InBox (config : WorldConfig) (tile : Position) : Prop :=
  (0 ≤ tile.x.val ∧ tile.x.val < config.side) ∧ (0 ≤ tile.y.val ∧ tile.y.val < config.side)

theorem inBox_iff (config : WorldConfig) (tile : Position) :
    inBox config tile = true ↔ InBox config tile := by
  unfold inBox InBox BoxPosition.checked
  by_cases column : 0 ≤ tile.x.val ∧ tile.x.val < config.side
  · by_cases row : 0 ≤ tile.y.val ∧ tile.y.val < config.side <;> simp [column, row]
  · simp [column]

instance (config : WorldConfig) (tile : Position) : Decidable (InBox config tile) :=
  decidable_of_iff _ (inBox_iff config tile)

def impassable (config : WorldConfig) (boat : Bool) (tile : Position) : Bool :=
  match terrain tile config.raw.seed config.raw.baseScale with
  | .ok .mountain => true
  | .ok .water => !boat
  | _ => false

def boxOffsets : List Int :=
  (List.range (2 * FeatureConstants.reachRadius + 1)).map fun (index : Nat) =>
    (index : Int) - (FeatureConstants.reachRadius : Int)

def covered (config : WorldConfig) (cells : List Position) : Option Position → Bool
  | some tile => inRegion cells tile || !inBox config tile
  | none => true

def regionBlocked (config : WorldConfig) (boat : Bool) (target : Position)
    (cells : List Position) (start : Position) : Bool :=
  !inRegion cells start &&
    (boxOffsets.all fun dy => boxOffsets.all fun dx =>
      covered config cells (target.translate dx dy)) &&
    cells.all fun cell => impassable config boat cell ||
      Direction.all.all fun direction =>
        covered config cells (cell.translate direction.delta.1 direction.delta.2)

structure BlockedCertificate (config : WorldConfig) (boat : Bool) (target start : Position) where
  cells : List Position
  accepted : regionBlocked config boat target cells start = true

def BlockedCertificate.check (config : WorldConfig) (boat : Bool) (target start : Position)
    (cells : List Position) : Option (BlockedCertificate config boat target start) :=
  if accepted : regionBlocked config boat target cells start = true then some ⟨cells, accepted⟩
  else none

def walkableTile (config : WorldConfig) (tile : Position) : Bool :=
  match terrain tile config.raw.seed config.raw.baseScale with
  | .ok kind => kind.walkable
  | .error _ => false

def stanceCertified (config : WorldConfig) (stance : BoxPosition config) (direction : Direction)
    (item : Item) : Bool :=
  (match terrain (stance.facingPosition direction) config.raw.seed config.raw.baseScale with
    | .ok kind => decide (kind.harvestYield = some item)
    | .error _ => false) &&
    walkableTile config stance.position &&
    match stance.position.translate (-direction.delta.1) (-direction.delta.2) with
    | some approach => inBox config approach && walkableTile config approach
    | none => false

structure StanceCertificate (config : WorldConfig) (item : Item) where
  stance : BoxPosition config
  direction : Direction
  accepted : stanceCertified config stance direction item = true

def StanceCertificate.check (config : WorldConfig) (item : Item) (stance : BoxPosition config)
    (direction : Direction) : Option (StanceCertificate config item) :=
  if accepted : stanceCertified config stance direction item = true then
    some ⟨stance, direction, accepted⟩
  else none

end Acorn.Host
