import Acorn.Host.WorldGeneration

namespace AcornVerif.CurrentSpawn
open Acorn Acorn.Host

def Walkable {config : WorldConfig} (world : World config) (tile : BoxPosition config) : Prop :=
  ∃ kind, world.tileKind tile.position = .ok kind ∧ kind.walkable = true

def Rich {config : WorldConfig} (world : World config) (tile : BoxPosition config) : Prop :=
  Walkable world tile ∧ ∃ trees, countKindNear world tile.position 4 .tree = .ok trees ∧ 2 ≤ trees

structure Scored {config : WorldConfig} (world : World config)
    (candidate : SpawnCandidate config) : Prop where
  walkable : Walkable world candidate.position
  scored : ∃ trees stone, countKindNear world candidate.position.position 4 .tree = .ok trees ∧
    countKindNear world candidate.position.position 4 .stone = .ok stone ∧
    candidate.score = trees + stone

theorem not_walkable {config : WorldConfig} {world : World config} {tile : BoxPosition config}
    {kind : TileKind} (located : world.tileKind tile.position = .ok kind)
    (blocked : kind.walkable = false) : ¬ Walkable world tile := by
  rintro ⟨other, same, walk⟩
  rw [located] at same
  cases Except.ok.inj same
  rw [blocked] at walk
  cases walk

theorem not_rich {config : WorldConfig} {world : World config} {tile : BoxPosition config}
    {trees : Nat} (counted : countKindNear world tile.position 4 .tree = .ok trees)
    (few : ¬ 2 ≤ trees) : ¬ Rich world tile := by
  rintro ⟨-, other, same, enough⟩
  rw [counted] at same
  cases Except.ok.inj same
  exact few enough

theorem scored_score {config : WorldConfig} {world : World config}
    {candidate : SpawnCandidate config} {trees stone : Nat} (scored : Scored world candidate)
    (treeCount : countKindNear world candidate.position.position 4 .tree = .ok trees)
    (stoneCount : countKindNear world candidate.position.position 4 .stone = .ok stone) :
    candidate.score = trees + stone := by
  obtain ⟨otherTrees, otherStone, treeSame, stoneSame, total⟩ := scored.scored
  rw [treeCount] at treeSame
  rw [stoneCount] at stoneSame
  cases Except.ok.inj treeSame
  cases Except.ok.inj stoneSame
  exact total

inductive Considered {config : WorldConfig} (world : World config) (x y : Int)
    (best selected : Option (SpawnCandidate config)) (finished : Bool) : Prop where
  | outside (refused : BoxPosition.checked config x y = none) (same : selected = best)
      (continues : finished = false)
  | blocked (position : BoxPosition config) (kind : TileKind)
      (admitted : BoxPosition.checked config x y = some position)
      (located : world.tileKind position.position = .ok kind) (walk : kind.walkable = false)
      (same : selected = best) (continues : finished = false)
  | scored (position : BoxPosition config) (kind : TileKind) (trees stone : Nat)
      (admitted : BoxPosition.checked config x y = some position)
      (located : world.tileKind position.position = .ok kind) (walk : kind.walkable = true)
      (treeCount : countKindNear world position.position 4 .tree = .ok trees)
      (stoneCount : countKindNear world position.position 4 .stone = .ok stone)
      (chosen : (best = none ∧ selected = some ⟨position, trees + stone⟩) ∨
        (∃ old, best = some old ∧ old.score < trees + stone ∧
          selected = some ⟨position, trees + stone⟩) ∨
        (∃ old, best = some old ∧ trees + stone ≤ old.score ∧ selected = some old))
      (flag : finished = decide (trees ≥ 2))

theorem considerSpawn_outcome {config : WorldConfig} (world : World config) (x y : Int)
    (best selected : Option (SpawnCandidate config)) (finished : Bool)
    (h : considerSpawn world x y best = .ok (selected, finished)) :
    Considered world x y best selected finished := by
  unfold considerSpawn at h
  cases admitted : BoxPosition.checked config x y with
  | none =>
    simp only [admitted, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact .outside admitted h.1.symm h.2.symm
  | some position =>
    simp only [admitted] at h
    cases treeCount : countKindNear world position.position 4 .tree with
    | error refusal => simp [treeCount, bind, Except.bind] at h
    | ok trees =>
      cases stoneCount : countKindNear world position.position 4 .stone with
      | error refusal => simp [treeCount, stoneCount, bind, Except.bind] at h
      | ok stone =>
        cases located : world.tileKind position.position with
        | error refusal => simp [treeCount, stoneCount, located, bind, Except.bind] at h
        | ok kind =>
          cases walk : kind.walkable with
          | false =>
            simp only [treeCount, stoneCount, located, walk, bind, Except.bind, pure,
              Except.pure, Bool.not_false, eq_self, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
            exact .blocked position kind admitted located walk h.1.symm h.2.symm
          | true =>
            simp only [treeCount, stoneCount, located, walk, bind, Except.bind, pure,
              Except.pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine .scored position kind trees stone admitted located walk treeCount stoneCount
              ?_ rfl
            cases best with
            | none => exact Or.inl ⟨rfl, rfl⟩
            | some old =>
              by_cases better : trees + stone > old.score
              · exact Or.inr (Or.inl ⟨old, rfl, better, ite_eq_left better⟩)
              · exact Or.inr (Or.inr ⟨old, rfl, by omega, ite_eq_right better⟩)

theorem considerSpawn_contract {config : WorldConfig} (world : World config) (x y : Int)
    (best selected : Option (SpawnCandidate config)) (finished : Bool)
    (h : considerSpawn world x y best = .ok (selected, finished))
    (held : ∀ candidate, best = some candidate → Scored world candidate) :
    (∀ candidate, selected = some candidate → Scored world candidate) ∧
    (∀ old, best = some old → ∃ kept, selected = some kept ∧ old.score ≤ kept.score) ∧
    (finished = true → ∃ position chosen, BoxPosition.checked config x y = some position ∧
      Rich world position ∧ selected = some chosen ∧ 2 ≤ chosen.score) := by
  cases considerSpawn_outcome world x y best selected finished h with
  | outside refused same continues =>
    subst same continues
    exact ⟨held, fun old was => ⟨old, was, Nat.le_refl _⟩, fun exit => by cases exit⟩
  | blocked position kind admitted located walk same continues =>
    subst same continues
    exact ⟨held, fun old was => ⟨old, was, Nat.le_refl _⟩, fun exit => by cases exit⟩
  | scored position kind trees stone admitted located walk treeCount stoneCount chosen flag =>
    subst flag
    have fresh : Scored world ⟨position, trees + stone⟩ :=
      ⟨⟨kind, located, walk⟩, ⟨trees, stone, treeCount, stoneCount, rfl⟩⟩
    have rich : decide (trees ≥ 2) = true → Rich world position := fun exit =>
      ⟨⟨kind, located, walk⟩, trees, treeCount, of_decide_eq_true exit⟩
    rcases chosen with ⟨empty, picked⟩ | ⟨old, was, better, picked⟩ | ⟨old, was, worse, picked⟩
    · subst empty picked
      refine ⟨fun candidate same => ?_, fun old was => (by cases was), fun exit => ?_⟩
      · cases Option.some.inj same
        exact fresh
      · have enough : 2 ≤ trees := of_decide_eq_true exit
        exact ⟨position, _, admitted, rich exit, rfl, by change 2 ≤ trees + stone; omega⟩
    · subst was picked
      refine ⟨fun candidate same => ?_, fun other was => ?_, fun exit => ?_⟩
      · cases Option.some.inj same
        exact fresh
      · cases Option.some.inj was
        exact ⟨_, rfl, by change old.score ≤ trees + stone; omega⟩
      · have enough : 2 ≤ trees := of_decide_eq_true exit
        exact ⟨position, _, admitted, rich exit, rfl, by change 2 ≤ trees + stone; omega⟩
    · subst was picked
      refine ⟨held, fun other was => ⟨other, was, Nat.le_refl _⟩, fun exit => ?_⟩
      have enough : 2 ≤ trees := of_decide_eq_true exit
      exact ⟨position, old, admitted, rich exit, rfl, by omega⟩

structure Searching {config : WorldConfig} (world : World config)
    (seen : BoxPosition config → Prop) (best : Option (SpawnCandidate config)) : Prop where
  scored : ∀ candidate, best = some candidate → Scored world candidate
  poor : ∀ tile, seen tile → ¬ Rich world tile
  barren : best = none → ∀ tile, seen tile → ¬ Walkable world tile
  greatest : ∀ other, Scored world other → seen other.position →
    ∃ kept, best = some kept ∧ other.score ≤ kept.score

theorem Searching.mono {config : WorldConfig} {world : World config}
    {seen fewer : BoxPosition config → Prop} {best : Option (SpawnCandidate config)}
    (searching : Searching world seen best) (subset : ∀ tile, fewer tile → seen tile) :
    Searching world fewer best :=
  ⟨searching.scored, fun tile member => searching.poor tile (subset tile member),
    fun empty tile member => searching.barren empty tile (subset tile member),
    fun other scored member => searching.greatest other scored (subset _ member)⟩

theorem search_step {config : WorldConfig} {world : World config} {x y : Int}
    {seen : BoxPosition config → Prop} {best selected : Option (SpawnCandidate config)}
    {finished : Bool} (searching : Searching world seen best)
    (outcome : Considered world x y best selected finished) :
    (finished = false → Searching world
      (fun tile => seen tile ∨ BoxPosition.checked config x y = some tile) selected) ∧
    (finished = true → ∃ chosen, selected = some chosen ∧ Scored world chosen ∧
      2 ≤ chosen.score) := by
  cases outcome with
  | outside refused same continues =>
    subst same continues
    refine ⟨fun _ => ⟨searching.scored, fun tile member => ?_, fun empty tile member => ?_,
      fun other scored member => ?_⟩, fun exit => by cases exit⟩
    · rcases member with member | member
      · exact searching.poor tile member
      · rw [refused] at member
        cases member
    · rcases member with member | member
      · exact searching.barren empty tile member
      · rw [refused] at member
        cases member
    · rcases member with member | member
      · exact searching.greatest other scored member
      · rw [refused] at member
        cases member
  | blocked position kind admitted located walk same continues =>
    subst same continues
    refine ⟨fun _ => ⟨searching.scored, fun tile member => ?_, fun empty tile member => ?_,
      fun other scored member => ?_⟩, fun exit => by cases exit⟩
    · rcases member with member | member
      · exact searching.poor tile member
      · rw [admitted] at member
        cases Option.some.inj member
        exact fun rich => not_walkable located walk rich.1
    · rcases member with member | member
      · exact searching.barren empty tile member
      · rw [admitted] at member
        cases Option.some.inj member
        exact not_walkable located walk
    · rcases member with member | member
      · exact searching.greatest other scored member
      · rw [admitted] at member
        have same : position = other.position := Option.some.inj member
        subst same
        exact absurd scored.walkable (not_walkable located walk)
  | scored position kind trees stone admitted located walk treeCount stoneCount chosen flag =>
    subst flag
    have fresh : Scored world ⟨position, trees + stone⟩ :=
      ⟨⟨kind, located, walk⟩, ⟨trees, stone, treeCount, stoneCount, rfl⟩⟩
    have held : ∀ candidate, selected = some candidate → Scored world candidate := by
      intro candidate same
      rcases chosen with ⟨-, picked⟩ | ⟨old, -, -, picked⟩ | ⟨old, was, -, picked⟩
      · rw [picked] at same
        cases Option.some.inj same
        exact fresh
      · rw [picked] at same
        cases Option.some.inj same
        exact fresh
      · rw [picked] at same
        cases Option.some.inj same
        exact searching.scored _ was
    have holding : selected ≠ none := by
      rcases chosen with ⟨-, picked⟩ | ⟨old, -, -, picked⟩ | ⟨old, -, -, picked⟩ <;>
        simp [picked]
    have greatest : ∀ other, Scored world other →
        (seen other.position ∨ BoxPosition.checked config x y = some other.position) →
        ∃ kept, selected = some kept ∧ other.score ≤ kept.score := by
      intro other scored member
      rcases member with member | member
      · obtain ⟨kept, was, least⟩ := searching.greatest other scored member
        rcases chosen with ⟨empty, picked⟩ | ⟨old, wasOld, better, picked⟩ |
          ⟨old, wasOld, worse, picked⟩
        · rw [empty] at was
          cases was
        · rw [wasOld] at was
          cases Option.some.inj was
          exact ⟨_, picked, by change other.score ≤ trees + stone; omega⟩
        · rw [wasOld] at was
          cases Option.some.inj was
          exact ⟨_, picked, least⟩
      · rw [admitted] at member
        have same : position = other.position := Option.some.inj member
        subst same
        have total := scored_score scored treeCount stoneCount
        rcases chosen with ⟨-, picked⟩ | ⟨old, -, -, picked⟩ | ⟨old, -, worse, picked⟩
        · exact ⟨_, picked, by change other.score ≤ trees + stone; omega⟩
        · exact ⟨_, picked, by change other.score ≤ trees + stone; omega⟩
        · exact ⟨old, picked, by omega⟩
    constructor
    · intro continues
      have few : ¬ 2 ≤ trees := of_decide_eq_false continues
      refine ⟨held, fun tile member => ?_, fun empty => absurd empty holding, greatest⟩
      rcases member with member | member
      · exact searching.poor tile member
      · rw [admitted] at member
        cases Option.some.inj member
        exact not_rich treeCount few
    · intro exit
      have enough : 2 ≤ trees := of_decide_eq_true exit
      rcases chosen with ⟨-, picked⟩ | ⟨old, -, better, picked⟩ | ⟨old, was, worse, picked⟩
      · exact ⟨_, picked, fresh, by change 2 ≤ trees + stone; omega⟩
      · exact ⟨_, picked, fresh, by change 2 ≤ trees + stone; omega⟩
      · exact ⟨old, picked, searching.scored old was, by omega⟩

def spiralX (config : WorldConfig) (radius directionIndex offset : Nat) : Int :=
  (config.side / 2 : Nat) +
    (Direction.fromIndex ⟨directionIndex % 4, Nat.mod_lt _ (by decide)⟩).delta.1 * radius +
    (Direction.fromIndex ⟨directionIndex % 4, Nat.mod_lt _ (by decide)⟩).delta.2 *
      ((offset : Int) - radius)

def spiralY (config : WorldConfig) (radius directionIndex offset : Nat) : Int :=
  (config.side / 2 : Nat) +
    (Direction.fromIndex ⟨directionIndex % 4, Nat.mod_lt _ (by decide)⟩).delta.2 * radius +
    (Direction.fromIndex ⟨directionIndex % 4, Nat.mod_lt _ (by decide)⟩).delta.1 *
      ((offset : Int) - radius)

theorem spiral_covers (config : WorldConfig) (tile : BoxPosition config) :
    ∃ radius directionIndex offset, radius < config.side ∧ directionIndex < 4 ∧
      offset < 2 * radius + 1 ∧
      BoxPosition.checked config (spiralX config radius directionIndex offset)
        (spiralY config radius directionIndex offset) = some tile := by
  have hx := tile.x.isLt
  have hy := tile.y.isLt
  obtain ⟨radius, ring⟩ : ∃ radius : Nat, radius =
      max ((tile.x.val : Int) - (config.side / 2 : Nat)).natAbs
        ((tile.y.val : Int) - (config.side / 2 : Nat)).natAbs := ⟨_, rfl⟩
  have found : ∀ directionIndex offset, directionIndex < 4 → offset < 2 * radius + 1 →
      spiralX config radius directionIndex offset = tile.x.val →
      spiralY config radius directionIndex offset = tile.y.val →
      ∃ radius directionIndex offset, radius < config.side ∧ directionIndex < 4 ∧
        offset < 2 * radius + 1 ∧
        BoxPosition.checked config (spiralX config radius directionIndex offset)
          (spiralY config radius directionIndex offset) = some tile := by
    intro directionIndex offset direction inside horizontal vertical
    refine ⟨radius, directionIndex, offset, by omega, direction, inside, ?_⟩
    rw [horizontal, vertical]
    exact BoxPosition.checked_position tile
  have edge : (tile.y.val : Int) - (config.side / 2 : Nat) = -(radius : Int) ∨
      (tile.y.val : Int) - (config.side / 2 : Nat) = radius ∨
      (tile.x.val : Int) - (config.side / 2 : Nat) = radius ∨
      (tile.x.val : Int) - (config.side / 2 : Nat) = -(radius : Int) := by omega
  rcases edge with edge | edge | edge | edge
  · refine found 0 ((radius : Int) - ((tile.x.val : Int) - (config.side / 2 : Nat))).toNat
      (by omega) (by omega) ?_ ?_
    · change _ + (0 : Int) * _ + (-1 : Int) * _ = _
      omega
    · change _ + (-1 : Int) * _ + (0 : Int) * _ = _
      omega
  · refine found 1 ((radius : Int) + ((tile.x.val : Int) - (config.side / 2 : Nat))).toNat
      (by omega) (by omega) ?_ ?_
    · change _ + (0 : Int) * _ + (1 : Int) * _ = _
      omega
    · change _ + (1 : Int) * _ + (0 : Int) * _ = _
      omega
  · refine found 2 ((radius : Int) + ((tile.y.val : Int) - (config.side / 2 : Nat))).toNat
      (by omega) (by omega) ?_ ?_
    · change _ + (1 : Int) * _ + (0 : Int) * _ = _
      omega
    · change _ + (0 : Int) * _ + (1 : Int) * _ = _
      omega
  · refine found 3 ((radius : Int) - ((tile.y.val : Int) - (config.side / 2 : Nat))).toNat
      (by omega) (by omega) ?_ ?_
    · change _ + (-1 : Int) * _ + (0 : Int) * _ = _
      omega
    · change _ + (0 : Int) * _ + (-1 : Int) * _ = _
      omega

def Before (radius direction offset radius' direction' offset' : Nat) : Prop :=
  radius' < radius ∨ (radius' = radius ∧ (direction' < direction ∨
    (direction' = direction ∧ offset' < offset)))

def Seen (config : WorldConfig) (radius direction offset : Nat) (tile : BoxPosition config) :
    Prop :=
  ∃ radius' direction' offset', direction' < 4 ∧ offset' < 2 * radius' + 1 ∧
    Before radius direction offset radius' direction' offset' ∧
    BoxPosition.checked config (spiralX config radius' direction' offset')
      (spiralY config radius' direction' offset') = some tile

theorem seen_start (config : WorldConfig) (tile : BoxPosition config) :
    ¬ Seen config 0 0 0 tile := by
  rintro ⟨radius', direction', offset', -, -, before, -⟩
  unfold Before at before
  omega

theorem seen_offset (config : WorldConfig) (radius direction offset : Nat)
    (tile : BoxPosition config) (seen : Seen config radius direction (offset + 1) tile) :
    Seen config radius direction offset tile ∨
      BoxPosition.checked config (spiralX config radius direction offset)
        (spiralY config radius direction offset) = some tile := by
  obtain ⟨radius', direction', offset', bounded, inside, before, admitted⟩ := seen
  unfold Before at before
  by_cases here : radius' = radius ∧ direction' = direction ∧ offset' = offset
  · obtain ⟨rfl, rfl, rfl⟩ := here
    exact Or.inr admitted
  · exact Or.inl ⟨radius', direction', offset', bounded, inside, by unfold Before; omega, admitted⟩

theorem seen_direction (config : WorldConfig) (radius direction : Nat) (tile : BoxPosition config)
    (seen : Seen config radius (direction + 1) 0 tile) :
    Seen config radius direction (2 * radius + 1) tile := by
  obtain ⟨radius', direction', offset', bounded, inside, before, admitted⟩ := seen
  unfold Before at before
  exact ⟨radius', direction', offset', bounded, inside, by unfold Before; omega, admitted⟩

theorem seen_radius (config : WorldConfig) (radius : Nat) (tile : BoxPosition config)
    (seen : Seen config (radius + 1) 0 0 tile) : Seen config radius 4 0 tile := by
  obtain ⟨radius', direction', offset', bounded, inside, before, admitted⟩ := seen
  unfold Before at before
  exact ⟨radius', direction', offset', bounded, inside, by unfold Before; omega, admitted⟩

theorem seen_all (config : WorldConfig) (tile : BoxPosition config) :
    Seen config config.side 0 0 tile := by
  obtain ⟨radius, direction, offset, ring, bounded, inside, admitted⟩ := spiral_covers config tile
  exact ⟨radius, direction, offset, bounded, inside, Or.inl ring, admitted⟩

def Exited {config : WorldConfig} (world : World config) (spawn : BoxPosition config) : Prop :=
  ∃ chosen, Scored world chosen ∧ chosen.position = spawn ∧ 2 ≤ chosen.score

theorem offset_step {config : WorldConfig} (world : World config)
    (radius direction offset : Nat) (best selected : Option (SpawnCandidate config))
    (finished : Bool) (x y : Int) (horizontal : x = spiralX config radius direction offset)
    (vertical : y = spiralY config radius direction offset)
    (searching : Searching world (Seen config radius direction offset) best)
    (h : considerSpawn world x y best = .ok (selected, finished)) :
    (finished = false → Searching world (Seen config radius direction (offset + 1)) selected) ∧
    (finished = true →
      Exited world ((selected.map (·.position)).getD (BoxPosition.center config))) := by
  obtain ⟨continues, exits⟩ :=
    search_step searching (considerSpawn_outcome world x y best selected finished h)
  subst horizontal vertical
  constructor
  · intro flag
    exact (continues flag).mono
      (fun tile seen => seen_offset config radius direction offset tile seen)
  · intro flag
    obtain ⟨chosen, picked, scored, enough⟩ := exits flag
    subst picked
    exact ⟨chosen, scored, rfl, enough⟩

theorem forIn_range'_indexed {ε σ : Type} (count : Nat) (inv : Nat → σ → Prop) (exit : σ → Prop)
    (body : Nat → σ → Except ε (ForInStep σ))
    (step : ∀ index state next, index < count → inv index state → body index state = .ok next →
      (∀ after, next = .yield after → inv (index + 1) after) ∧
        (∀ after, next = .done after → exit after)) :
    ∀ (remaining start : Nat) (init result : σ), start + remaining = count → inv start init →
      forIn (List.range' start remaining 1) init body = .ok result →
        exit result ∨ inv count result
  | 0, start, init, result, total, held, h => by
    simp only [List.range'_zero, List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    have same : start = count := by omega
    exact Or.inr (same ▸ held)
  | remaining + 1, start, init, result, total, held, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    cases taken : body start init with
    | error refusal => simp [taken, bind, Except.bind] at h
    | ok next =>
      obtain ⟨continues, exits⟩ := step start init next (by omega) held taken
      cases next with
      | done after =>
        simp only [taken, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact Or.inl (exits _ rfl)
      | yield after =>
        simp only [taken, bind, Except.bind] at h
        exact forIn_range'_indexed count inv exit body step remaining (start + 1) after result
          (by omega) (continues _ rfl) h

theorem forIn_range_indexed {ε σ : Type} (count : Nat) (inv : Nat → σ → Prop) (exit : σ → Prop)
    (body : Nat → σ → Except ε (ForInStep σ))
    (step : ∀ index state next, index < count → inv index state → body index state = .ok next →
      (∀ after, next = .yield after → inv (index + 1) after) ∧
        (∀ after, next = .done after → exit after))
    (init result : σ) (start : inv 0 init) (h : forIn [:count] init body = .ok result) :
    exit result ∨ inv count result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  have size : ([:count] : Std.Legacy.Range).size = count := by simp [Std.Legacy.Range.size]
  rw [size] at h
  exact forIn_range'_indexed count inv exit body step count 0 init result (by omega) start h

theorem bind_ok {ε α β : Type} (first : Except ε α) (rest : α → Except ε β) (result : β)
    (h : (first >>= rest) = .ok result) :
    ∃ middle, first = .ok middle ∧ rest middle = .ok result := by
  cases first with
  | error refusal => simp [bind, Except.bind] at h
  | ok middle => exact ⟨middle, rfl, h⟩

def reads {config : WorldConfig} (world : World config) (position : Position) (radius : Nat)
    (kind : TileKind) (row column : Nat) : Bool :=
  match position.translate ((column : Int) - radius) ((row : Int) - radius) with
  | some tile =>
    match world.tileKind tile with
    | .ok found => found == kind
    | .error _ => false
  | none => false

def rowCount {config : WorldConfig} (world : World config) (position : Position) (radius : Nat)
    (kind : TileKind) (row : Nat) : Nat → Nat
  | 0 => 0
  | columns + 1 => rowCount world position radius kind row columns +
      if reads world position radius kind row columns then 1 else 0

def squareCount {config : WorldConfig} (world : World config) (position : Position)
    (radius : Nat) (kind : TileKind) : Nat → Nat
  | 0 => 0
  | rows + 1 => squareCount world position radius kind rows +
      rowCount world position radius kind rows (2 * radius + 1)

theorem countKindNear_eq {config : WorldConfig} (world : World config) (position : Position)
    (radius count : Nat) (kind : TileKind)
    (h : countKindNear world position radius kind = .ok count) :
    count = squareCount world position radius kind (2 * radius + 1) := by
  unfold countKindNear at h
  dsimp only at h
  obtain ⟨total, outer, rest⟩ := bind_ok _ _ _ h
  simp only [pure, Except.pure, Except.ok.injEq] at rest
  subst rest
  suffices closing : False ∨ total = squareCount world position radius kind (2 * radius + 1) by
    rcases closing with impossible | same
    · exact impossible.elim
    · exact same
  refine forIn_range_indexed (2 * radius + 1)
    (fun rows state => state = squareCount world position radius kind rows) (fun _ => False)
    _ ?_ _ total rfl outer
  intro row state next _ held taken
  obtain ⟨sum, inner, rest⟩ := bind_ok _ _ _ taken
  simp only [pure, Except.pure, Except.ok.injEq] at rest
  subst rest
  suffices closing : False ∨
      sum = state + rowCount world position radius kind row (2 * radius + 1) by
    refine ⟨fun after same => ?_, fun after same => ?_⟩
    · cases same
      rcases closing with impossible | same
      · exact impossible.elim
      · rw [same, held]
        rfl
    · cases same
  refine forIn_range_indexed (2 * radius + 1)
    (fun columns count => count = state + rowCount world position radius kind row columns)
    (fun _ => False) _ ?_ _ sum rfl inner
  intro column count next _ held taken
  split at taken
  · rename_i tile translated
    obtain ⟨found, located, rest⟩ := bind_ok _ _ _ taken
    have read : reads world position radius kind row column = (found == kind) := by
      simp only [reads, translated, located]
    by_cases same : (found == kind) = true
    · simp only [same, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      refine ⟨fun after eq => ?_, fun after eq => ?_⟩
      · cases eq
        rw [held]
        simp only [rowCount, read, same, ↓reduceIte]
        omega
      · cases eq
    · have off : (found == kind) = false := Bool.eq_false_iff.mpr same
      simp only [off, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      refine ⟨fun after eq => ?_, fun after eq => ?_⟩
      · cases eq
        rw [held]
        simp only [rowCount, read, off, Bool.false_eq_true, ↓reduceIte]
        omega
      · cases eq
  · simp [bind, Except.bind] at taken

def Open {config : WorldConfig} (world : World config) (seen : BoxPosition config → Prop)
    (state : Option (BoxPosition config) × Option (SpawnCandidate config)) : Prop :=
  state.1 = none ∧ Searching world seen state.2

def Closed {config : WorldConfig} (world : World config)
    (state : Option (BoxPosition config) × Option (SpawnCandidate config)) : Prop :=
  ∃ spawn, state.1 = some spawn ∧ Exited world spawn

theorem selectSpawn_post {config : WorldConfig} (world : World config)
    (spawn : BoxPosition config) (h : selectSpawn world = .ok spawn) :
    Exited world spawn ∨
      ((∀ tile, ¬ Rich world tile) ∧
        ((∃ chosen, Scored world chosen ∧ chosen.position = spawn ∧
            ∀ other, Scored world other → other.score ≤ chosen.score) ∨
          (spawn = BoxPosition.center config ∧ ∀ tile, ¬ Walkable world tile))) := by
  unfold selectSpawn at h
  dsimp only at h
  obtain ⟨final, outer, rest⟩ := bind_ok _ _ _ h
  suffices closing : Closed world final ∨ Open world (Seen config config.side 0 0) final by
    obtain ⟨early, best⟩ := final
    rcases closing with ⟨exit, isEarly, exited⟩ | ⟨isOpen, searching⟩
    · dsimp only at isEarly rest
      subst isEarly
      simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      exact Or.inl exited
    · dsimp only at isOpen rest searching
      subst isOpen
      simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      refine Or.inr ⟨fun tile => searching.poor tile (seen_all config tile), ?_⟩
      cases best with
      | none =>
        exact Or.inr ⟨rfl, fun tile => searching.barren rfl tile (seen_all config tile)⟩
      | some chosen =>
        refine Or.inl ⟨chosen, searching.scored chosen rfl, rfl, fun other scored => ?_⟩
        obtain ⟨kept, was, least⟩ :=
          searching.greatest other scored (seen_all config other.position)
        cases Option.some.inj was
        exact least
  have start : Open world (Seen config 0 0 0) (none, none) :=
    ⟨rfl, fun candidate same => (by cases same),
      fun tile seen => absurd seen (seen_start config tile),
      fun _ tile seen => absurd seen (seen_start config tile),
      fun other _ seen => absurd seen (seen_start config other.position)⟩
  refine forIn_range_indexed config.side
    (fun radius state => Open world (Seen config radius 0 0) state) (Closed world) _ ?_ _ final
    start outer
  intro radius state next _ held taken
  obtain ⟨ring, middle, rest⟩ := bind_ok _ _ _ taken
  suffices closing : Closed world ring ∨ Open world (Seen config radius 4 0) ring by
    obtain ⟨early, best⟩ := ring
    rcases closing with ⟨exit, isEarly, exited⟩ | ⟨isOpen, searching⟩
    · dsimp only at isEarly rest
      subst isEarly
      simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      refine ⟨fun after same => ?_, fun after same => ?_⟩
      · cases same
      · cases same
        exact ⟨exit, rfl, exited⟩
    · dsimp only at isOpen rest searching
      subst isOpen
      simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      refine ⟨fun after same => ?_, fun after same => ?_⟩
      · cases same
        exact ⟨rfl, searching.mono (seen_radius config radius)⟩
      · cases same
  have start : Open world (Seen config radius 0 0) (none, state.2) := ⟨rfl, held.2⟩
  refine forIn_range_indexed 4
    (fun direction state => Open world (Seen config radius direction 0) state) (Closed world)
    _ ?_ _ ring start middle
  intro direction state next _ held taken
  obtain ⟨edge, inner, rest⟩ := bind_ok _ _ _ taken
  suffices closing : Closed world edge ∨
      Open world (Seen config radius direction (2 * radius + 1)) edge by
    obtain ⟨early, best⟩ := edge
    rcases closing with ⟨exit, isEarly, exited⟩ | ⟨isOpen, searching⟩
    · dsimp only at isEarly rest
      subst isEarly
      simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      refine ⟨fun after same => ?_, fun after same => ?_⟩
      · cases same
      · cases same
        exact ⟨exit, rfl, exited⟩
    · dsimp only at isOpen rest searching
      subst isOpen
      simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      refine ⟨fun after same => ?_, fun after same => ?_⟩
      · cases same
        exact ⟨rfl, searching.mono (seen_direction config radius direction)⟩
      · cases same
  have start : Open world (Seen config radius direction 0) (none, state.2) := ⟨rfl, held.2⟩
  refine forIn_range_indexed (2 * radius + 1)
    (fun offset state => Open world (Seen config radius direction offset) state)
    (Closed world) _ ?_ _ edge start inner
  intro offset state next _ held taken
  obtain ⟨pair, considered, rest⟩ := bind_ok _ _ _ taken
  obtain ⟨selected, finished⟩ := pair
  dsimp only at rest
  have step := offset_step world radius direction offset state.2 selected finished
    _ _ rfl rfl held.2 considered
  cases finished with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
    subst rest
    refine ⟨fun after same => ?_, fun after same => ?_⟩
    · cases same
      exact ⟨rfl, step.1 rfl⟩
    · cases same
  | true =>
    simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
    subst rest
    refine ⟨fun after same => ?_, fun after same => ?_⟩
    · cases same
    · cases same
      exact ⟨_, rfl, step.2 rfl⟩

theorem spawn_of_rich {config : WorldConfig} (world : World config) (spawn : BoxPosition config)
    (h : selectSpawn world = .ok spawn) (tile : BoxPosition config) (rich : Rich world tile) :
    Exited world spawn := by
  rcases selectSpawn_post world spawn h with exited | ⟨poor, -⟩
  · exact exited
  · exact absurd rich (poor tile)

theorem spawn_walkable {config : WorldConfig} (world : World config) (spawn : BoxPosition config)
    (h : selectSpawn world = .ok spawn) (tile : BoxPosition config)
    (walkable : Walkable world tile) : Walkable world spawn := by
  rcases selectSpawn_post world spawn h with
    ⟨chosen, scored, same, -⟩ | ⟨-, ⟨chosen, scored, same, -⟩ | ⟨-, barren⟩⟩
  · exact same ▸ scored.walkable
  · exact same ▸ scored.walkable
  · exact absurd walkable (barren tile)

theorem initial_spawn (config : WorldConfig) (world : World config)
    (h : World.initial config = .ok world) :
    selectSpawn (World.empty config) = .ok world.body.position := by
  unfold World.initial at h
  cases hadm : config.raw.admissible with
  | false => simp [hadm, bind, Except.bind] at h
  | true =>
    simp only [hadm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h
    cases hs : selectSpawn (World.empty config) with
    | error error => simp [hs] at h
    | ok position =>
      simp only [hs] at h
      cases hd : initializeDeer (World.empty config) with
      | error error => simp [hd] at h
      | ok pair =>
        simp only [hd, pure, Except.pure, Except.ok.injEq] at h
        rw [← h]

end AcornVerif.CurrentSpawn
