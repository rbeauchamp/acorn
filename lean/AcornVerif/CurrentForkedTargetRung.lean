/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetRung
import AcornVerif.CurrentExplorer
import AcornVerif.CurrentForkedTarget
import AcornVerif.CurrentFrameSlots
import AcornVerif.CurrentTerrain

/-!
# The rung of concealed targets by day and by night

This module fixes the class of `AcornVerif.CurrentForkedTarget.forkedFind` in the first rung's
world and proves that its promises can be met.

**The two situations.** The first is the first rung's start, `witnessLive`: the host's empty
world of the witness configuration, whose clock reads zero, the first phase of the day. The
second, `duskLive`, is the same world with its clock at 1024, the day's midpoint, where the
fifth of the day's eight phases begins. The two differ in the clock alone, so the body stands on
one tile in both (`dusk_start`). A frame carries the phase of the day as a word on the channel
`0x41` (`Acorn.Handcrafted.sensorWords`), and `showsDusk` reads it: at a start of the first
situation it is not set, and at a start of the second it is (`dawn_shown`, `dusk_shown`). The
second needs the host's observation to succeed there, which it does at every world of the
configuration whose body stands at the center (`centered_observes`): each tile of the window
translates inside the signed range and the value noise admits it. The kernel evaluates the
quotients of eleven coordinates by four scales (`window_admits`), and no terrain.

**The members.** `rungForks mode` is the class with visits of seven steps. `rungPairs` lists 147
of its members with 147 different first targets (`rungPairs_card`, `rungPairs_distinct`): each
tile within three of the three end tiles of the witness's walks is a first target, paired with a
second target chosen so that the two ask together for eight moves, one more than a visit has.
A first target east of the start is paired with the tile fourteen to its west, one to the west
with the tile fourteen to its east, and one to the south, at `(x, y)`, with the tile
`(78 - y, x)` to the east (`partner`). Each second target is met from `duskLive` by seven steps
east or west, which the kernel evaluates (`dusk_walk`).

**An agent that meets both promises.** `forkWitness` is the switch of
`AcornVerif.Kernel.switch` over two replaying agents, one for each situation, with `showsDusk` as
its reading of the situation and the achievement flag as the replaying agents' signal. It keeps
with no lapse before every horizon (`witness_keeps`), and under the order that alternates the two
situations it solves, on visit 5, each of the 147 members in both situations (`witness_masters`).
It is evidence that the promises are satisfiable, built for that purpose: it reads the percept at
the first decision of each visit and follows a stored route by its own count for the rest, and it
chooses by no learned value.
-/

namespace AcornVerif.CurrentForkedTargetRung
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentForkedTarget

/-! ## The second situation -/

/-- The live state of the second situation: the witness's world with its clock at the day's
midpoint, and an empty carried result. -/
def duskLive : Live witnessConfig :=
  ⟨{ Host.World.empty witnessConfig with time := 1024 }, {}⟩

/-- In the second situation the body starts on the first's tile, the center `(32, 32)`. -/
theorem dusk_start : tile duskLive.world.body.position.position = (32, 32) := by
  decide +kernel

/-- The first situation starts in the day's first phase. -/
theorem dawn_phase : witnessLive.world.dayPhase.val = 0 := by
  decide +kernel

/-- The second situation starts in the day's fifth phase, the first of its second half. -/
theorem dusk_phase : duskLive.world.dayPhase.val = 4 := by
  decide +kernel

/-- The two situations carry one result. -/
theorem dusk_carried : witnessLive.carried = duskLive.carried := rfl

/-! ## The host observes at the center -/

/-- A success holds a value. -/
theorem ok_of_isOk {ε α : Type} {result : Except ε α} (accepted : result.isOk = true) :
    ∃ value, result = .ok value := by
  cases result with
  | error error => exact absurd accepted (by simp [Except.isOk, Except.toBool])
  | ok value => exact ⟨value, rfl⟩

/-- A vector made by a fallible function succeeds where each of its entries succeeds. -/
theorem ofFnM_isOk {ε α : Type} {n : Nat} (f : Fin n → Except ε α)
    (each : ∀ index, (f index).isOk = true) : (Vector.ofFnM f).isOk = true := by
  have values : f = fun index => pure (Classical.choose (ok_of_isOk (each index))) :=
    funext fun index => Classical.choose_spec (ok_of_isOk (each index))
  rw [values, Vector.ofFnM_pure]
  rfl

/-- The observation of a world succeeds where each tile of its window translates inside the
signed range and the value noise admits the tile at the noise scale of the world
(`CurrentTerrain.tileKind_isOk`). -/
theorem observe_isOk {config : Host.WorldConfig} (world : Host.World config)
    (window : ∀ row column : Fin Host.patchSide, ∃ tile,
      world.body.position.position.translate ((column.val : Int) - (Host.patchSide / 2 : Nat))
          ((row.val : Int) - (Host.patchSide / 2 : Nat)) = some tile ∧
        CurrentTerrain.LatticeAdmits tile config.raw.baseScale) :
    world.observe.isOk = true := by
  have tiles : ∀ row column, (world.observeTile world.occupancy row column).isOk = true := by
    intro row column
    obtain ⟨tile, translated, admits⟩ := window row column
    obtain ⟨kind, kinded⟩ := ok_of_isOk ((CurrentTerrain.tileKind_isOk world tile).mpr admits)
    unfold Host.World.observeTile
    simp only [translated, kinded]
    rfl
  obtain ⟨rows, built⟩ := ok_of_isOk (ofFnM_isOk _ fun row => ofFnM_isOk _ (tiles row))
  unfold Host.World.observe
  simp only [built, bind, Except.bind, pure, Except.pure]
  rfl

/-- Each coordinate of the window around the center, 27 to 37, has a quotient by each octave
scale of the witness's noise scale that is not past the last coordinate. The kernel evaluates the
forty-four quotients. -/
theorem window_admits : ∀ offset : Fin Host.patchSide, ∀ octave : Fin 4,
    ¬CurrentTerrain.PastLast
      ((Host.coordinateFloatWord (Int64.ofInt (27 + offset.val))).div
        (CurrentTerrain.octaveScale ⟨0x41000000⟩ octave.val)) := by
  decide +kernel

/-- **The host observes every world of the witness configuration whose body stands at the
center**, whatever its clock, its goal and what it holds: each tile of the window translates
inside the signed range, and the value noise admits it. No terrain is evaluated. -/
theorem centered_observes (world : Host.World witnessConfig)
    (centered : world.body.position = (Host.World.empty witnessConfig).body.position) :
    world.observe.isOk = true := by
  have center : ((Host.World.empty witnessConfig).body.position.x.val : Int) = 32 ∧
      ((Host.World.empty witnessConfig).body.position.y.val : Int) = 32 := by decide
  have radius : ((Host.patchSide / 2 : Nat) : Int) = 5 := rfl
  refine observe_isOk _ fun row column => ?_
  have columnBound := column.isLt
  have rowBound := row.isLt
  have side : Host.patchSide = 11 := rfl
  refine ⟨⟨⟨27 + column.val, by omega⟩, ⟨27 + row.val, by omega⟩⟩,
    CurrentCertificates.translate_of_eq _ _ _ _ ?_ ?_,
    fun octave below => ⟨window_admits column ⟨octave, below⟩, window_admits row ⟨octave, below⟩⟩⟩
  · rw [centered]
    change (27 + column.val : Int) =
      ((Host.World.empty witnessConfig).body.position.x.val : Int) + _
    rw [center.1]
    omega
  · rw [centered]
    change (27 + row.val : Int) =
      ((Host.World.empty witnessConfig).body.position.y.val : Int) + _
    rw [center.2]
    omega

/-- An observation the host makes reports the world's day phase. -/
theorem observe_day {config : Host.WorldConfig} (world : Host.World config)
    (observation : Host.Observation) (seen : world.observe = .ok observation) :
    observation.day = world.dayPhase.val.toUInt8 := by
  unfold Host.World.observe at seen
  cases tiles : Vector.ofFnM (fun row => Vector.ofFnM (world.observeTile world.occupancy row))
    with
  | error refusal => simp [tiles, bind, Except.bind] at seen
  | ok tiles =>
    simp only [tiles, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at seen
    cases seen
    rfl

/-! ## Reading the situation from a percept -/

/-- The value of the first word a percept's frame carries on the channel of the day's phase. -/
def dayWord (percept : Percept Grid.interface) : Option UInt64 :=
  (percept.frame.words.find? (fun word => word.channel == 0x41)).map (·.value)

/-- Whether a percept shows the day's fifth phase, in which the second situation starts. -/
def showsDusk (percept : Percept Grid.interface) : Bool :=
  dayWord percept == some 4

/-- No word of a tile is on the channel of the day's phase. -/
theorem tileWords_channel (row col : Fin Host.patchSide) (tile : Host.TileObservation)
    (word : SensorWord) (member : word ∈ tileWords row col tile) :
    (word.channel == 0x41) = false := by
  unfold tileWords at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (rfl | food) | deer
  · rfl
  · split at food
    · rw [List.mem_singleton] at food
      subst food
      rfl
    · cases food
  · split at deer
    · rw [List.mem_singleton] at deer
      subst deer
      rfl
    · cases deer

/-- **A grid percept's day word is its observation's day phase.** The frame's first word on the
channel of the day's phase is the one the observation's phase supplies: the words before it are
those of the window's tiles and of the body's energy. -/
theorem dayWord_percept (mode : TaskFeatureMode) (observation : Host.Observation)
    (reward : Binary32) (achieved : Bool) :
    dayWord (Grid.percept mode observation reward achieved) =
      some observation.day.toUInt64 := by
  have tiles : ((List.finRange Host.patchSide).flatMap (fun row =>
      (List.finRange Host.patchSide).flatMap fun col =>
        tileWords row col ((observation.tiles.get row).get col))).find?
        (fun word => word.channel == 0x41) = none := by
    rw [List.find?_eq_none]
    intro word member
    obtain ⟨row, -, inRow⟩ := List.mem_flatMap.mp member
    obtain ⟨col, -, inTile⟩ := List.mem_flatMap.mp inRow
    rw [tileWords_channel row col _ word inTile]
    exact Bool.false_ne_true
  change ((sensorWords observation mode).find? (fun word => word.channel == 0x41)).map
    (·.value) = _
  unfold sensorWords
  rw [List.append_assoc, List.append_assoc, List.find?_append, tiles]
  rfl

/-- A percept of a live state whose sensed observation reports a day phase carries that phase as
its day word. -/
theorem dayWord_live (mode : TaskFeatureMode) (live : Live witnessConfig) :
    dayWord ((gridWorld witnessConfig mode).percept (some live)) =
      some (sensed live.world).day.toUInt64 :=
  dayWord_percept mode (sensed live.world) live.carried.reward live.carried.events.done

/-- At a start of the first situation the sensed observation reports the day's first phase: the
host's observation reports it, and the blank observation that stands in where the host refuses
reports it too. -/
theorem dawn_day (target : Host.Position) :
    (sensed (witnessLive.world.setGoal (.find target))).day = 0 := by
  rcases CurrentFrameSlots.sensed_day (witnessLive.world.setGoal (.find target)) with day | day
  · have phase : (witnessLive.world.setGoal (.find target)).dayPhase =
        witnessLive.world.dayPhase := rfl
    rw [day, phase, dawn_phase]
    rfl
  · exact day

/-- **A start of the first situation does not show the fifth phase.** Whatever target is
installed, the percept at the first situation's start carries the word of the day's first
phase. -/
theorem dawn_shown (mode : TaskFeatureMode) (target : Host.Position) :
    showsDusk ((gridWorld witnessConfig mode).percept (member witnessLive target)) = false := by
  change (dayWord ((gridWorld witnessConfig mode).percept
    (some ⟨witnessLive.world.setGoal (.find target), witnessLive.carried⟩)) == some 4) = false
  rw [dayWord_live, dawn_day]
  rfl

/-- **A start of the second situation shows the fifth phase.** Whatever target is installed, the
host observes the second situation's start (`centered_observes`), and its observation reports the
day's fifth phase. -/
theorem dusk_shown (mode : TaskFeatureMode) (target : Host.Position) :
    showsDusk ((gridWorld witnessConfig mode).percept (member duskLive target)) = true := by
  obtain ⟨observation, seen⟩ := ok_of_isOk
    (centered_observes (duskLive.world.setGoal (.find target)) rfl)
  have day : (sensed (duskLive.world.setGoal (.find target))).day = 4 := by
    have phase : (duskLive.world.setGoal (.find target)).dayPhase =
        duskLive.world.dayPhase := rfl
    rw [sensed_ok _ observation seen, observe_day _ observation seen, phase, dusk_phase]
    rfl
  change (dayWord ((gridWorld witnessConfig mode).percept
    (some ⟨duskLive.world.setGoal (.find target), duskLive.carried⟩)) == some 4) = true
  rw [dayWord_live, day]
  rfl

/-! ## The rung's class and 147 of its members -/

/-- The rung's class: concealed targets in the two situations, with visits of seven steps. -/
abbrev rungForks (mode : TaskFeatureMode) : Kernel.TurnClass Grid.interface :=
  forkedFind witnessConfig mode witnessLive duskLive 7

/-- The goal of every member of the rung's class, in both situations. -/
abbrev rungForkGoals (mode : TaskFeatureMode) : (rungForks mode).Goals :=
  forkedGoals witnessConfig mode witnessLive duskLive 7

/-- Seven steps east, and seven steps west, carry the body from the second situation's start to
the end tiles of the witness's first two walks. The kernel evaluates the executed world step
along the two walks. -/
theorem dusk_walk (visit : ℕ) (within : visit ≤ 1) :
    (physicalPath (physical duskLive.world) (witnessExplore visit) 7).map
      (fun world => tile world.body.position.position) = some (witnessEnd visit) := by
  rcases (by omega : visit = 0 ∨ visit = 1) with rfl | rfl
  · decide +kernel
  · decide +kernel

/-- The tile of the second target paired with a first target's tile. East of the start it is the
tile fourteen to the west, west of the start the tile fourteen to the east, and south of the
start, at `(x, y)`, the tile `(78 - y, x)` to the east. -/
def partner (point : ℤ × ℤ) : ℤ × ℤ :=
  if 36 ≤ point.1 then (point.1 - 14, point.2)
  else if point.1 ≤ 28 then (point.1 + 14, point.2)
  else (78 - point.2, point.1)

/-- A lattice point near the box is the tile of its position. -/
theorem tile_point (point : ℤ × ℤ)
    (small : -100 ≤ point.1 ∧ point.1 ≤ 100 ∧ -100 ≤ point.2 ∧ point.2 ≤ 100) :
    tile (pointPosition point) = point := by
  refine Prod.ext ?_ ?_ <;> simp only [tile, pointPosition, clampCoordinate] <;> omega

/-- Where a tile of the witness lies, and where its partner then lies: east of the start with
its partner west, west with its partner east, or south with its partner east. -/
theorem partner_cases (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    (36 ≤ point.1 ∧ point.1 ≤ 42 ∧ 29 ≤ point.2 ∧ point.2 ≤ 35 ∧
        partner point = (point.1 - 14, point.2)) ∨
      (22 ≤ point.1 ∧ point.1 ≤ 28 ∧ 29 ≤ point.2 ∧ point.2 ≤ 35 ∧
        partner point = (point.1 + 14, point.2)) ∨
      (29 ≤ point.1 ∧ point.1 ≤ 35 ∧ 36 ≤ point.2 ∧ point.2 ≤ 42 ∧
        partner point = (78 - point.2, point.1)) := by
  obtain ⟨visit, within, near⟩ := witnessTiles_near point inside
  rw [mem_box] at near
  rcases (by omega : visit = 0 ∨ visit = 1 ∨ visit = 2) with rfl | rfl | rfl <;>
    simp only [witnessEnd] at near
  · refine Or.inl ⟨by omega, by omega, by omega, by omega, ?_⟩
    unfold partner
    rw [ite_eq_left (by omega)]
  · refine Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, ?_⟩)
    unfold partner
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  · refine Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega, ?_⟩)
    unfold partner
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A partner is the tile of its position, lies more than three tiles from the start, and lies
within three tiles of the end tile of the witness's walk east or west. -/
theorem partner_spec (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    tile (pointPosition (partner point)) = partner point ∧ partner point ∉ box 3 (32, 32) ∧
      ∃ visit, visit ≤ 1 ∧ partner point ∈ box 3 (witnessEnd visit) := by
  rcases partner_cases point inside with ⟨_, _, _, _, value⟩ | ⟨_, _, _, _, value⟩ |
    ⟨_, _, _, _, value⟩
  · rw [value]
    refine ⟨tile_point _ ⟨by omega, by omega, by omega, by omega⟩, fun close => ?_,
      1, Nat.le_refl 1, ?_⟩
    · rw [mem_box] at close
      omega
    · rw [mem_box]
      simp only [witnessEnd]
      omega
  · rw [value]
    refine ⟨tile_point _ ⟨by omega, by omega, by omega, by omega⟩, fun close => ?_,
      0, Nat.zero_le 1, ?_⟩
    · rw [mem_box] at close
      omega
    · rw [mem_box]
      simp only [witnessEnd]
      omega
  · rw [value]
    refine ⟨tile_point _ ⟨by omega, by omega, by omega, by omega⟩, fun close => ?_,
      0, Nat.zero_le 1, ?_⟩
    · rw [mem_box] at close
      omega
    · rw [mem_box]
      simp only [witnessEnd]
      omega

/-- A tile of the witness is a concealed target of the first situation: the start's goal box
does not hold it. -/
theorem first_admitted (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    ¬ InGoalBox (pointPosition point) witnessLive.world.body.position.position := by
  rw [member_tile, witness_start, (witnessTiles_admitted point inside).1]
  exact (witnessTiles_admitted point inside).2

/-- A tile of the witness is met within a visit from the first situation's start. -/
theorem first_feasible (mode : TaskFeatureMode) (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    Kernel.Feasible (completion witnessConfig mode 7)
      (member witnessLive (pointPosition point)) := by
  obtain ⟨visit, within, near⟩ := witnessTiles_near point inside
  refine ⟨witnessExplore visit, 7, by omega, Nat.le_refl 7,
    witness_meets mode 7 visit within _ ?_⟩
  rw [(witnessTiles_admitted point inside).1]
  exact near

/-- A partner is a concealed target of the second situation. -/
theorem second_admitted (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    ¬ InGoalBox (pointPosition (partner point)) duskLive.world.body.position.position := by
  rw [member_tile, dusk_start, (partner_spec point inside).1]
  exact (partner_spec point inside).2.1

/-- A partner is met within a visit from the second situation's start. -/
theorem second_feasible (mode : TaskFeatureMode) (point : ℤ × ℤ)
    (inside : point ∈ witnessTiles) :
    Kernel.Feasible (completion witnessConfig mode 7)
      (member duskLive (pointPosition (partner point))) := by
  obtain ⟨same, -, visit, within, near⟩ := partner_spec point inside
  refine ⟨witnessExplore visit, 7, by omega, Nat.le_refl 7,
    find_near_met mode duskLive 7 (witnessExplore visit) 7 (witnessEnd visit)
      (dusk_walk visit within) _ ?_⟩
  rw [same]
  exact near

/-- **A tile of the witness and its partner are apart.** No single action sequence meets, within
a visit, the tile's target from the first situation's start and its partner's from the second's:
the two ask together for eight actions that name two different directions, and a visit has
seven. -/
theorem pair_apart (mode : TaskFeatureMode) (point : ℤ × ℤ) (inside : point ∈ witnessTiles)
    (actions : ℕ → Kernel.Act Grid.interface) :
    ¬ ((completion witnessConfig mode 7).MetBy (member witnessLive (pointPosition point))
        actions ∧
      (completion witnessConfig mode 7).MetBy (member duskLive (pointPosition (partner point)))
        actions) := by
  rintro ⟨one, two⟩
  have first := met_takes mode witnessLive 7 actions _ one
  have second := met_takes mode duskLive 7 actions _ two
  rw [witness_start, (witnessTiles_admitted point inside).1] at first
  rw [dusk_start, (partner_spec point inside).1] at second
  have eastWest := taken_pair actions .east .west (by decide) 7
  have southEast := taken_pair actions .south .east (by decide) 7
  rcases partner_cases point inside with ⟨_, _, _, _, value⟩ | ⟨_, _, _, _, value⟩ |
    ⟨_, _, _, _, value⟩ <;>
  · rw [value] at second
    dsimp only at first second
    omega

/-- The member of the first situation's feasible targets at a tile of the witness. -/
def firstIndex (mode : TaskFeatureMode) (point : { point // point ∈ witnessTiles }) :
    (feasibleFind witnessConfig mode witnessLive 7).Index :=
  ⟨⟨pointPosition point.1, first_admitted point.1 point.2⟩, first_feasible mode point.1 point.2⟩

/-- The member of the second situation's feasible targets at the partner of a tile of the
witness. -/
def secondIndex (mode : TaskFeatureMode) (point : { point // point ∈ witnessTiles }) :
    (feasibleFind witnessConfig mode duskLive 7).Index :=
  ⟨⟨pointPosition (partner point.1), second_admitted point.1 point.2⟩,
    second_feasible mode point.1 point.2⟩

/-- The member of the rung's class whose first target is a tile of the witness and whose second
is that tile's partner. -/
def rungPair (mode : TaskFeatureMode) (point : { point // point ∈ witnessTiles }) :
    (rungForks mode).Index :=
  ⟨(firstIndex mode point, secondIndex mode point), pair_apart mode point.1 point.2⟩

/-- Members at different tiles of the witness have different first targets. -/
theorem rungPair_key (mode : TaskFeatureMode) (one two : { point // point ∈ witnessTiles })
    (same : firstTarget mode witnessLive duskLive 7 (rungPair mode one) =
      firstTarget mode witnessLive duskLive 7 (rungPair mode two)) : one = two := by
  have tiles := congrArg
    (fun target : (feasibleFind witnessConfig mode witnessLive 7).Index => tile target.1.1) same
  change tile (pointPosition one.1) = tile (pointPosition two.1) at tiles
  rw [(witnessTiles_admitted one.1 one.2).1, (witnessTiles_admitted two.1 two.2).1] at tiles
  exact Subtype.ext tiles

/-- Different tiles of the witness give different members. -/
theorem rungPair_injective (mode : TaskFeatureMode) : Function.Injective (rungPair mode) :=
  fun one two same => rungPair_key mode one two
    (congrArg (firstTarget mode witnessLive duskLive 7) same)

/-- 147 members of the rung's class: one for each tile within three of the end tiles of the
witness's three walks. -/
def rungPairs (mode : TaskFeatureMode) : Finset (rungForks mode).Index :=
  witnessTiles.attach.map ⟨rungPair mode, rungPair_injective mode⟩

/-- The listed members number 147, more than the covering bound of 98. -/
theorem rungPairs_card (mode : TaskFeatureMode) : (rungPairs mode).card = 147 := by
  rw [rungPairs, Finset.card_map, Finset.card_attach, card_witnessTiles]

/-- No two of the listed members have one first target. -/
theorem rungPairs_distinct (mode : TaskFeatureMode) :
    ∀ one ∈ rungPairs mode, ∀ two ∈ rungPairs mode,
      firstTarget mode witnessLive duskLive 7 one =
        firstTarget mode witnessLive duskLive 7 two → one = two := by
  intro one inOne two inTwo same
  obtain ⟨first, -, rfl⟩ := Finset.mem_map.mp inOne
  obtain ⟨second, -, rfl⟩ := Finset.mem_map.mp inTwo
  exact congrArg (rungPair mode) (rungPair_key mode first second same)

/-! ## An agent that meets both promises -/

/-- Evidence that the promises are satisfiable, built for that purpose: the switch over two
replaying agents, one for each situation, each exploring east, then west, then south on its own
visits. It reads the situation from the first percept of each visit and follows a stored route by
its own count for the rest. -/
def forkWitness : Kernel.Agent Grid.interface :=
  Kernel.switch showsDusk 7
    (fun _ => Kernel.replay Grid.interface 7 achievedSignal witnessExplore)

/-- The percept at each start of each member shows its situation. -/
theorem witness_reads (mode : TaskFeatureMode) (pair : (rungForks mode).Index)
    (situation : Bool) :
    showsDusk (((rungForks mode).world pair).percept ((rungForks mode).start pair situation)) =
      situation := by
  cases situation
  · exact dawn_shown mode pair.1.1.1.1
  · exact dusk_shown mode pair.1.2.1.1

/-- **The witness keeps with no lapse**, before every horizon: under every order, a member it
has solved on a visit it solves on every later visit that brings the same situation. -/
theorem witness_keeps (mode : TaskFeatureMode) (horizon : ℕ) :
    Kernel.KeepsBut (rungForks mode) (rungForkGoals mode) 7 horizon 0 forkWitness :=
  Kernel.switch_keeps (rungForks mode) (rungForkGoals mode) 7 showsDusk _ (witness_reads mode)
    (fun situation index visit later after solved =>
      Kernel.replay_solves ((rungForks mode).side situation) (rungForkGoals mode) 7
        achievedSignal witnessExplore index (achieved_decodes witnessConfig mode 7) visit later
        after solved)
    horizon

/-- The order that alternates the two situations, the first on the even visits. -/
def alternate (visit : ℕ) : Bool :=
  decide (visit % 2 = 1)

/-- **The witness masters.** Under the alternating order, on visit 5, it solves each of the 147
listed members whichever situation that visit brings: by then each situation's replaying agent
has explored east, west and, in the first situation, south, and replays what met the target. So
the two promises hold together of one agent, at the covering bound 98 and before visit 6. -/
theorem witness_masters (mode : TaskFeatureMode) :
    Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 (49 + 7 * 7)
      (firstTarget mode witnessLive duskLive 7) 6 forkWitness := by
  refine ⟨alternate, 5, rungPairs mode, by decide, ?_, rungPairs_distinct mode, ?_⟩
  · rw [rungPairs_card]
    decide
  intro pair chosen situation
  obtain ⟨point, -, rfl⟩ := Finset.mem_map.mp chosen
  refine (Kernel.switch_turn (rungForks mode) (rungForkGoals mode) 7 showsDusk
    (fun _ => Kernel.replay Grid.interface 7 achievedSignal witnessExplore)
    (Function.update alternate 5 situation) 5 (rungPair mode point)
    (witness_reads mode _)).mpr ?_
  rw [Function.update_self,
    Kernel.seen_congr (Function.update alternate 5 situation) alternate situation 5
      (fun _ before => Function.update_of_ne (Nat.ne_of_lt before) _ _)]
  cases situation
  · have count : Kernel.seen alternate false 5 = 3 := by decide
    obtain ⟨visit, within, near⟩ := witnessTiles_near point.1 point.2
    rw [count]
    refine Kernel.replay_solves_explored ((rungForks mode).side false) (rungForkGoals mode) 7
      achievedSignal witnessExplore _ (achieved_decodes witnessConfig mode 7) visit 3
      (by omega) ⟨7, by omega, Nat.le_refl 7, witness_meets mode 7 visit within _ ?_⟩
    change tile (pointPosition point.1) ∈ box 3 (witnessEnd visit)
    rw [(witnessTiles_admitted point.1 point.2).1]
    exact near
  · have count : Kernel.seen alternate true 5 = 2 := by decide
    obtain ⟨same, -, visit, within, near⟩ := partner_spec point.1 point.2
    rw [count]
    refine Kernel.replay_solves_explored ((rungForks mode).side true) (rungForkGoals mode) 7
      achievedSignal witnessExplore _ (achieved_decodes witnessConfig mode 7) visit 2
      (by omega) ⟨7, by omega, Nat.le_refl 7,
        find_near_met mode duskLive 7 (witnessExplore visit) 7 (witnessEnd visit)
          (dusk_walk visit within) _ ?_⟩
    change tile (pointPosition (partner point.1)) ∈ box 3 (witnessEnd visit)
    rw [same]
    exact near

end AcornVerif.CurrentForkedTargetRung
