/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentForkedTargetRung
import AcornVerif.CurrentFrameSize
import AcornVerif.CurrentFrameSlots

/-!
# The frozen encoder tells the two situations apart

The clause `AcornVerif.CurrentForkedTargetRule.StepsByRule` fixes the encoder through which the
executed agent's action reads its percept. If that encoder laid one frame at the starts of both
situations of `AcornVerif.CurrentForkedTargetRung.rungForks`, no agent the clause admits could
value them differently at a visit's first decision. This module proves it does not.

`starts_differ`: for either planning selection, in every state of the rung's agent, reachable or
not, and for every pair of installed targets, the frame laid on the percept at the first
situation's start holds a slot that the frame laid on the percept at the second situation's
start does not hold. The slot is that of the first phase's day word, `⟨0x41, 0⟩`, at the third
tiling (`daySlot`).

The proof has two halves.

- *What a frame at the second start can hold.* A frame's slots are those of its words at each
  tiling and those of the active units (`Acorn.Features.rawEncodeWith_def`). The words are the
  world's and the feedback words of the stored predictions (`Acorn.Handcrafted.Agent.words_def`).
  The host observes the second start, and the observation has a window each of whose tiles has
  the code of one of the eight terrain kinds, full energy, the day's fifth phase, a concealed
  target's task relation and an empty inventory (`dusk_sensed`); no terrain is evaluated. So every
  word of the world there is one of 1222 candidates (`dusk_words`), and every feedback word,
  whatever predictions are stored, is one of 99 (`feedbackWords_mem`).
- *None of them has the slot.* The kernel evaluates the hash of each candidate word at each of
  the eight tilings, and of each of the 512 units, and none equals `daySlot`
  (`candidates_miss`).

The statement is about active slots. It says the controller's readout can differ between the two
situations, since weight on that slot reaches one frame's values and not the other's. It says
nothing of whether any learning rule puts weight there.

The numbers are the rung's: seed 1, eight tilings, 16384 slots and 512 units (`slot_val`,
`unit_val`). A change to the coder's hash, to those constants or to the words a frame carries
makes the kernel's evaluation fail or the candidates incomplete, and the slot is then chosen
again.
-/

namespace AcornVerif.CurrentForkedTargetFrames
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung AcornVerif.CurrentForkedTargetRung

/-- The slot of a word at a tiling, as a number, in a feature space of 16384 slots under the seed
one: the tiled coder's hash, masked. -/
def slotNumber (tiling : ℕ) (word : SensorWord) : ℕ :=
  ((Rng.hash3 ((1 : UInt64) ^^^ tiling.toUInt64) word.channel word.value).toUInt32 &&&
    (16383 : ℕ).toUInt32).toNat

/-- The words a tile of the window can give: its kind, one of the eight terrain kinds, and its
food and deer marks. -/
def tileCandidates : List SensorWord :=
  (List.finRange Host.patchSide).flatMap fun row =>
    (List.finRange Host.patchSide).flatMap fun col =>
      ((List.range 8).map fun kind =>
        (⟨0x10, (positionWord row col <<< 8) ||| kind.toUInt64⟩ : SensorWord)) ++
        [⟨0x20, positionWord row col⟩, ⟨0x30, positionWord row col⟩]

/-- The other words a frame at the second situation's start can carry: full energy, the day's
fifth phase, a concealed target's task words with either flag, and an empty inventory. -/
def fixedCandidates : List SensorWord :=
  [⟨0x40, (10 : UInt8).toUInt64⟩, ⟨0x41, (4 : UInt8).toUInt64⟩,
    ⟨0x42, Rng.hash3 5 0 0⟩, ⟨0x49, 5⟩, ⟨0x4A, flagWord false⟩, ⟨0x4A, flagWord true⟩,
    ⟨0x43, resourceBucket 0⟩, ⟨0x44, resourceBucket 0⟩, ⟨0x45, resourceBucket 0⟩,
    ⟨0x46, resourceBucket 0⟩, ⟨0x47, flagWord false⟩, ⟨0x48, flagWord false⟩]

/-- The feedback words any stored predictions can give: one of nine buckets on one of the eleven
feedback channels. -/
def feedbackCandidates : List SensorWord :=
  (List.range 11).flatMap fun index => (List.range 9).map fun bucket =>
    (⟨Grid.interface.feedback + index.toUInt64, bucket.toUInt64⟩ : SensorWord)

/-- The slot that tells the situations apart: the slot of the first phase's day word at the
third tiling. -/
def daySlot : ℕ := slotNumber 2 ⟨0x41, 0⟩

/-- **No word a frame at the second situation's start can carry, and no unit, has the first
phase's slot.** The kernel evaluates the hash of each candidate word at each of the eight
tilings, and of each of the 512 units. -/
theorem candidates_miss :
    ((tileCandidates ++ fixedCandidates ++ feedbackCandidates).all fun word =>
        (List.range 8).all fun tiling => slotNumber tiling word != daySlot) = true ∧
      ((List.range 512).all fun unit =>
        ((Rng.hash3 ((1 : UInt64) ^^^ 0x1D) 0x1D unit.toUInt64).toUInt32 &&&
          (16383 : ℕ).toUInt32).toNat != daySlot) = true := by
  decide +kernel

/-! ## The words a frame at the second situation's start can carry -/

/-- Every feedback word is one of nine buckets on one of the channels from the base on, one for
each question. -/
theorem feedbackWords_mem (base : UInt64) (discounts : List Discount) (values : List Binary32)
    (index : ℕ) (word : SensorWord) (held : word ∈ feedbackWords base discounts values index) :
    ∃ position bucket, index ≤ position ∧ position < index + discounts.length ∧ bucket < 9 ∧
      word = ⟨base + position.toUInt64, bucket.toUInt64⟩ := by
  induction discounts generalizing values index with
  | nil =>
    change word ∈ ([] : List SensorWord) at held
    cases held
  | cons discount rest ih =>
    cases values with
    | nil =>
      change word ∈ ([] : List SensorWord) at held
      cases held
    | cons value others =>
      rw [feedbackWords_cons_cons] at held
      rcases List.mem_cons.mp held with rfl | later
      · exact ⟨index, (predictionBucket value discount.horizon).val, Nat.le_refl _,
          by rw [List.length_cons]; omega, (predictionBucket value discount.horizon).isLt, rfl⟩
      · obtain ⟨position, bucket, low, high, small, same⟩ := ih others (index + 1) later
        exact ⟨position, bucket, by omega, by rw [List.length_cons]; omega, small, same⟩

/-- Each terrain kind's code is one of the first eight numbers. -/
theorem kind_code (kind : Host.TileKind) :
    ∃ number, number < 8 ∧ kind.code.toUInt64 = number.toUInt64 := by
  cases kind
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩

/-- **Each tile the host observes around the center has a terrain kind's code.** At every world
of the witness configuration whose body stands at the center, the observation of each tile of the
window succeeds, and the tile's kind is the code of a terrain kind. No terrain is evaluated. -/
theorem centered_tile (world : Host.World witnessConfig)
    (centered : world.body.position = (Host.World.empty witnessConfig).body.position)
    (row column : Fin Host.patchSide) :
    ∃ tile : Host.TileObservation,
      world.observeTile world.occupancy row column = .ok tile ∧
        ∃ kind : Host.TileKind, tile.kind = kind.code := by
  have center : ((Host.World.empty witnessConfig).body.position.x.val : Int) = 32 ∧
      ((Host.World.empty witnessConfig).body.position.y.val : Int) = 32 := by decide
  have radius : ((Host.patchSide / 2 : Nat) : Int) = 5 := rfl
  have side : Host.patchSide = 11 := rfl
  have columnBound := column.isLt
  have rowBound := row.isLt
  have translated : world.body.position.position.translate
      ((column.val : Int) - (Host.patchSide / 2 : Nat))
      ((row.val : Int) - (Host.patchSide / 2 : Nat)) =
      some ⟨⟨27 + column.val, by omega⟩, ⟨27 + row.val, by omega⟩⟩ := by
    refine CurrentCertificates.translate_of_eq _ _ _ _ ?_ ?_
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
  obtain ⟨kind, kinded⟩ := ok_of_isOk
    ((CurrentTerrain.tileKind_isOk world
      ⟨⟨27 + column.val, by omega⟩, ⟨27 + row.val, by omega⟩⟩).mpr
      (fun octave below =>
        ⟨window_admits column ⟨octave, below⟩, window_admits row ⟨octave, below⟩⟩))
  have shape : ∃ food deer, world.observeTile world.occupancy row column =
      .ok ⟨kind.code, food, deer⟩ := by
    unfold Host.World.observeTile
    simp only [translated, kinded]
    exact ⟨_, _, rfl⟩
  obtain ⟨food, deer, seen⟩ := shape
  exact ⟨_, seen, kind, rfl⟩

/-- **The host's observation around the center.** At every world of the witness configuration
whose body stands at the center, the host observes, and its observation holds a window each of
whose tiles has the code of a terrain kind, with the world's own energy, day phase, task relation
and inventory. No terrain is evaluated. -/
theorem centered_observation (world : Host.World witnessConfig)
    (centered : world.body.position = (Host.World.empty witnessConfig).body.position) :
    ∃ tiles : Vector (Vector Host.TileObservation Host.patchSide) Host.patchSide,
      (∀ row col, ∃ kind : Host.TileKind, ((tiles.get row).get col).kind = kind.code) ∧
      world.observe = .ok ⟨tiles, (min (world.body.energy.val / 100) 10).toUInt8,
        world.dayPhase.val.toUInt8, world.taskObservation, world.body.inventory⟩ := by
  choose seenTile seen kinds using centered_tile world centered
  have rows : (fun row => Vector.ofFnM (world.observeTile world.occupancy row)) =
      fun row => (pure (Vector.ofFn (seenTile row)) :
        Except Host.WorldError (Vector Host.TileObservation Host.patchSide)) := by
    funext row
    have columns : world.observeTile world.occupancy row =
        fun column => pure (seenTile row column) := funext (seen row)
    rw [columns, Vector.ofFnM_pure]
  have built : Vector.ofFnM (fun row => Vector.ofFnM (world.observeTile world.occupancy row)) =
      .ok (Vector.ofFn fun row => Vector.ofFn (seenTile row)) := by
    rw [rows, Vector.ofFnM_pure]
    rfl
  refine ⟨Vector.ofFn fun row => Vector.ofFn (seenTile row), fun row col => ?_, ?_⟩
  · obtain ⟨kind, code⟩ := kinds row col
    refine ⟨kind, ?_⟩
    rw [← code]
    have entry : ((Vector.ofFn fun row => Vector.ofFn (seenTile row)).get row).get col =
        seenTile row col := by
      simp [Vector.get, Fin.cast]
    rw [entry]
  · unfold Host.World.observe
    simp only [built, bind, Except.bind, pure, Except.pure]

/-- **What the host observes at the second situation's start.** Whatever target is installed,
the sensed observation there holds a window each of whose tiles has the code of a terrain kind,
full energy, the day's fifth phase, the concealed target's task relation and an empty
inventory. -/
theorem dusk_sensed (target : Host.Position) :
    ∃ tiles : Vector (Vector Host.TileObservation Host.patchSide) Host.patchSide,
      (∀ row col, ∃ kind : Host.TileKind, ((tiles.get row).get col).kind = kind.code) ∧
      sensed (duskLive.world.setGoal (.find target)) =
        ⟨tiles, 10, 4,
          .find (Rng.hash3 5 0 0) (duskLive.world.setGoal (.find target)).goalSatisfied,
          ⟨0, 0, 0, 0, false, false⟩⟩ := by
  obtain ⟨tiles, kinds, observed⟩ :=
    centered_observation (duskLive.world.setGoal (.find target)) rfl
  have energy : (min ((duskLive.world.setGoal (.find target)).body.energy.val / 100) 10).toUInt8
      = 10 := by
    change (min (duskLive.world.body.energy.val / 100) 10).toUInt8 = 10
    decide +kernel
  have phase : (duskLive.world.setGoal (.find target)).dayPhase.val.toUInt8 = 4 := by
    change duskLive.world.dayPhase.val.toUInt8 = 4
    rw [dusk_phase]
    rfl
  refine ⟨tiles, kinds, ?_⟩
  rw [sensed_ok _ _ observed, energy, phase,
    find_task (duskLive.world.setGoal (.find target)) target rfl]
  rfl

/-- The words of a frame at the second situation's start beside its tiles' are candidates. -/
theorem rest_candidates (mode : TaskFeatureMode) (here : Bool) :
    ∀ word ∈ ([⟨0x40, (10 : UInt8).toUInt64⟩, ⟨0x41, (4 : UInt8).toUInt64⟩] : List SensorWord) ++
        (taskWords (.find (Rng.hash3 5 0 0) here) mode ++
          [⟨0x43, resourceBucket 0⟩, ⟨0x44, resourceBucket 0⟩, ⟨0x45, resourceBucket 0⟩,
            ⟨0x46, resourceBucket 0⟩, ⟨0x47, flagWord false⟩, ⟨0x48, flagWord false⟩]),
      word ∈ fixedCandidates := by
  cases mode <;> cases here <;> decide +kernel

/-- **Every word of a frame at the second situation's start is a candidate.** -/
theorem dusk_words (mode : TaskFeatureMode) (target : Host.Position) (word : SensorWord)
    (held : word ∈ ((gridWorld witnessConfig mode).percept (member duskLive target)).frame.words) :
    word ∈ tileCandidates ++ fixedCandidates := by
  obtain ⟨tiles, kinds, shown⟩ := dusk_sensed target
  change word ∈ sensorWords (sensed (duskLive.world.setGoal (.find target))) mode at held
  rw [shown] at held
  unfold sensorWords at held
  rw [List.append_assoc, List.append_assoc] at held
  rcases List.mem_append.mp held with inTiles | inRest
  · refine List.mem_append_left _ ?_
    obtain ⟨row, -, inRow⟩ := List.mem_flatMap.mp inTiles
    obtain ⟨col, -, inTile⟩ := List.mem_flatMap.mp inRow
    refine List.mem_flatMap.mpr ⟨row, List.mem_finRange row,
      List.mem_flatMap.mpr ⟨col, List.mem_finRange col, ?_⟩⟩
    obtain ⟨kind, code⟩ := kinds row col
    obtain ⟨number, small, same⟩ := kind_code kind
    unfold tileWords at inTile
    simp only [List.mem_append, List.mem_singleton] at inTile
    rcases inTile with (rfl | food) | deer
    · refine List.mem_append_left _ (List.mem_map.mpr ⟨number, List.mem_range.mpr small, ?_⟩)
      rw [code, same]
    · split at food
      · rw [List.mem_singleton] at food
        subst food
        exact List.mem_append_right _ (List.mem_cons_self)
      · cases food
    · split at deer
      · rw [List.mem_singleton] at deer
        subst deer
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self))
      · cases deer
  · exact List.mem_append_right _ (rest_candidates mode _ word inRest)

/-- The slot of a word at a tiling, under the rung's construction, is its slot number. -/
theorem slot_val (planning : PlanningSelection) (tiling : ℕ) (word : SensorWord) :
    (FeatIdx.fromHash (rungConstruction planning).dimension
      (Rng.hash3 ((rungConstruction planning).config.seed ^^^ tiling.toUInt64) word.channel
        word.value)).val = slotNumber tiling word := by
  cases planning <;> rfl

/-- The slot of a unit, under the rung's construction, as a number. -/
theorem unit_val (planning : PlanningSelection)
    (unit : Fin (rungConstruction planning).config.units.count) :
    (unitFeature (rungConstruction planning).dimension (rungConstruction planning).config
      unit).val =
      ((Rng.hash3 ((1 : UInt64) ^^^ 0x1D) 0x1D unit.val.toUInt64).toUInt32 &&&
        (16383 : ℕ).toUInt32).toNat := by
  cases planning <;> rfl

/-- **The frozen encoder tells the two situations apart, in every state of the agent.** For
either planning selection, every state of the rung's agent, reachable or not, and every pair of
installed targets: the frame the agent's encoder lays on the percept at the first situation's
start holds a slot that the frame it lays on the percept at the second situation's start does
not hold. The slot is that of the first phase's day word at the third tiling. So the policy the
primitive controller freezes can value the two situations differently: weight on that slot
reaches the first situation's values and not the second's. -/
theorem starts_differ (planning : PlanningSelection)
    (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (first second : Host.Position) :
    ∃ slot,
      slot ∈ (agent.advanceClock.frame
        ((gridWorld witnessConfig (rungConstruction planning).profile.taskMode).percept
          (member witnessLive first)).frame).active.indices ∧
      slot ∉ (agent.advanceClock.frame
        ((gridWorld witnessConfig (rungConstruction planning).profile.taskMode).percept
          (member duskLive second)).frame).active.indices := by
  have tilings : (rungConstruction planning).config.tilings.toNat = 8 := by
    cases planning <;> rfl
  have units : (rungConstruction planning).config.units.count = 512 := by
    cases planning <;> rfl
  refine ⟨FeatIdx.fromHash (rungConstruction planning).dimension
    (Rng.hash3 ((rungConstruction planning).config.seed ^^^ (2 : ℕ).toUInt64) 0x41 0), ?_, ?_⟩
  · have held := CurrentFrameSlots.percept_day_word
      (rungConstruction planning).profile.taskMode (member witnessLive first)
      (fun live same => by
        cases same
        change witnessLive.world.time.toNat < witnessConfig.raw.dayLength.toNat / 8
        decide +kernel)
    have laid := CurrentFrameSlots.word_slot agent .learnThenAct _ ⟨0x41, 0⟩ held 2
      (by rw [tilings]; decide)
    rw [CurrentFrameSize.choose_frame] at laid
    exact laid
  · intro inside
    rw [(agent.advanceClock.frame _).fresh, encode_membership] at inside
    change _ ∈ rawEncodeWith _ _ _ _ at inside
    rw [rawEncodeWith_def, tiledFeatures_def, imprintFeatures_def] at inside
    rcases List.mem_append.mp inside with tiled | imprinted
    · obtain ⟨tiling, inRange, inMap⟩ := List.mem_flatMap.mp tiled
      obtain ⟨word, held, same⟩ := List.mem_map.mp inMap
      have small : tiling < 8 := by
        rw [← tilings]
        exact List.mem_range.mp inRange
      have numbers : slotNumber tiling word = daySlot :=
        (slot_val planning tiling word).symm.trans
          ((congrArg Fin.val same).trans (slot_val planning 2 ⟨0x41, 0⟩))
      rw [Agent.words_def] at held
      have candidate : word ∈ tileCandidates ++ fixedCandidates ++ feedbackCandidates := by
        rcases List.mem_append.mp held with world | feedback
        · exact List.mem_append_left _
            (dusk_words (rungConstruction planning).profile.taskMode second word world)
        · obtain ⟨position, bucket, -, high, few, rfl⟩ := feedbackWords_mem _ _ _ _ _ feedback
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨position,
            List.mem_range.mpr (Nat.lt_of_lt_of_le high (by decide)),
            List.mem_map.mpr ⟨bucket, List.mem_range.mpr few, rfl⟩⟩)
      have missed := List.all_eq_true.mp
        (List.all_eq_true.mp candidates_miss.1 word candidate) tiling (List.mem_range.mpr small)
      exact absurd numbers (by simpa using missed)
    · obtain ⟨unit, -, chosen⟩ := List.mem_filterMap.mp imprinted
      split at chosen
      · have numbers : ((Rng.hash3 ((1 : UInt64) ^^^ 0x1D) 0x1D unit.val.toUInt64).toUInt32 &&&
            (16383 : ℕ).toUInt32).toNat = daySlot :=
          (unit_val planning unit).symm.trans
            ((congrArg Fin.val (Option.some.inj chosen)).trans (slot_val planning 2 ⟨0x41, 0⟩))
        have missed := List.all_eq_true.mp candidates_miss.2 unit.val
          (List.mem_range.mpr (by rw [← units]; exact unit.isLt))
        exact absurd numbers (by simpa using missed)
      · cases chosen

end AcornVerif.CurrentForkedTargetFrames
