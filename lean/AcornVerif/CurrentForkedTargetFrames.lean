import AcornVerif.CurrentForkedTargetRung
import AcornVerif.CurrentFrameSize
import AcornVerif.CurrentFrameSlots

namespace AcornVerif.CurrentForkedTargetFrames
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung AcornVerif.CurrentForkedTargetRung

def slotNumber (tiling : ℕ) (word : SensorWord) : ℕ :=
  ((Rng.hash3 ((1 : UInt64) ^^^ tiling.toUInt64) word.channel word.value).toUInt32 &&&
    (16383 : ℕ).toUInt32).toNat

def tileValues : List UInt64 :=
  (List.finRange Host.patchSide).flatMap fun row =>
    (List.finRange Host.patchSide).flatMap fun col =>
      (List.range 8).map fun kind => (positionWord row col <<< 8) ||| kind.toUInt64

def tileCandidates : List SensorWord :=
  tileValues.map fun value => ⟨0x10, value⟩

def fixedCandidates : List SensorWord :=
  [⟨0x40, (10 : UInt8).toUInt64⟩, ⟨0x41, (4 : UInt8).toUInt64⟩,
    ⟨0x42, Rng.hash3 5 0 0⟩, ⟨0x49, 5⟩, ⟨0x4A, flagWord false⟩, ⟨0x4A, flagWord true⟩,
    ⟨0x43, resourceBucket 0⟩, ⟨0x44, resourceBucket 0⟩, ⟨0x45, resourceBucket 0⟩,
    ⟨0x46, resourceBucket 0⟩, ⟨0x47, flagWord false⟩, ⟨0x48, flagWord false⟩]

def feedbackCandidates : List SensorWord :=
  (List.range 11).flatMap fun index => (List.range 9).map fun bucket =>
    (⟨Grid.interface.feedback + index.toUInt64, bucket.toUInt64⟩ : SensorWord)

def daySlot : ℕ := slotNumber 2 ⟨0x41, 0⟩

private def hashPrefix (seed channel : UInt64) : UInt64 :=
  Rng.mix64 (Rng.mix64 (seed ^^^ Rng.increment) ^^^ channel)

private theorem mask14_eq (h : UInt64) :
    (h &&& (16383 : UInt64)).toNat = (h.toUInt32 &&& (16383 : ℕ).toUInt32).toNat := by
  have h1 : (h &&& (16383 : UInt64)).toNat = h.toNat % 2 ^ 14 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod h.toNat 14
  have h2 : (h.toUInt32 &&& (16383 : ℕ).toUInt32).toNat = (h.toNat % 2 ^ 32) % 2 ^ 14 := by
    rw [UInt32.toNat_and]
    have hl : h.toUInt32.toNat = h.toNat % 2 ^ 32 := rfl
    rw [hl]
    exact Nat.and_two_pow_sub_one_eq_mod (h.toNat % 2 ^ 32) 14
  rw [h1, h2, Nat.mod_mod_of_dvd _ (by decide)]

private theorem slotNumber_from_prefix (tiling : ℕ) (word : SensorWord) :
    slotNumber tiling word =
      (Rng.mix64 (hashPrefix ((1 : UInt64) ^^^ tiling.toUInt64) word.channel ^^^
        Rng.rotateLeft word.value 17) &&& (16383 : UInt64)).toNat := by
  unfold slotNumber hashPrefix Rng.hash3
  exact (mask14_eq _).symm

private def daySlotU64 : UInt64 :=
  Rng.hash3 ((1 : UInt64) ^^^ (2 : ℕ).toUInt64) 0x41 0 &&& (16383 : UInt64)

private theorem daySlotU64_toNat : daySlotU64.toNat = daySlot := by
  unfold daySlotU64 daySlot slotNumber
  exact mask14_eq _

private theorem tiles_miss_fast :
    ((List.range 8).all fun tiling =>
      let pref := hashPrefix ((1 : UInt64) ^^^ tiling.toUInt64) 0x10
      tileValues.all fun value =>
        (Rng.mix64 (pref ^^^ Rng.rotateLeft value 17) &&& (16383 : UInt64)) != daySlotU64) =
      true := by
  decide +kernel

private theorem fixed_miss_fast :
    ((List.range 8).all fun tiling =>
      fixedCandidates.all fun word =>
        (Rng.hash3 ((1 : UInt64) ^^^ tiling.toUInt64) word.channel word.value &&&
          (16383 : UInt64)) != daySlotU64) = true := by
  decide +kernel

private theorem feedback_miss_fast :
    ((List.range 8).all fun tiling =>
      (List.range 11).all fun index =>
        let pref := hashPrefix ((1 : UInt64) ^^^ tiling.toUInt64)
          (Grid.interface.feedback + index.toUInt64)
        (List.range 9).all fun bucket =>
          (Rng.mix64 (pref ^^^ Rng.rotateLeft bucket.toUInt64 17) &&& (16383 : UInt64)) !=
            daySlotU64) = true := by
  decide +kernel

private theorem units_miss_fast :
    (let pref := hashPrefix ((1 : UInt64) ^^^ 0x1D) 0x1D
     (List.range 512).all fun unit =>
      (Rng.mix64 (pref ^^^ Rng.rotateLeft unit.toUInt64 17) &&& (16383 : UInt64)) !=
        daySlotU64) = true := by
  decide +kernel

theorem candidates_miss :
    ((tileCandidates ++ fixedCandidates ++ feedbackCandidates).all fun word =>
        (List.range 8).all fun tiling => slotNumber tiling word != daySlot) = true ∧
      ((List.range 512).all fun unit =>
        ((Rng.hash3 ((1 : UInt64) ^^^ 0x1D) 0x1D unit.toUInt64).toUInt32 &&&
          (16383 : ℕ).toUInt32).toNat != daySlot) = true := by
  have hne : ∀ h : UInt64, ((h &&& (16383 : UInt64)) != daySlotU64) = true →
      ((h &&& (16383 : UInt64)).toNat != daySlot) = true := by
    intro h hm
    simp only [bne_iff_ne, ne_eq] at hm ⊢
    intro heq
    apply hm
    apply UInt64.toNat_inj.mp
    rw [heq, daySlotU64_toNat]
  constructor
  · rw [List.all_eq_true]
    intro word hmem
    rw [List.all_eq_true]
    intro tiling htiling
    rw [slotNumber_from_prefix]
    rcases List.mem_append.mp hmem with htf | hfb
    · rcases List.mem_append.mp htf with htile | hfix
      · obtain ⟨value, hval, rfl⟩ := List.mem_map.mp htile
        exact hne _ (List.all_eq_true.mp (List.all_eq_true.mp tiles_miss_fast tiling htiling)
          value hval)
      · exact hne _ (List.all_eq_true.mp (List.all_eq_true.mp fixed_miss_fast tiling htiling)
          word hfix)
    · obtain ⟨index, hidx, hrem⟩ := List.mem_flatMap.mp hfb
      obtain ⟨bucket, hbkt, rfl⟩ := List.mem_map.mp hrem
      exact hne _ (List.all_eq_true.mp
        (List.all_eq_true.mp (List.all_eq_true.mp feedback_miss_fast tiling htiling) index hidx)
        bucket hbkt)
  · rw [List.all_eq_true]
    intro unit hunit
    rw [← mask14_eq]
    exact hne _ (List.all_eq_true.mp units_miss_fast unit hunit)

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

private theorem witness_occupancy_empty (world : Host.World witnessConfig) :
    world.occupancy = ∅ := by
  have hfood : world.food.entries = #[] :=
    Array.eq_empty_of_size_eq_zero (by have := world.food.bounded; change _ ≤ 0 at this; omega)
  have hdeer : world.deer.entries = #[] :=
    Array.eq_empty_of_size_eq_zero (by have := world.deer.bounded; change _ ≤ 0 at this; omega)
  unfold Host.World.occupancy
  rw [hfood, hdeer]
  rfl

theorem centered_tile (world : Host.World witnessConfig)
    (centered : world.body.position = (Host.World.empty witnessConfig).body.position)
    (row column : Fin Host.patchSide) :
    ∃ tile : Host.TileObservation,
      world.observeTile world.occupancy row column = .ok tile ∧
        (∃ kind : Host.TileKind, tile.kind = kind.code) ∧ tile.food = 0 ∧ tile.deer = 0 := by
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
  have shape : world.observeTile world.occupancy row column = .ok ⟨kind.code, 0, 0⟩ := by
    unfold Host.World.observeTile
    rw [witness_occupancy_empty world]
    simp only [translated, kinded, bind, Except.bind, pure, Except.pure]
    rfl
  exact ⟨⟨kind.code, 0, 0⟩, shape, ⟨kind, rfl⟩, rfl, rfl⟩

theorem centered_observation (world : Host.World witnessConfig)
    (centered : world.body.position = (Host.World.empty witnessConfig).body.position) :
    ∃ tiles : Vector (Vector Host.TileObservation Host.patchSide) Host.patchSide,
      (∀ row col, (∃ kind : Host.TileKind, ((tiles.get row).get col).kind = kind.code) ∧
        ((tiles.get row).get col).food = 0 ∧ ((tiles.get row).get col).deer = 0) ∧
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
  · have entry : ((Vector.ofFn fun row => Vector.ofFn (seenTile row)).get row).get col =
        seenTile row col := by
      simp [Vector.get, Fin.cast]
    rw [entry]
    exact kinds row col
  · unfold Host.World.observe
    simp only [built, bind, Except.bind, pure, Except.pure]

theorem dusk_sensed (target : Host.Position) :
    ∃ tiles : Vector (Vector Host.TileObservation Host.patchSide) Host.patchSide,
      (∀ row col, (∃ kind : Host.TileKind, ((tiles.get row).get col).kind = kind.code) ∧
        ((tiles.get row).get col).food = 0 ∧ ((tiles.get row).get col).deer = 0) ∧
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

theorem rest_candidates (mode : TaskFeatureMode) (here : Bool) :
    ∀ word ∈ ([⟨0x40, (10 : UInt8).toUInt64⟩, ⟨0x41, (4 : UInt8).toUInt64⟩] : List SensorWord) ++
        (taskWords (.find (Rng.hash3 5 0 0) here) mode ++
          [⟨0x43, resourceBucket 0⟩, ⟨0x44, resourceBucket 0⟩, ⟨0x45, resourceBucket 0⟩,
            ⟨0x46, resourceBucket 0⟩, ⟨0x47, flagWord false⟩, ⟨0x48, flagWord false⟩]),
      word ∈ fixedCandidates := by
  cases mode <;> cases here <;> decide +kernel

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
    obtain ⟨⟨kind, code⟩, hfood, hdeer⟩ := kinds row col
    obtain ⟨number, small, same⟩ := kind_code kind
    unfold tileWords at inTile
    simp only [hfood, hdeer, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      List.append_nil, List.mem_singleton] at inTile
    subst inTile
    refine List.mem_map.mpr ⟨(positionWord row col <<< 8) ||| number.toUInt64,
      List.mem_flatMap.mpr ⟨row, List.mem_finRange row,
        List.mem_flatMap.mpr ⟨col, List.mem_finRange col,
          List.mem_map.mpr ⟨number, List.mem_range.mpr small, rfl⟩⟩⟩, ?_⟩
    rw [code, same]
  · exact List.mem_append_right _ (rest_candidates mode _ word inRest)

theorem slot_val (planning : PlanningSelection) (tiling : ℕ) (word : SensorWord) :
    (FeatIdx.fromHash (rungConstruction planning).dimension
      (Rng.hash3 ((rungConstruction planning).config.seed ^^^ tiling.toUInt64) word.channel
        word.value)).val = slotNumber tiling word := by
  cases planning <;> rfl

theorem unit_val (planning : PlanningSelection)
    (unit : Fin (rungConstruction planning).config.units.count) :
    (unitFeature (rungConstruction planning).dimension (rungConstruction planning).config
      unit).val =
      ((Rng.hash3 ((1 : UInt64) ^^^ 0x1D) 0x1D unit.val.toUInt64).toUInt32 &&&
        (16383 : ℕ).toUInt32).toNat := by
  cases planning <;> rfl

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
