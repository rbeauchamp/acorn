import AcornVerif.CurrentFrameSize

namespace AcornVerif.CurrentFrameSlots
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentFrameSize

variable {config : Host.WorldConfig}

theorem sensorWords_energy (observation : Host.Observation) (mode : TaskFeatureMode) :
    (⟨0x40, observation.energy.toUInt64⟩ : SensorWord) ∈ sensorWords observation mode := by
  simp [sensorWords]

theorem percept_holds_word (mode : TaskFeatureMode) (state : Option (Live config)) :
    ∃ word, word ∈ ((gridWorld config mode).percept state).frame.words := by
  cases state with
  | none => exact ⟨_, sensorWords_energy blank mode⟩
  | some live => exact ⟨_, sensorWords_energy (sensed live.world) mode⟩

theorem sensorWords_day (observation : Host.Observation) (mode : TaskFeatureMode) :
    (⟨0x41, observation.day.toUInt64⟩ : SensorWord) ∈ sensorWords observation mode := by
  simp [sensorWords]

theorem dayPhase_early (world : Host.World config)
    (early : world.time.toNat < config.raw.dayLength.toNat / 8) : world.dayPhase.val = 0 := by
  have slot : world.time.toNat % config.raw.dayLength.toNat = world.time.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have first : world.time.toNat < config.raw.dayLength.toNat / 2 := by omega
  have eighth : max 1 (config.raw.dayLength.toNat / 8) = config.raw.dayLength.toNat / 8 := by
    omega
  unfold Host.World.dayPhase
  simp only [FeatureConstants.dayPhases, slot, first, eighth, ↓reduceIte,
    Nat.div_eq_of_lt early, Nat.zero_min]

theorem sensed_day (world : Host.World config) :
    (sensed world).day = world.dayPhase.val.toUInt8 ∨ (sensed world).day = 0 := by
  unfold sensed
  cases seen : world.observe with
  | error refusal => exact Or.inr rfl
  | ok observation =>
    left
    unfold Host.World.observe at seen
    cases tiles : Vector.ofFnM (fun row => Vector.ofFnM (world.observeTile world.occupancy row))
      with
    | error refusal => simp [tiles, bind, Except.bind] at seen
    | ok tiles =>
      simp only [tiles, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at seen
      cases seen
      rfl

theorem percept_day_word (mode : TaskFeatureMode) (state : Option (Live config))
    (early : ∀ live, state = some live →
      live.world.time.toNat < config.raw.dayLength.toNat / 8) :
    (⟨0x41, 0⟩ : SensorWord) ∈ ((gridWorld config mode).percept state).frame.words := by
  cases state with
  | none => exact sensorWords_day blank mode
  | some live =>
    have word := sensorWords_day (sensed live.world) mode
    rcases sensed_day live.world with day | day
    · rw [day, dayPhase_early live.world (early live rfl)] at word
      exact word
    · rw [day] at word
      exact word

theorem tileKind_unharvested (world : Host.World config)
    (unharvested : world.harvested.isEmpty = true) (position : Host.Position) :
    world.tileKind position =
      Host.terrain position config.raw.seed config.raw.baseScale := by
  unfold Host.World.tileKind
  cases Host.terrain position config.raw.seed config.raw.baseScale with
  | error refusal => rfl
  | ok base =>
    simp only [bind, Except.bind, Std.TreeMap.getElem?_of_isEmpty unharvested]
    repeat' split
    all_goals rfl

theorem observe_congr (world next : Host.World config)
    (place : next.body.position = world.body.position)
    (kinds : ∀ position, next.tileKind position = world.tileKind position)
    (occupied : next.occupancy = world.occupancy)
    (energy : min (next.body.energy.val / 100) 10 = min (world.body.energy.val / 100) 10)
    (day : next.dayPhase = world.dayPhase)
    (task : next.taskObservation = world.taskObservation)
    (inventory : next.body.inventory = world.body.inventory) :
    next.observe = world.observe := by
  have tiles : ∀ (occupancy : Host.Occupancy) (row : Fin Host.patchSide),
      next.observeTile occupancy row = world.observeTile occupancy row := by
    intro occupancy row
    funext column
    unfold Host.World.observeTile
    rw [place]
    simp only [kinds]
  unfold Host.World.observe
  simp only [occupied, tiles, energy, day, task, inventory]

theorem sensed_congr (first second : Host.World config)
    (same : first.observe = second.observe) : sensed first = sensed second := by
  unfold sensed
  rw [same]

theorem percept_frame_congr (mode : TaskFeatureMode) (first second : Live config)
    (same : sensed first.world = sensed second.world) :
    ((gridWorld config mode).percept (some first)).frame.words =
        ((gridWorld config mode).percept (some second)).frame.words ∧
      ((gridWorld config mode).percept (some first)).frame.symbols =
        ((gridWorld config mode).percept (some second)).frame.symbols := by
  constructor
  · change sensorWords (sensed first.world) mode = sensorWords (sensed second.world) mode
    rw [same]
  · change observationPatch (sensed first.world) mode = observationPatch (sensed second.world) mode
    rw [same]

section Slots

variable {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

theorem word_slot (state : Agent interface profile features criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) (word : SensorWord)
    (held : word ∈ percept.frame.words) (tiling : ℕ) (within : tiling < features.tilings.toNat) :
    FeatIdx.fromHash dimension (Rng.hash3 (features.seed ^^^ tiling.toUInt64) word.channel
      word.value) ∈ (state.choose order percept).features.indices := by
  rw [choose_frame, (state.advanceClock.frame percept.frame).fresh, encode_membership]
  change _ ∈ rawEncodeWith dimension features _ _
  rw [rawEncodeWith_def, tiledFeatures_def]
  refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨tiling, List.mem_range.mpr within,
    List.mem_map.mpr ⟨word, ?_, rfl⟩⟩)
  rw [Agent.words_def]
  exact List.mem_append_left _ held

theorem shared_slot
    (first second : Agent interface profile features criterion dimension planning)
    (order other : StepOrder) (one two : Percept interface) (word : SensorWord)
    (heldOne : word ∈ one.frame.words) (heldTwo : word ∈ two.frame.words)
    (tiled : 0 < features.tilings.toNat) :
    ∃ slot, slot ∈ (first.choose order one).features.indices ∧
      slot ∈ (second.choose other two).features.indices :=
  ⟨_, word_slot first order one word heldOne 0 tiled,
    word_slot second other two word heldTwo 0 tiled⟩

theorem choose_features_congr
    (first second : Agent interface profile features criterion dimension planning)
    (order other : StepOrder) (one two : Percept interface)
    (words : one.frame.words = two.frame.words) (symbols : one.frame.symbols = two.frame.symbols)
    (bank : first.control.runtime.lifecycle.representation.bank =
      second.control.runtime.lifecycle.representation.bank)
    (stored : first.control.runtime.references.demonPredictions =
      second.control.runtime.references.demonPredictions) :
    (first.choose order one).features = (second.choose other two).features := by
  rw [choose_frame, choose_frame, (first.advanceClock.frame one.frame).fresh,
    (second.advanceClock.frame two.frame).fresh, Agent.words_def, Agent.words_def]
  change encode dimension first.control.runtime.lifecycle.representation.bank
      (one.frame.words ++ feedbackWords interface.feedback interface.layout
        first.control.runtime.references.demonPredictions.words 0) one.frame.symbols =
    encode dimension second.control.runtime.lifecycle.representation.bank
      (two.frame.words ++ feedbackWords interface.feedback interface.layout
        second.control.runtime.references.demonPredictions.words 0) two.frame.symbols
  rw [words, symbols, bank, stored]

end Slots

section Grid

variable {profile : FeatureProfile} {features : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {planning : PlanningSelection}

theorem grid_frame_slot (mode : TaskFeatureMode) (order : StepOrder)
    (state : Agent Grid.interface profile features criterion dimension planning)
    (inner : Option (Live config)) (tiled : 0 < features.tilings.toNat) :
    ∃ slot, slot ∈
      (state.choose order ((gridWorld config mode).percept inner)).features.indices := by
  obtain ⟨word, held⟩ := percept_holds_word mode inner
  exact ⟨_, word_slot state order _ word held 0 tiled⟩

end Grid

end AcornVerif.CurrentFrameSlots
