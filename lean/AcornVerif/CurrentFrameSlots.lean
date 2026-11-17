/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentFrameSize

/-!
# The slots a frame holds

`AcornVerif.CurrentFrameSize` bounds the number of a frame's slots from above. This module says
which slots a frame holds, as far as its percept's words decide it.

The tiled coder hashes each word of the frame once for each tiling, and the first-occurrence
filtering keeps every slot. So each word of a percept's frame gives a slot of the frame the step
lays, at each tiling (`word_slot`); the slot is a function of the word, the tiling and the
feature configuration's seed, and of no agent state. Two frames whose percepts carry a common
word therefore share a slot, under a configuration with a tiling, whatever the two agent states
(`shared_slot`).

Every percept of the grid world carries its energy word, at every state, the refused state
included (`percept_holds_word`). So, under a configuration with a tiling, every frame the
executed agent lays from a grid percept holds at least one slot (`grid_frame_slot`).

Every percept also carries its day word (`sensorWords_day`). The host reports the day's phase,
which is zero until an eighth of the day has passed (`dayPhase_early`), and the blank observation
that stands in for a refused one reports zero (`sensed_day`). So at a state that is refused, or
whose clock has not passed an eighth of the day, the percept carries the word of day phase zero
(`percept_day_word`), and two such percepts have that word in common.

A frame is encoded from the words and the symbols of its percept's frame and the words fed back
from the agent's stored predictions, under the agent's feature bank. So two steps lay the same
frame when their percepts' frames carry the same words and symbols and the two agent states hold
the same bank and the same stored predictions (`choose_features_congr`). In the grid world the
words and the symbols are functions of the host's observation (`sensed_congr`,
`percept_frame_congr`), and two worlds are observed alike when they agree on the body's position,
inventory and energy bucket, on the kind of every tile, on the food and the deer, on the day's
phase and on the task (`observe_congr`). Where no tile is harvested a tile's kind is its base
terrain (`tileKind_bare`), and a population of capacity zero is empty (`population_unique`).

What this does not say. Which other word two percepts of a run have in common: that is a fact of
the world's states. How many slots two different frames share. And two words can hash to one
slot, as any two hashed words can, so a frame can hold fewer slots than its words times its
tilings.
-/

namespace AcornVerif.CurrentFrameSlots
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentFrameSize

variable {config : Host.WorldConfig}

/-! ## The words every grid percept carries -/

/-- Every observation's words hold its energy word. -/
theorem sensorWords_energy (observation : Host.Observation) (mode : TaskFeatureMode) :
    (⟨0x40, observation.energy.toUInt64⟩ : SensorWord) ∈ sensorWords observation mode := by
  simp [sensorWords]

/-- Every percept of the grid world carries a word, at every state, the refused state included:
its energy word. -/
theorem percept_holds_word (mode : TaskFeatureMode) (state : Option (Live config)) :
    ∃ word, word ∈ ((gridWorld config mode).percept state).frame.words := by
  cases state with
  | none => exact ⟨_, sensorWords_energy blank mode⟩
  | some live => exact ⟨_, sensorWords_energy (sensed live.world) mode⟩

/-- Every observation's words hold its day word. -/
theorem sensorWords_day (observation : Host.Observation) (mode : TaskFeatureMode) :
    (⟨0x41, observation.day.toUInt64⟩ : SensorWord) ∈ sensorWords observation mode := by
  simp [sensorWords]

/-- Before an eighth of the day has passed, the day phase is zero. -/
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

/-- The observation a state senses reports the world's day phase, or zero where the host
refuses and the blank observation stands in. -/
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

/-- **Early in the day every percept carries one day word.** At a state of the grid world that is
refused, or whose clock has not passed an eighth of the day, the percept carries the word of day
phase zero. -/
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

/-! ## Worlds the host observes alike -/

/-- Where no tile has been harvested, the effective kind of a tile is its base terrain. -/
theorem tileKind_bare (world : Host.World config) (bare : world.harvested.isEmpty = true)
    (position : Host.Position) :
    world.tileKind position =
      Host.terrain position config.raw.seed config.raw.baseScale := by
  unfold Host.World.tileKind
  cases Host.terrain position config.raw.seed config.raw.baseScale with
  | error refusal => rfl
  | ok base =>
    simp only [bind, Except.bind, Std.TreeMap.getElem?_of_isEmpty bare]
    repeat' split
    all_goals rfl

/-- A population of capacity zero is the empty one. -/
theorem population_unique {α : Type} {capacity : Nat} (zero : capacity = 0)
    (first second : Host.Population α capacity) : first = second := by
  subst zero
  obtain ⟨firstEntries, firstBound⟩ := first
  obtain ⟨secondEntries, secondBound⟩ := second
  have one : firstEntries = #[] := Array.eq_empty_of_size_eq_zero (by omega)
  have two : secondEntries = #[] := Array.eq_empty_of_size_eq_zero (by omega)
  subst one two
  rfl

/-- **What the host's observation reads.** Two worlds are observed alike when they agree on the
body's position and inventory, on the bucket of its energy, on the effective kind of every tile,
on the food and the deer, on the day's phase and on the task. -/
theorem observe_congr (world next : Host.World config)
    (place : next.body.position = world.body.position)
    (kinds : ∀ position, next.tileKind position = world.tileKind position)
    (food : next.food = world.food) (deer : next.deer = world.deer)
    (energy : min (next.body.energy.val / 100) 10 = min (world.body.energy.val / 100) 10)
    (day : next.dayPhase = world.dayPhase)
    (task : next.taskObservation = world.taskObservation)
    (inventory : next.body.inventory = world.body.inventory) :
    next.observe = world.observe := by
  have occupied : next.occupancy = world.occupancy := by
    unfold Host.World.occupancy
    rw [food, deer]
  have tiles : ∀ (occupancy : Host.Occupancy) (row : Fin Host.patchSide),
      next.observeTile occupancy row = world.observeTile occupancy row := by
    intro occupancy row
    funext column
    unfold Host.World.observeTile
    rw [place]
    simp only [kinds]
  unfold Host.World.observe
  simp only [occupied, tiles, energy, day, task, inventory]

/-- Two worlds the host observes alike are sensed alike. -/
theorem sensed_congr (first second : Host.World config)
    (same : first.observe = second.observe) : sensed first = sensed second := by
  unfold sensed
  rw [same]

/-- Two live states whose worlds are sensed alike deliver percepts whose frames carry the same
words and the same symbols. -/
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

/-! ## The slots of the words -/

section Slots

variable {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- Every word of a percept's frame gives, at each tiling, a slot of the frame the step lays: the
tiled coder hashes each word once for each tiling, and the first-occurrence filtering keeps every
slot. -/
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

/-- **Two frames that carry a common word share a slot.** Under a feature configuration with a
tiling, two steps on percepts whose frames carry one common word lay one common slot, whatever
the two agent states and step orders. -/
theorem shared_slot
    (first second : Agent interface profile features criterion dimension planning)
    (order other : StepOrder) (one two : Percept interface) (word : SensorWord)
    (heldOne : word ∈ one.frame.words) (heldTwo : word ∈ two.frame.words)
    (tiled : 0 < features.tilings.toNat) :
    ∃ slot, slot ∈ (first.choose order one).features.indices ∧
      slot ∈ (second.choose other two).features.indices :=
  ⟨_, word_slot first order one word heldOne 0 tiled,
    word_slot second other two word heldTwo 0 tiled⟩

/-- **A frame is decided by the percept's frame, the bank and the stored predictions.** Two steps
lay the same slots, in the same order, when their percepts' frames carry the same words and the
same symbols and the two agent states hold the same bank and the same stored predictions,
whatever else the states hold and whatever the step orders. -/
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

/-- **Every frame of the grid world holds a slot.** Under a feature configuration with a tiling,
every step of the executed agent on a percept of the grid world lays at least one slot, from
every agent state, at every state of the world and under every step order. -/
theorem grid_frame_slot (mode : TaskFeatureMode) (order : StepOrder)
    (state : Agent Grid.interface profile features criterion dimension planning)
    (inner : Option (Live config)) (tiled : 0 < features.tilings.toNat) :
    ∃ slot, slot ∈
      (state.choose order ((gridWorld config mode).percept inner)).features.indices := by
  obtain ⟨word, held⟩ := percept_holds_word mode inner
  exact ⟨_, word_slot state order _ word held 0 tiled⟩

end Grid

end AcornVerif.CurrentFrameSlots
