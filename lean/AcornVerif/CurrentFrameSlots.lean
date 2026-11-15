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

What this does not say. Which word two percepts of a run have in common: that is a fact of the
world's states. And two words can hash to one slot, as any two hashed words can, so a frame can
hold fewer slots than its words times its tilings.
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
