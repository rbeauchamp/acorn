/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentConstruction
import AcornVerif.CurrentCreditHorizon
import AcornVerif.CurrentGridWorld

/-!
# The size of a grid frame

The theorems on how far back a first reward reaches assume frames of at most 1999 active slots
(`AcornVerif.CurrentCreditHorizon.dormant_weight_rests`, `candidates_read_window`) or 1900
(`recent_weight_moves`). The interface alone bounds a frame by its tilings times the most words it
allows and its prediction questions, and its units (`Acorn.Handcrafted.Agent.frame_length`): for
the grid interface under the standard feature configuration that is eight tilings of 381 words and
eleven questions, and 512 units, 3648 slots. This module bounds a frame by the words its percept
carries (`frame_slots`), and bounds those words in a grid world that holds no deer and no food.

A grid frame carries one word for each of the 121 tiles of its window, one more where the tile
holds food and one more where it holds a deer, then energy and day, at most ten task words and six
inventory words. A world whose configuration admits no deer and no food (`Unpopulated`) holds
neither in any state, by the bound its populations carry. So every percept it delivers has at most
139 words (`percept_words`), at every state of the grid world, the refused state included. Every
frame the executed agent lays from such a percept, under every step order, then has at most
`bareSlots` slots (`unpopulated_fits`), which is 1712 for the standard feature configuration
(`standard_slots`). So for percepts of such a world the credit horizon holds with no hypothesis on
frames (`unpopulated_weight_rests`).

What this does not say. No theorem here bounds a frame of a world with deer or food below the
interface's bound: that needs a bound on how many deer and how much food a window can hold along a
run. `unpopulated_weight_rests` discharges the hypothesis of `dormant_weight_rests` alone;
`recent_weight_moves` is about a controller's run and takes the size of its frames as given.
-/

namespace AcornVerif.CurrentFrameSize
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentCreditHorizon

/-! ## A world with no deer and no food -/

/-- A configuration that admits no deer and no food. -/
def Unpopulated (config : Host.WorldConfig) : Prop :=
  config.raw.deerCap = 0 ∧ config.raw.foodCap = 0

variable {config : Host.WorldConfig}

/-- A world of a configuration that admits no deer holds none: its population carries the bound. -/
theorem deer_empty (bare : Unpopulated config) (world : Host.World config) :
    world.deer.entries = #[] := by
  have bound := world.deer.bounded
  have none : config.raw.deerCap.toNat = 0 := by rw [bare.1]; rfl
  exact Array.eq_empty_of_size_eq_zero (by omega)

/-- A world of a configuration that admits no food holds none. -/
theorem food_empty (bare : Unpopulated config) (world : Host.World config) :
    world.food.entries = #[] := by
  have bound := world.food.bounded
  have none : config.raw.foodCap.toNat = 0 := by rw [bare.2]; rfl
  exact Array.eq_empty_of_size_eq_zero (by omega)

/-- The occupancy index of a world with no deer and no food is empty. -/
theorem occupancy_empty (bare : Unpopulated config) (world : Host.World config) :
    world.occupancy = ∅ := by
  unfold Host.World.occupancy
  rw [deer_empty bare world, food_empty bare world]
  rfl

/-- A tile observed against an empty occupancy index holds no food and no deer. -/
theorem observeTile_bare (world : Host.World config) (row column : Fin Host.patchSide)
    (tile : Host.TileObservation) (seen : world.observeTile ∅ row column = .ok tile) :
    tile.food = 0 ∧ tile.deer = 0 := by
  unfold Host.World.observeTile at seen
  dsimp only at seen
  cases translated : world.body.position.position.translate
      ((column.val : Int) - (Host.patchSide / 2 : Nat))
      ((row.val : Int) - (Host.patchSide / 2 : Nat)) with
  | none =>
    rw [translated] at seen
    cases seen
  | some position =>
    rw [translated] at seen
    cases kinded : world.tileKind position with
    | error refusal =>
      simp only [kinded, bind, Except.bind] at seen
      cases seen
    | ok kind =>
      simp only [kinded, bind, Except.bind, pure, Except.pure, Std.TreeMap.getElem?_emptyc,
        Option.getD_none, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at seen
      rw [← seen]
      exact ⟨rfl, rfl⟩

/-- Every entry of a vector a fallible function builds has what every entry the function returns
has. -/
theorem ofFnM_each {ε α : Type} (holds : α → Prop) :
    ∀ {count : Nat} (make : Fin count → Except ε α) (values : Vector α count),
      (∀ index value, make index = .ok value → holds value) →
      Vector.ofFnM make = .ok values → ∀ (index : Nat) (inside : index < count), holds values[index]
  | 0, _, _, _, _, _, inside => absurd inside (Nat.not_lt_zero _)
  | count + 1, make, values, each, built, index, inside => by
    rw [Vector.ofFnM_succ] at built
    cases front : Vector.ofFnM (fun earlier : Fin count => make earlier.castSucc) with
    | error refusal =>
      simp only [front, bind, Except.bind] at built
      cases built
    | ok head =>
      cases last : make (Fin.last count) with
      | error refusal =>
        simp only [front, last, bind, Except.bind] at built
        cases built
      | ok tail =>
        simp only [front, last, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at built
        subst built
        rw [Vector.getElem_push]
        split
        · exact ofFnM_each holds _ head (fun earlier value made => each earlier.castSucc value made)
            front index ‹_›
        · exact each _ _ last

/-- An observation whose window holds no food and no deer. -/
def Bare (observation : Host.Observation) : Prop :=
  ∀ row column : Fin Host.patchSide,
    ((observation.tiles.get row).get column).food = 0 ∧
      ((observation.tiles.get row).get column).deer = 0

/-- The observation that stands in for a refused one holds no food and no deer. -/
theorem blank_bare : Bare blank := by
  intro row column
  simp [blank, Vector.get]

/-- Every observation of a world with no deer and no food holds neither. -/
theorem observe_bare (bare : Unpopulated config) (world : Host.World config)
    (observation : Host.Observation) (seen : world.observe = .ok observation) :
    Bare observation := by
  unfold Host.World.observe at seen
  rw [occupancy_empty bare world] at seen
  cases built : Vector.ofFnM (fun row => Vector.ofFnM (world.observeTile ∅ row)) with
  | error refusal =>
    simp only [built, bind, Except.bind] at seen
    cases seen
  | ok tiles =>
    simp only [built, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at seen
    subst seen
    intro row column
    have rows := ofFnM_each
      (fun cells : Vector Host.TileObservation Host.patchSide =>
        ∀ (index : Nat) (inside : index < Host.patchSide),
          cells[index].food = 0 ∧ cells[index].deer = 0)
      (fun row => Vector.ofFnM (world.observeTile ∅ row)) tiles
      (fun row cells made => ofFnM_each (fun tile => tile.food = 0 ∧ tile.deer = 0)
        (world.observeTile ∅ row) cells (fun column tile => observeTile_bare world row column tile)
        made)
      built row.val row.isLt column.val column.isLt
    exact rows

/-- What an agent senses of a world with no deer and no food holds neither. -/
theorem sensed_bare (bare : Unpopulated config) (world : Host.World config) :
    Bare (sensed world) := by
  unfold sensed
  split
  · exact observe_bare bare world _ ‹_›
  · exact blank_bare

/-! ## The words of a frame -/

/-- A tile with no food and no deer contributes its kind word alone. -/
theorem tileWords_bare (row column : Fin Host.patchSide) (tile : Host.TileObservation)
    (food : tile.food = 0) (deer : tile.deer = 0) : (tileWords row column tile).length ≤ 1 := by
  simp [tileWords, food, deer]

/-- Most words of a grid frame whose window holds no food and no deer: one for each tile of the
window, energy and day, the task context, and six inventory words. -/
def bareWords : ℕ :=
  Host.patchSide * Host.patchSide + 2 + Acorn.FeatureConstants.taskContextWords + 6

/-- The bound `bareWords` is 139. -/
theorem bareWords_eq : bareWords = 139 := rfl

/-- An observation whose window holds no food and no deer has at most `bareWords` words, in both
task modes. -/
theorem sensorWords_bare (observation : Host.Observation) (mode : TaskFeatureMode)
    (bare : Bare observation) : (sensorWords observation mode).length ≤ bareWords := by
  have tiles := flatMap_length_le (List.finRange Host.patchSide)
    (fun row => (List.finRange Host.patchSide).flatMap fun column =>
      tileWords row column ((observation.tiles.get row).get column)) Host.patchSide
    (fun row => by
      have cells := flatMap_length_le (List.finRange Host.patchSide)
        (fun column => tileWords row column ((observation.tiles.get row).get column)) 1
        (fun column => tileWords_bare row column _ (bare row column).1 (bare row column).2)
      simpa [List.length_finRange] using cells)
  have task := taskWords_fit observation.task mode
  simp only [List.length_finRange] at tiles
  simp only [sensorWords, List.length_append, List.length_cons, List.length_nil, bareWords]
  omega

/-- **Every percept of a world with no deer and no food has at most 139 words**, at every state
of the grid world, the refused state included. -/
theorem percept_words (bare : Unpopulated config) (mode : TaskFeatureMode)
    (state : Option (Live config)) :
    ((gridWorld config mode).percept state).frame.words.length ≤ bareWords := by
  cases state with
  | none => exact sensorWords_bare blank mode blank_bare
  | some live => exact sensorWords_bare (sensed live.world) mode (sensed_bare bare live.world)

/-! ## The slots of a frame -/

section Slots

variable {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- The active slots of a frame are bounded by the words the frame carries, where
`Acorn.Handcrafted.Agent.frame_length` bounds them by the most the interface allows. -/
theorem frame_slots (state : Agent interface profile features criterion dimension planning)
    (observation : Frame interface) :
    (state.frame observation).active.indices.length ≤
      features.tilings.toNat * (observation.words.length + interface.layout.length) +
        features.units.count := by
  have feedback := feedbackWords_length interface.feedback interface.layout
    state.control.runtime.references.demonPredictions.words 0
  have read : (state.words observation).length ≤
      observation.words.length + interface.layout.length := by
    simp only [Agent.words_def, List.length_append]
    omega
  rw [(state.frame observation).fresh]
  exact Nat.le_trans (encode_length dimension _ (state.words observation) observation.symbols)
    (Nat.add_le_add_right (Nat.mul_le_mul_left features.tilings.toNat read) _)

/-- The frame a step lays, under every step order, is bounded by the words of its percept. -/
theorem choose_slots (state : Agent interface profile features criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    (state.choose order percept).features.indices.length ≤
      features.tilings.toNat * (percept.frame.words.length + interface.layout.length) +
        features.units.count := by
  have same : (state.choose order percept).features =
      (state.advanceClock.frame percept.frame).active := by
    cases order with
    | actThenLearn => exact (state.choose_drawn percept).2.2.2.1
    | learnThenAct => exact (state.choose_selected .learnThenAct (by decide) percept).2.2.2.1
    | planAfterAct => exact (state.choose_selected .planAfterAct (by decide) percept).2.2.2.1
  rw [same]
  exact frame_slots state.advanceClock percept.frame

/-- Over percepts of at most `words` words, every step of the executed agent lays a frame of at
most `tilings * (words + questions) + units` slots. -/
theorem traced_slots (order : StepOrder) (words : ℕ) :
    ∀ (percepts : List (Percept interface))
      (state : Agent interface profile features criterion dimension planning),
      (∀ percept ∈ percepts, percept.frame.words.length ≤ words) →
      ∀ step ∈ (traced order state percepts).2, step.features.indices.length ≤
        features.tilings.toNat * (words + interface.layout.length) + features.units.count
  | [], _, _, _, member => nomatch member
  | percept :: rest, state, fits, step, member => by
    change step ∈ _ :: (traced order (state.choose order percept).learn rest).2 at member
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_trans (choose_slots state order percept)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _
          (Nat.add_le_add_right (fits percept (List.mem_cons_self ..)) _)) _)
    · exact traced_slots order words rest _
        (fun other held => fits other (List.mem_cons_of_mem _ held)) step later

end Slots

/-! ## The credit horizon in a world with no deer and no food -/

/-- The percepts of a list are percepts the grid world of a configuration delivers. -/
def Delivered (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (percepts : List (Percept Grid.interface)) : Prop :=
  ∀ percept ∈ percepts, ∃ state : Option (Live config),
    percept = (gridWorld config mode).percept state

/-- Most active slots of a frame of a world with no deer and no food, under a feature
configuration: its tilings times the frame's words and the eleven prediction questions, and its
units. -/
def bareSlots (features : Features.Config) : ℕ :=
  features.tilings.toNat * (bareWords + Grid.interface.layout.length) + features.units.count

section Horizon

variable {profile : FeatureProfile} {features : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {planning : PlanningSelection}

/-- Over percepts a world with no deer and no food delivers, every step of the executed agent
lays a frame of at most `bareSlots` slots, from every state and under every step order. -/
theorem unpopulated_fits (bare : Unpopulated config) (mode : TaskFeatureMode) (order : StepOrder)
    (percepts : List (Percept Grid.interface)) (delivered : Delivered config mode percepts)
    (state : Agent Grid.interface profile features criterion dimension planning) :
    ∀ step ∈ (traced order state percepts).2,
      step.features.indices.length ≤ bareSlots features :=
  traced_slots order bareWords percepts state fun percept held => by
    obtain ⟨world, rfl⟩ := delivered percept held
    exact percept_words bare mode world

end Horizon

/-- **The credit horizon in a world with no deer and no food.** For a feature configuration whose
bound `bareSlots` is at most 1999: from cold initialization, over percepts the world delivers whose
reward words are zero, and then any percepts at all, a primitive weight is a zero word unless its
row laid its slot in the window. It is `AcornVerif.CurrentCreditHorizon.dormant_weight_rests` with
its hypothesis on frames discharged. -/
theorem unpopulated_weight_rests (bare : Unpopulated config) (mode : TaskFeatureMode)
    (profile : FeatureProfile) (features : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (planning : PlanningSelection) (order : StepOrder)
    (perStep : profile.credit = .perStep) (small : bareSlots features ≤ 1999)
    (quiet post : List (Percept Grid.interface)) (delivered : Delivered config mode quiet)
    (silent : ∀ percept ∈ quiet, percept.reward.isZero = true) :
    let start := Agent.initial Grid.interface profile features criterion dimension planning
    let first := traced order start quiet
    let second := traced order first.1 post
    ∀ (row : Action Grid.interface.actions.word.toNat) (slot : FeatIdx dimension),
      (∀ step ∈ window criterion first.2 second.2, ¬step.Lays row slot) →
      (((controlOf second.1).learners.get row).state.weights.get slot).value.isZero = true :=
  dormant_weight_rests Grid.interface profile features criterion dimension planning order perStep
    quiet post silent fun step member =>
      Nat.le_trans (unpopulated_fits bare mode order quiet delivered _ step member) small

/-- The standard feature configuration encodes a frame of a world with no deer and no food in at
most 1712 slots: eight tilings of its 139 words and eleven questions, and 512 units. -/
theorem standard_slots (seed : UInt64) (selection : Host.AgentSelection)
    (planning : PlanningSelection) (order : StepOrder) :
    bareSlots (AgentConstruction.standard seed selection planning order).config = 1712 := by
  change Acorn.FeatureConstants.defaultTilings.toUInt64.toNat *
    (bareWords + Grid.interface.layout.length) + Acorn.FeatureConstants.defaultImprintUnits = 1712
  decide

end AcornVerif.CurrentFrameSize
