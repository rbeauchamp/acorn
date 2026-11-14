/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission
import AcornVerif.CurrentConcealedTargetMission
import AcornVerif.CurrentCreditHorizon

/-!
# The first rung's class for the executed agent

`AcornVerif.CurrentConcealedTargetMission.executed_mission` proves the mission theorem's statement
of the executed agent from named premises, for every host world, visit length and agent state. This
module fixes those for the first rung of the mission's ladder (`docs/mission-contract.md`, section
"The mission theorem and its ladder") and proves what each choice rests on. `rung_mission` is the
statement at these constants.

## The constants

- **The world** is the world of the separation witness
  (`AcornVerif.CurrentConcealedTarget.witnessConfig`, `witnessLive`): the host's standard
  configuration at seed 5 and the smallest side, 64, with no deer and no food
  (`AcornVerif.CurrentConcealedTarget.witness_standard`), started at the box's center with full
  energy and a carried reward of zero. So its day, its noise scale and its terrain are those of the
  world the host builds at that seed and side.
- **A visit** is seven steps of the world.
- **The agent** is the cold agent the host constructs for the primitive research profile under the
  discounted criterion, at the world's seed and the default step order (`rungConstruction`), under
  either planning selection. The discounted criterion is the one the host's entry for runs of
  visits constructs.

The members the comparison counts are not fixed here: they are members the executed agent finds,
which the premise `ExecutedFinds` names.

## What each choice rests on

- **Every premise about the class is proved in this world**, the count of feasible members
  included: 147 feasible members against the covering bound 98
  (`AcornVerif.CurrentConcealedTarget.witness_big`). Every member's target lies within ten tiles of
  the start (`feasible_window`), so the class has at most 392 members (`rung_members`); that
  window, tiles 22 to 42 on both axes, lies inside the box.
- **No deer and no food, so that every frame is small.** A grid frame carries one word for each
  tile of its window, one more where the tile holds food and one more where it holds a deer. A
  world whose configuration admits neither (`Unpopulated`) holds neither in any state, by the bound
  its populations carry, so every percept it delivers has at most 139 words (`percept_words`), and
  every frame the standard feature configuration encodes from one has at most 1712 active slots
  (`standard_slots`, `rung_frames`). The theorems on how far back a first reward reaches
  (`AcornVerif.CurrentCreditHorizon.dormant_weight_rests`, `recent_weight_moves`) assume frames of
  at most 1999 and 1900 slots. For percepts of such a world the first holds with no hypothesis on
  frames (`unpopulated_weight_rests`, `rung_weight_rests`). The interface alone bounds a grid frame
  of that configuration by 3648 slots, eight tilings of 381 words and eleven questions, and 512
  units (`Acorn.Handcrafted.Agent.frame_length`). That is all that is proved of a world with deer
  and food.
- **A visit of seven steps is within the proved reach of a first reward.** A slot laid at most 81
  steps before a first reward of one has a weight the reward moves, on a controller's cold run
  (`recent_weight_moves`). A first reward arrives at most seven decisions after its visit's first,
  so it moves every weight that first decision laid (`rung_reach`). This is a statement about the
  primitive controller's cold run over frames of the rung's size, not yet about the agent's run.
  Seven is the visit length of the witness: the least at which a goal box at the end of a straight
  walk clears the start's box.

## What is not proved here

- No premise of `rung_mission` about the agent. Whether the executed agent finds and retains in
  this class is rbeauchamp/acorn#232.
- That the host can run this world. The host's entry `acorn-core visits` builds the standard
  configuration, with deer and food, and starts where its spawn search ends. No theorem relates a
  run of it to a member of this class.
- Anything about a longer visit or a world with deer and food. The constants are the smallest for
  which the class premises and the frame bound are proved; a larger class is a later rung.

Evaluating the terrain of one tile in Lean's kernel is slow (`docs/roadmap.md` records the
timing), and a proof about a world's layout pays for each tile it reads on every build. The
witness reads 21 tiles. A class with visits of 81 steps, the proved reach of a first reward, has
a covering bound of 616 and so needs the terrain of at least 89 tiles, and the spawn search of a
standard world reads some thousands.
-/

namespace AcornVerif.CurrentConcealedTargetRung
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentCreditHorizon
open AcornVerif.Intent AcornVerif.Intent.MissionTheorem

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

/-- A grid frame whose window holds no food and no deer has at most 139 words. -/
theorem bareWords_eq : bareWords = 139 := rfl

/-- The words of an observation with no food and no deer, in both task modes. -/
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
frames of such a world hold at most 1999 slots: from cold initialization, over percepts the world
delivers whose reward words are zero, and then any percepts at all, a primitive weight is a zero
word unless its row laid its slot in the window. It is
`AcornVerif.CurrentCreditHorizon.dormant_weight_rests` with its hypothesis on frames discharged. -/
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

/-! ## The window of a class of concealed targets -/

/-- Each point of a walk is within its index of the walk's first point, on both axes. -/
theorem walk_within (walk : ℕ → ℤ × ℤ) (near : ∀ index, Near (walk index) (walk (index + 1))) :
    ∀ index, walk index ∈ box index (walk 0)
  | 0 => mem_box.mpr ⟨by simp, by simp⟩
  | index + 1 => by
    have earlier := mem_box.mp (walk_within walk near index)
    have step := near index
    unfold Near at step
    refine mem_box.mpr ⟨?_, ?_⟩ <;> omega

/-- The points within a radius of a walk's first `steps + 1` points are within the radius and the
steps of its first point. -/
theorem swept_subset_box (radius : ℕ) (walk : ℕ → ℤ × ℤ)
    (near : ∀ index, Near (walk index) (walk (index + 1))) :
    ∀ steps, swept radius walk steps ⊆ box (radius + steps) (walk 0) := by
  have each : ∀ index steps, index ≤ steps →
      box radius (walk index) ⊆ box (radius + steps) (walk 0) := by
    intro index steps within point inside
    have here := mem_box.mp (walk_within walk near index)
    have close := mem_box.mp inside
    exact mem_box.mpr ⟨by omega, by omega⟩
  intro steps
  induction steps with
  | zero => exact each 0 0 (Nat.le_refl 0)
  | succ steps ih =>
    change swept radius walk steps ∪ box radius (walk (steps + 1)) ⊆ _
    refine Finset.union_subset (Finset.Subset.trans ih fun point inside => ?_)
      (each (steps + 1) (steps + 1) (Nat.le_refl _))
    have close := mem_box.mp inside
    exact mem_box.mpr ⟨by omega, by omega⟩

/-- **The window.** A concealed target that some action sequence meets within `length` steps lies
within `3 + length` tiles of the start on both axes. So the window of that radius around the start
holds every member of the class, whatever the terrain. -/
theorem feasible_window (mode : TaskFeatureMode) (live : Live config) (length : ℕ)
    (target : Host.Position)
    (feasible : Kernel.Feasible (completion config mode length) (member live target)) :
    tile target ∈ box (3 + length) (tile live.world.body.position.position) := by
  obtain ⟨actions, met⟩ := feasible
  exact swept_subset_box 3 (walk (physical live.world) actions)
    (walk_near (physical live.world) actions) length
    (find_met_swept mode live length actions target met)

/-- A class of feasible concealed targets has at most `(2 (3 + length) + 1)² - 49` members: the
tiles of its window less those within three tiles of the start. -/
theorem feasible_count (mode : TaskFeatureMode) (live : Live config) (length : ℕ)
    (members : Finset (feasibleFind config mode live length).Index) :
    members.card ≤ (2 * (3 + length) + 1) * (2 * (3 + length) + 1) - 49 := by
  classical
  have inside : members.image (fun target => tile target.1.1) ⊆
      box (3 + length) (tile live.world.body.position.position) \
        box 3 (tile live.world.body.position.position) := by
    intro point chosen
    obtain ⟨target, -, rfl⟩ := Finset.mem_image.mp chosen
    exact Finset.mem_sdiff.mpr ⟨feasible_window mode live length target.1.1 target.2,
      (member_tile live target.1.1).mp target.1.2⟩
  have nested : box 3 (tile live.world.body.position.position) ⊆
      box (3 + length) (tile live.world.body.position.position) := by
    intro point close
    have near := mem_box.mp close
    exact mem_box.mpr ⟨by omega, by omega⟩
  calc members.card
      = (members.image (fun target => tile target.1.1)).card :=
        (Finset.card_image_of_injective members fun first second same =>
          Subtype.ext (Subtype.ext (tile_injective same))).symm
    _ ≤ (box (3 + length) (tile live.world.body.position.position) \
          box 3 (tile live.world.body.position.position)).card := Finset.card_le_card inside
    _ = (2 * (3 + length) + 1) * (2 * (3 + length) + 1) - 49 := by
        rw [Finset.card_sdiff_of_subset nested, card_box, card_box]

/-! ## The first rung -/

/-- The witness's configuration admits no deer and no food. -/
theorem witness_unpopulated : Unpopulated witnessConfig := ⟨rfl, rfl⟩

/-- The construction of the first rung's agent: the one the host builds for the primitive research
profile under the discounted criterion, at the seed of the rung's world and the default step
order, under a planning selection. -/
def rungConstruction (planning : PlanningSelection) : AgentConstruction :=
  AgentConstruction.standard witnessConfig.raw.seed ⟨.primitive, .discounted⟩ planning
    .learnThenAct

/-- The standard feature configuration encodes a frame of a world with no deer and no food in at
most 1712 slots: eight tilings of its 139 words and eleven questions, and 512 units. -/
theorem standard_slots (seed : UInt64) (selection : Host.AgentSelection)
    (planning : PlanningSelection) (order : StepOrder) :
    bareSlots (AgentConstruction.standard seed selection planning order).config = 1712 := by
  change Acorn.FeatureConstants.defaultTilings.toUInt64.toNat *
    (bareWords + Grid.interface.layout.length) + Acorn.FeatureConstants.defaultImprintUnits = 1712
  decide

/-- **The frames of the first rung.** Over percepts the rung's world delivers, every step of the
rung's agent lays a frame of at most 1712 slots, from every state and under every step order. -/
theorem rung_frames (planning : PlanningSelection) (mode : TaskFeatureMode) (order : StepOrder)
    (percepts : List (Percept Grid.interface)) (delivered : Delivered witnessConfig mode percepts)
    (state : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning) :
    ∀ step ∈ (traced order state percepts).2, step.features.indices.length ≤ 1712 :=
  fun step member => Nat.le_trans
    (unpopulated_fits witness_unpopulated mode order percepts delivered state step member)
    (Nat.le_of_eq (standard_slots _ _ _ _))

/-- **The credit horizon of the first rung.** For the rung's agent from cold initialization, over
percepts the rung's world delivers whose reward words are zero, and then any percepts at all, a
primitive weight is a zero word unless its row laid its slot in the window: the last 119 steps
without reward and every later step. No hypothesis on frames remains. -/
theorem rung_weight_rests (planning : PlanningSelection) (mode : TaskFeatureMode)
    (order : StepOrder) (quiet post : List (Percept Grid.interface))
    (delivered : Delivered witnessConfig mode quiet)
    (silent : ∀ percept ∈ quiet, percept.reward.isZero = true) :
    let start := (rungConstruction planning).initial.agent
    let first := traced order start quiet
    let second := traced order first.1 post
    ∀ (row : Action Grid.interface.actions.word.toNat)
      (slot : FeatIdx (rungConstruction planning).dimension),
      (∀ step ∈ window (rungConstruction planning).criterion first.2 second.2,
        ¬step.Lays row slot) →
      (((controlOf second.1).learners.get row).state.weights.get slot).value.isZero = true :=
  unpopulated_weight_rests witness_unpopulated mode _ _ _ _ _ order rfl
    (Nat.le_trans (Nat.le_of_eq (standard_slots _ _ _ _)) (by decide)) quiet post delivered silent

/-- **A visit of the first rung is within the proved reach of a first reward.** On a primitive
controller's cold run over frames of the rung's size, a slot that a step laid, followed by at most
six more steps, has a weight that a reward of one at the next step moves, under either criterion.
In a visit of seven steps a first reward arrives at most seven decisions after the visit's first,
so it moves every weight that first decision laid. The statement is of the controller's run, not
of the agent's. -/
theorem rung_reach (criterion : Criterion) (dimension : Dimension) {actions : Nat}
    (before after : List (Laid dimension actions)) (laid : Laid dimension actions)
    (slot : FeatIdx dimension) (held : slot ∈ laid.features.indices)
    (within : after.length + 1 ≤ 7)
    (fits : ∀ step ∈ before ++ laid :: after, step.features.indices.length ≤ 1712)
    (next : Laid dimension actions) :
    let quiet : Controller (criterion.config .control) dimension actions :=
      quietRun (before ++ laid :: after)
    (((quiet.step next.features next.row .one).1.learners.get laid.row).state.weights.get
      slot).value.isZero = false :=
  recent_weight_moves criterion dimension before after laid slot held (by omega)
    (fun step member => Nat.le_trans (fits step member) (by decide)) next

/-- **The members of the first rung.** Every member's target lies within ten tiles of the start
on both axes, so the class has at most 392 members; 147 of them are proved feasible
(`AcornVerif.CurrentConcealedTarget.witness_big`), against a covering bound of 98. -/
theorem rung_members (mode : TaskFeatureMode)
    (members : Finset (feasibleFind witnessConfig mode witnessLive 7).Index) :
    members.card ≤ 392 :=
  feasible_count mode witnessLive 7 members

/-- **The mission theorem on the first rung, from its named premises.** In the rung's world, with
visits of seven steps and a list of distinct counted members: if the rung's agent finds and
retains, then every agent that takes its actions, and whose own memory and reports meet the four
premises of contract 3, achieves goals over the class. It is
`AcornVerif.CurrentConcealedTargetMission.executed_mission` at the rung's constants; no premise is
proved. -/
theorem rung_mission (planning : PlanningSelection)
    (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
      witnessLive 7).Index)
    (distinct : counted.Nodup) {agent : Kernel.Agent Grid.interface}
    (acts : ActsAsExecuted (rungConstruction planning).initial.agent agent)
    {updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept Grid.interface × ℚ → ℕ}
    {resume : agent.Memory → agent.Memory}
    (finds : ExecutedFinds (rungConstruction planning).initial.agent witnessConfig witnessLive 7
      counted)
    (retains : ExecutedRetains (rungConstruction planning).initial.agent witnessConfig
      witnessLive 7)
    (memory : MemoryBounded (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 counted agent updates work
      resume))
    (bounded : WorkBounded (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 counted agent updates work
      resume))
    (arrival : LearnsOnArrival (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 counted agent updates work
      resume))
    (discipline : KeepsDiscipline (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 counted agent updates work
      resume)) :
    Mission (findRung witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7
      counted agent updates work resume) :=
  executed_mission (rungConstruction planning).initial.agent witnessConfig witnessLive 7 rfl
    counted distinct acts finds retains memory bounded arrival discipline

end AcornVerif.CurrentConcealedTargetRung
