/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentForkedTargetBoth
import AcornVerif.CurrentForkedTargetRung

/-!
# A grid of members of the rung by day and by night, and an agent that masters it

`AcornVerif.Kernel.MastersGridBy` asks for a set of first targets and a set of second targets,
each larger than the bound, every pair of which is a member the agent solves in both situations.
This module shows that the rung's class holds such a grid at the sharp bound 49, and that an
agent built for the purpose masters it and keeps it.

**The grid.** `dayTiles` holds 56 first targets: the 28 tiles of columns 22 to 25 and rows 29 to
35, west of the start, and the 28 of columns 29 to 35 and rows 39 to 42, south of it. `duskTiles`
holds 56 second targets: the 28 of columns 39 to 42 and rows 29 to 35, to the east, and the 28 of
columns 29 to 35 and rows 22 to 25, to the north. Each first target asks for at least four moves
west or four moves south, and each second for at least four east or four north, so every one of
the 3136 pairs is a fork (`grid_apart`): a visit has seven moves. Each first target is met from
the first situation's start by the witness's walk west or south
(`AcornVerif.CurrentConcealedTarget.witness_walk`), and each second from the second's by seven
steps east or north, which the kernel evaluates (`dusk_grid_walk`).

**The agent.** `gridWitness` is `AcornVerif.Kernel.switch` over two replaying agents: by day it
explores east, west and then south on its own visits, and by night east and then north. It reads
the situation from the first percept of each visit and replays the actions of a visit that met
the target. Under the alternating order, on visit 5, it solves every member of the grid in both
situations (`grid_witness_masters`), and it keeps with no lapse under every order
(`grid_witness_keeps`). It is evidence that the promises are satisfiable and is not an agent of
the executed type: it records a route for each situation it reads and replays it.
-/

namespace AcornVerif.CurrentForkedTargetRungBoth
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentForkedTarget
open AcornVerif.CurrentForkedTargetBoth AcornVerif.CurrentForkedTargetRung

/-! ## The grid's targets -/

/-- The tiles of the grid's first targets: a strip west of the start and a strip south of it. -/
def dayTiles : Finset (ℤ × ℤ) :=
  Finset.Icc 22 25 ×ˢ Finset.Icc 29 35 ∪ Finset.Icc 29 35 ×ˢ Finset.Icc 39 42

/-- The tiles of the grid's second targets: a strip east of the start and a strip north of
it. -/
def duskTiles : Finset (ℤ × ℤ) :=
  Finset.Icc 39 42 ×ˢ Finset.Icc 29 35 ∪ Finset.Icc 29 35 ×ˢ Finset.Icc 22 25

/-- The grid has 56 first targets. -/
theorem dayTiles_card : dayTiles.card = 56 := by
  decide

/-- The grid has 56 second targets. -/
theorem duskTiles_card : duskTiles.card = 56 := by
  decide

/-- Where a first target of the grid lies: at least seven tiles west of the start, or at least
seven south of it, and within three of the end of the witness's walk west or south. -/
theorem dayTiles_spec (point : ℤ × ℤ) (inside : point ∈ dayTiles) :
    (-100 ≤ point.1 ∧ point.1 ≤ 100 ∧ -100 ≤ point.2 ∧ point.2 ≤ 100) ∧
      point ∉ box 3 (32, 32) ∧ (point.1 ≤ 25 ∨ 39 ≤ point.2) ∧
      ∃ visit, 1 ≤ visit ∧ visit ≤ 2 ∧ point ∈ box 3 (witnessEnd visit) := by
  simp only [dayTiles, Finset.mem_union, Finset.mem_product, Finset.mem_Icc] at inside
  rcases inside with west | south
  · refine ⟨by omega, fun close => ?_, Or.inl (by omega), 1, Nat.le_refl 1, by decide, ?_⟩
    · rw [mem_box] at close
      omega
    · rw [mem_box]
      simp only [witnessEnd]
      omega
  · refine ⟨by omega, fun close => ?_, Or.inr (by omega), 2, by decide, Nat.le_refl 2, ?_⟩
    · rw [mem_box] at close
      omega
    · rw [mem_box]
      simp only [witnessEnd]
      omega

/-- The exploration of the second situation's replaying agent: east at every step of its first
visit, and north on every later one. -/
def duskExplore (visit : ℕ) (_ : ℕ) : Kernel.Act Grid.interface :=
  code (match visit with | 0 => .east | _ => .north)

/-- The tile each of those visits ends on: seven tiles east and seven north of the center. -/
def duskEnd : ℕ → ℤ × ℤ
  | 0 => (39, 32)
  | _ => (32, 25)

/-- Seven steps east, and seven steps north, carry the body from the second situation's start to
those end tiles. The kernel evaluates the executed world step along the two walks. -/
theorem dusk_grid_walk (visit : ℕ) (within : visit ≤ 1) :
    (physicalPath (physical duskLive.world) (duskExplore visit) 7).map
      (fun world => tile world.body.position.position) = some (duskEnd visit) := by
  rcases (by omega : visit = 0 ∨ visit = 1) with rfl | rfl
  · decide +kernel
  · decide +kernel

/-- Where a second target of the grid lies: at least seven tiles east of the start, or at least
seven north of it, and within three of the end of a walk east or north. -/
theorem duskTiles_spec (point : ℤ × ℤ) (inside : point ∈ duskTiles) :
    (-100 ≤ point.1 ∧ point.1 ≤ 100 ∧ -100 ≤ point.2 ∧ point.2 ≤ 100) ∧
      point ∉ box 3 (32, 32) ∧ (39 ≤ point.1 ∨ point.2 ≤ 25) ∧
      ∃ visit, visit ≤ 1 ∧ point ∈ box 3 (duskEnd visit) := by
  simp only [duskTiles, Finset.mem_union, Finset.mem_product, Finset.mem_Icc] at inside
  rcases inside with east | north
  · refine ⟨by omega, fun close => ?_, Or.inl (by omega), 0, Nat.zero_le 1, ?_⟩
    · rw [mem_box] at close
      omega
    · rw [mem_box]
      simp only [duskEnd]
      omega
  · refine ⟨by omega, fun close => ?_, Or.inr (by omega), 1, Nat.le_refl 1, ?_⟩
    · rw [mem_box] at close
      omega
    · rw [mem_box]
      simp only [duskEnd]
      omega

/-- The first target at a tile of the grid, as a member of the first situation's feasible
targets. -/
def dayIndex (mode : TaskFeatureMode) (point : { point // point ∈ dayTiles }) :
    (feasibleFind witnessConfig mode witnessLive 7).Index :=
  ⟨⟨pointPosition point.1, by
      rw [member_tile, witness_start, tile_point point.1 (dayTiles_spec point.1 point.2).1]
      exact (dayTiles_spec point.1 point.2).2.1⟩, by
    obtain ⟨small, -, -, visit, low, high, near⟩ := dayTiles_spec point.1 point.2
    refine ⟨witnessExplore visit, 7, by omega, Nat.le_refl 7,
      witness_meets mode 7 visit high _ ?_⟩
    rw [tile_point point.1 small]
    exact near⟩

/-- The second target at a tile of the grid, as a member of the second situation's feasible
targets. -/
def duskIndex (mode : TaskFeatureMode) (point : { point // point ∈ duskTiles }) :
    (feasibleFind witnessConfig mode duskLive 7).Index :=
  ⟨⟨pointPosition point.1, by
      rw [member_tile, dusk_start, tile_point point.1 (duskTiles_spec point.1 point.2).1]
      exact (duskTiles_spec point.1 point.2).2.1⟩, by
    obtain ⟨small, -, -, visit, within, near⟩ := duskTiles_spec point.1 point.2
    refine ⟨duskExplore visit, 7, by omega, Nat.le_refl 7,
      find_near_met mode duskLive 7 (duskExplore visit) 7 (duskEnd visit)
        (dusk_grid_walk visit within) _ ?_⟩
    rw [tile_point point.1 small]
    exact near⟩

/-- **Every pair of the grid is a fork.** No single action sequence meets, within a visit, a
first target of the grid from the first situation's start and a second target of the grid from
the second's: the first asks for four moves west or south, the second for four east or north,
and a visit has seven. -/
theorem grid_apart (mode : TaskFeatureMode) (one : { point // point ∈ dayTiles })
    (two : { point // point ∈ duskTiles }) (actions : ℕ → Kernel.Act Grid.interface) :
    ¬ ((completion witnessConfig mode 7).MetBy (member witnessLive (pointPosition one.1))
        actions ∧
      (completion witnessConfig mode 7).MetBy (member duskLive (pointPosition two.1))
        actions) := by
  rintro ⟨day, dusk⟩
  obtain ⟨smallOne, -, whereOne, -⟩ := dayTiles_spec one.1 one.2
  obtain ⟨smallTwo, -, whereTwo, -⟩ := duskTiles_spec two.1 two.2
  have first := met_takes mode witnessLive 7 actions _ day
  have second := met_takes mode duskLive 7 actions _ dusk
  rw [witness_start, tile_point one.1 smallOne] at first
  rw [dusk_start, tile_point two.1 smallTwo] at second
  have westEast := taken_pair actions .west .east (by decide) 7
  have westNorth := taken_pair actions .west .north (by decide) 7
  have southEast := taken_pair actions .south .east (by decide) 7
  have southNorth := taken_pair actions .south .north (by decide) 7
  dsimp only at first second
  omega

/-- The member of the rung's class at a first and a second target of the grid. -/
def gridPair (mode : TaskFeatureMode) (one : { point // point ∈ dayTiles })
    (two : { point // point ∈ duskTiles }) : (rungForks mode).Index :=
  ⟨(dayIndex mode one, duskIndex mode two), grid_apart mode one two⟩

/-- Different tiles give different first targets. -/
theorem dayIndex_injective (mode : TaskFeatureMode) : Function.Injective (dayIndex mode) := by
  intro one two same
  have tiles := congrArg
    (fun target : (feasibleFind witnessConfig mode witnessLive 7).Index => tile target.1.1) same
  change tile (pointPosition one.1) = tile (pointPosition two.1) at tiles
  rw [tile_point one.1 (dayTiles_spec one.1 one.2).1,
    tile_point two.1 (dayTiles_spec two.1 two.2).1] at tiles
  exact Subtype.ext tiles

/-- Different tiles give different second targets. -/
theorem duskIndex_injective (mode : TaskFeatureMode) : Function.Injective (duskIndex mode) := by
  intro one two same
  have tiles := congrArg
    (fun target : (feasibleFind witnessConfig mode duskLive 7).Index => tile target.1.1) same
  change tile (pointPosition one.1) = tile (pointPosition two.1) at tiles
  rw [tile_point one.1 (duskTiles_spec one.1 one.2).1,
    tile_point two.1 (duskTiles_spec two.1 two.2).1] at tiles
  exact Subtype.ext tiles

/-- The grid's 56 first targets. -/
def gridFirsts (mode : TaskFeatureMode) :
    Finset (feasibleFind witnessConfig mode witnessLive 7).Index :=
  dayTiles.attach.map ⟨dayIndex mode, dayIndex_injective mode⟩

/-- The grid's 56 second targets. -/
def gridSeconds (mode : TaskFeatureMode) :
    Finset (feasibleFind witnessConfig mode duskLive 7).Index :=
  duskTiles.attach.map ⟨duskIndex mode, duskIndex_injective mode⟩

/-! ## An agent that masters the grid and keeps it -/

/-- The replaying agent of each situation: by day it explores as the first rung's witness does,
and by night east and then north. -/
def gridAgents : Bool → Kernel.Agent Grid.interface
  | false => Kernel.replay Grid.interface 7 achievedSignal witnessExplore
  | true => Kernel.replay Grid.interface 7 achievedSignal duskExplore

/-- Evidence that mastery of a grid can be met, built for that purpose: the switch over the two
replaying agents. It reads the situation from the first percept of each visit, records the
actions of a visit that met the target, and replays them. -/
def gridWitness : Kernel.Agent Grid.interface :=
  Kernel.switch showsDusk 7 gridAgents

/-- **The grid's witness keeps with no lapse**, before every horizon and under every order. -/
theorem grid_witness_keeps (mode : TaskFeatureMode) (horizon : ℕ) :
    Kernel.KeepsBut (rungForks mode) (rungForkGoals mode) 7 horizon 0 gridWitness :=
  Kernel.switch_keeps (rungForks mode) (rungForkGoals mode) 7 showsDusk gridAgents
    (witness_reads mode)
    (fun situation index visit later after solved => by
      cases situation
      · exact Kernel.replay_solves ((rungForks mode).side false) (rungForkGoals mode) 7
          achievedSignal witnessExplore index (achieved_decodes witnessConfig mode 7) visit
          later after solved
      · exact Kernel.replay_solves ((rungForks mode).side true) (rungForkGoals mode) 7
          achievedSignal duskExplore index (achieved_decodes witnessConfig mode 7) visit later
          after solved)
    horizon

/-- **The grid's witness masters the grid.** Under the alternating order, on visit 5, it solves
each of the 3136 members of the grid in both situations, at the sharp covering bound 49, with
every visit admitted. So it masters a grid before every limit of at least 6, at every horizon
and every number of lapses, under the predicate that admits every visit. -/
theorem grid_witness_masters (mode : TaskFeatureMode) (horizon lapses : ℕ) :
    Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 49
      (firstTarget mode witnessLive duskLive 7) (secondTarget mode witnessLive duskLive 7)
      6 horizon lapses (fun _ _ _ => True) gridWitness := by
  refine ⟨alternate, 5, gridFirsts mode, gridSeconds mode, by decide, ?_, ?_,
    fun one inFirsts two inSeconds => ?_⟩
  · rw [gridFirsts, Finset.card_map, Finset.card_attach, dayTiles_card]
    decide
  · rw [gridSeconds, Finset.card_map, Finset.card_attach, duskTiles_card]
    decide
  obtain ⟨day, -, rfl⟩ := Finset.mem_map.mp inFirsts
  obtain ⟨dusk, -, rfl⟩ := Finset.mem_map.mp inSeconds
  refine ⟨gridPair mode day dusk, rfl, rfl, fun situation =>
    ⟨?_, ∅, Nat.zero_le lapses, fun _ _ _ => trivial⟩⟩
  refine (Kernel.switch_turn (rungForks mode) (rungForkGoals mode) 7 showsDusk gridAgents
    (Function.update alternate 5 situation) 5 (gridPair mode day dusk)
    (witness_reads mode _)).mpr ?_
  rw [Function.update_self,
    Kernel.seen_congr (Function.update alternate 5 situation) alternate situation 5
      (fun _ before => Function.update_of_ne (Nat.ne_of_lt before) _ _)]
  cases situation
  · have count : Kernel.seen alternate false 5 = 3 := by decide
    obtain ⟨small, -, -, visit, -, high, near⟩ := dayTiles_spec day.1 day.2
    rw [count]
    refine Kernel.replay_solves_explored ((rungForks mode).side false) (rungForkGoals mode) 7
      achievedSignal witnessExplore _ (achieved_decodes witnessConfig mode 7) visit 3
      (by omega) ⟨7, by omega, Nat.le_refl 7, witness_meets mode 7 visit high _ ?_⟩
    change tile (pointPosition day.1) ∈ box 3 (witnessEnd visit)
    rw [tile_point day.1 small]
    exact near
  · have count : Kernel.seen alternate true 5 = 2 := by decide
    obtain ⟨small, -, -, visit, within, near⟩ := duskTiles_spec dusk.1 dusk.2
    rw [count]
    refine Kernel.replay_solves_explored ((rungForks mode).side true) (rungForkGoals mode) 7
      achievedSignal duskExplore _ (achieved_decodes witnessConfig mode 7) visit 2
      (by omega) ⟨7, by omega, Nat.le_refl 7,
        find_near_met mode duskLive 7 (duskExplore visit) 7 (duskEnd visit)
          (dusk_grid_walk visit within) _ ?_⟩
    change tile (pointPosition dusk.1) ∈ box 3 (duskEnd visit)
    rw [tile_point dusk.1 small]
    exact near

end AcornVerif.CurrentForkedTargetRungBoth
