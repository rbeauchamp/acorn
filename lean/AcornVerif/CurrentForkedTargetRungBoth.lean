import AcornVerif.CurrentForkedTargetBoth
import AcornVerif.CurrentForkedTargetRung

namespace AcornVerif.CurrentForkedTargetRungBoth
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentForkedTarget
open AcornVerif.CurrentForkedTargetBoth AcornVerif.CurrentForkedTargetRung

def dayTiles : Finset (ℤ × ℤ) :=
  Finset.Icc 22 25 ×ˢ Finset.Icc 29 35 ∪ Finset.Icc 29 35 ×ˢ Finset.Icc 39 42

def duskTiles : Finset (ℤ × ℤ) :=
  Finset.Icc 39 42 ×ˢ Finset.Icc 29 35 ∪ Finset.Icc 29 35 ×ˢ Finset.Icc 22 25

theorem dayTiles_card : dayTiles.card = 56 := by
  decide

theorem duskTiles_card : duskTiles.card = 56 := by
  decide

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

def duskExplore (visit : ℕ) (_ : ℕ) : Kernel.Act Grid.interface :=
  code (match visit with | 0 => .east | _ => .north)

def duskEnd : ℕ → ℤ × ℤ
  | 0 => (39, 32)
  | _ => (32, 25)

private theorem dusk_north_walkable :
    witnessWalkFast (32, 32) (List.replicate 7 .north) = true := by
  decide +kernel

theorem dusk_grid_walk (visit : ℕ) (within : visit ≤ 1) :
    (physicalPath (physical duskLive.world) (duskExplore visit) 7).map
      (fun world => tile world.body.position.position) = some (duskEnd visit) := by
  rcases (by omega : visit = 0 ∨ visit = 1) with rfl | rfl
  · exact dusk_walk 0 (Nat.zero_le 1)
  · have hstart : tile (physical duskLive.world).body.position.position = (32, 32) := dusk_start
    have hen : 4 * 7 ≤ (physical duskLive.world).body.energy.val := by decide
    have hwin : 25 ≤ (tile (physical duskLive.world).body.position.position).1 ∧
        (tile (physical duskLive.world).body.position.position).1 ≤ 39 ∧
        25 ≤ (tile (physical duskLive.world).body.position.position).2 ∧
        (tile (physical duskLive.world).body.position.position).2 ≤ 39 := by
      rw [hstart]; omega
    change (physicalPath (physical duskLive.world) (fun _ => code .north) 7).map
      (fun world => tile world.body.position.position) = some (32, 25)
    simpa [hstart, witnessWalkEnd, Host.Action.direction, Host.Direction.delta] using
      witness_physicalPath_const (physical duskLive.world) .north 7 hen hwin
        (hstart ▸ dusk_north_walkable)

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

def gridPair (mode : TaskFeatureMode) (one : { point // point ∈ dayTiles })
    (two : { point // point ∈ duskTiles }) : (rungForks mode).Index :=
  ⟨(dayIndex mode one, duskIndex mode two), grid_apart mode one two⟩

theorem dayIndex_injective (mode : TaskFeatureMode) : Function.Injective (dayIndex mode) := by
  intro one two same
  have tiles := congrArg
    (fun target : (feasibleFind witnessConfig mode witnessLive 7).Index => tile target.1.1) same
  change tile (pointPosition one.1) = tile (pointPosition two.1) at tiles
  rw [tile_point one.1 (dayTiles_spec one.1 one.2).1,
    tile_point two.1 (dayTiles_spec two.1 two.2).1] at tiles
  exact Subtype.ext tiles

theorem duskIndex_injective (mode : TaskFeatureMode) : Function.Injective (duskIndex mode) := by
  intro one two same
  have tiles := congrArg
    (fun target : (feasibleFind witnessConfig mode duskLive 7).Index => tile target.1.1) same
  change tile (pointPosition one.1) = tile (pointPosition two.1) at tiles
  rw [tile_point one.1 (duskTiles_spec one.1 one.2).1,
    tile_point two.1 (duskTiles_spec two.1 two.2).1] at tiles
  exact Subtype.ext tiles

def gridFirsts (mode : TaskFeatureMode) :
    Finset (feasibleFind witnessConfig mode witnessLive 7).Index :=
  dayTiles.attach.map ⟨dayIndex mode, dayIndex_injective mode⟩

def gridSeconds (mode : TaskFeatureMode) :
    Finset (feasibleFind witnessConfig mode duskLive 7).Index :=
  duskTiles.attach.map ⟨duskIndex mode, duskIndex_injective mode⟩

def gridAgents : Bool → Kernel.Agent Grid.interface
  | false => Kernel.replay Grid.interface 7 achievedSignal witnessExplore
  | true => Kernel.replay Grid.interface 7 achievedSignal duskExplore

def gridWitness : Kernel.Agent Grid.interface :=
  Kernel.switch showsDusk 7 gridAgents

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

theorem alternate_later (horizon returns : ℕ) (room : 2 * returns + 6 ≤ horizon)
    (situation : Bool) :
    ∃ later : Finset ℕ, returns ≤ later.card ∧
      ∀ other ∈ later, 5 < other ∧ other < horizon ∧
        Function.update alternate 5 situation other = situation := by
  refine ⟨(Finset.range returns).image fun turn => 2 * turn + 6 + (if situation then 1 else 0),
    ?_, fun other member => ?_⟩
  · rw [Finset.card_image_of_injective _ (fun left right same => by
      have equal : 2 * left + 6 + (if situation then 1 else 0) =
          2 * right + 6 + (if situation then 1 else 0) := same
      omega), Finset.card_range]
  · obtain ⟨turn, within, rfl⟩ := Finset.mem_image.mp member
    rw [Finset.mem_range] at within
    cases situation
    · refine ⟨by simp only [Bool.false_eq_true, ite_false]; omega,
        by simp only [Bool.false_eq_true, ite_false]; omega, ?_⟩
      rw [Function.update_of_ne (by simp only [Bool.false_eq_true, ite_false]; omega)]
      simp only [alternate, Bool.false_eq_true, ite_false, decide_eq_false_iff_not]
      omega
    · refine ⟨by simp only [ite_true]; omega, by simp only [ite_true]; omega, ?_⟩
      rw [Function.update_of_ne (by simp only [ite_true]; omega)]
      simp only [alternate, ite_true, decide_eq_true_eq]
      omega

theorem grid_witness_masters (mode : TaskFeatureMode) (horizon returns : ℕ)
    (room : 2 * returns + 6 ≤ horizon) :
    Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 49
      (firstTarget mode witnessLive duskLive 7) (secondTarget mode witnessLive duskLive 7)
      6 horizon returns (fun _ _ _ => True) gridWitness := by
  refine ⟨alternate, 5, gridFirsts mode, gridSeconds mode, by decide, ?_, ?_,
    fun one inFirsts two inSeconds => ?_⟩
  · rw [gridFirsts, Finset.card_map, Finset.card_attach, dayTiles_card]
    decide
  · rw [gridSeconds, Finset.card_map, Finset.card_attach, duskTiles_card]
    decide
  obtain ⟨day, -, rfl⟩ := Finset.mem_map.mp inFirsts
  obtain ⟨dusk, -, rfl⟩ := Finset.mem_map.mp inSeconds
  choose comeBack enough back using fun situation => alternate_later horizon returns room situation
  refine ⟨gridPair mode day dusk, rfl, rfl, fun situation =>
    ⟨?_, trivial, comeBack situation, enough situation, fun other member =>
      ⟨(back situation other member).1, (back situation other member).2.1,
        (back situation other member).2.2, trivial⟩⟩⟩
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
