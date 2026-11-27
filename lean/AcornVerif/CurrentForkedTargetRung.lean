import AcornVerif.CurrentConcealedTargetRung
import AcornVerif.CurrentExplorer
import AcornVerif.CurrentForkedTarget
import AcornVerif.CurrentFrameSlots
import AcornVerif.CurrentTerrain

namespace AcornVerif.CurrentForkedTargetRung
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentForkedTarget

def duskLive : Live witnessConfig :=
  ⟨{ Host.World.empty witnessConfig with time := 1024 }, {}⟩

theorem dusk_start : tile duskLive.world.body.position.position = (32, 32) := by
  decide +kernel

theorem dawn_phase : witnessLive.world.dayPhase.val = 0 := by
  decide +kernel

theorem dusk_phase : duskLive.world.dayPhase.val = 4 := by
  decide +kernel

theorem dusk_carried : witnessLive.carried = duskLive.carried := rfl

theorem ok_of_isOk {ε α : Type} {result : Except ε α} (accepted : result.isOk = true) :
    ∃ value, result = .ok value := by
  cases result with
  | error error => exact absurd accepted (by simp [Except.isOk, Except.toBool])
  | ok value => exact ⟨value, rfl⟩

theorem ofFnM_isOk {ε α : Type} {n : Nat} (f : Fin n → Except ε α)
    (each : ∀ index, (f index).isOk = true) : (Vector.ofFnM f).isOk = true := by
  have values : f = fun index => pure (Classical.choose (ok_of_isOk (each index))) :=
    funext fun index => Classical.choose_spec (ok_of_isOk (each index))
  rw [values, Vector.ofFnM_pure]
  rfl

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

theorem window_admits : ∀ offset : Fin Host.patchSide, ∀ octave : Fin 4,
    ¬CurrentTerrain.PastLast
      ((Host.coordinateFloatWord (Int64.ofInt (27 + offset.val))).div
        (CurrentTerrain.octaveScale ⟨0x41000000⟩ octave.val)) := by
  decide +kernel

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

def dayWord (percept : Percept Grid.interface) : Option UInt64 :=
  (percept.frame.words.find? (fun word => word.channel == 0x41)).map (·.value)

def showsDusk (percept : Percept Grid.interface) : Bool :=
  dayWord percept == some 4

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

theorem dayWord_live (mode : TaskFeatureMode) (live : Live witnessConfig) :
    dayWord ((gridWorld witnessConfig mode).percept (some live)) =
      some (sensed live.world).day.toUInt64 :=
  dayWord_percept mode (sensed live.world) live.carried.reward live.carried.events.done

theorem dawn_day (target : Host.Position) :
    (sensed (witnessLive.world.setGoal (.find target))).day = 0 := by
  rcases CurrentFrameSlots.sensed_day (witnessLive.world.setGoal (.find target)) with day | day
  · have phase : (witnessLive.world.setGoal (.find target)).dayPhase =
        witnessLive.world.dayPhase := rfl
    rw [day, phase, dawn_phase]
    rfl
  · exact day

theorem dawn_shown (mode : TaskFeatureMode) (target : Host.Position) :
    showsDusk ((gridWorld witnessConfig mode).percept (member witnessLive target)) = false := by
  change (dayWord ((gridWorld witnessConfig mode).percept
    (some ⟨witnessLive.world.setGoal (.find target), witnessLive.carried⟩)) == some 4) = false
  rw [dayWord_live, dawn_day]
  rfl

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

abbrev rungForks (mode : TaskFeatureMode) : Kernel.TurnClass Grid.interface :=
  forkedFind witnessConfig mode witnessLive duskLive 7

abbrev rungForkGoals (mode : TaskFeatureMode) : (rungForks mode).Goals :=
  forkedGoals witnessConfig mode witnessLive duskLive 7

theorem dusk_walk (visit : ℕ) (within : visit ≤ 1) :
    (physicalPath (physical duskLive.world) (witnessExplore visit) 7).map
      (fun world => tile world.body.position.position) = some (witnessEnd visit) := by
  have hstart : tile (physical duskLive.world).body.position.position = (32, 32) := dusk_start
  have hen : 4 * 7 ≤ (physical duskLive.world).body.energy.val := by decide
  have hwin : 25 ≤ (tile (physical duskLive.world).body.position.position).1 ∧
      (tile (physical duskLive.world).body.position.position).1 ≤ 39 ∧
      25 ≤ (tile (physical duskLive.world).body.position.position).2 ∧
      (tile (physical duskLive.world).body.position.position).2 ≤ 39 := by
    rw [hstart]; omega
  rcases (by omega : visit = 0 ∨ visit = 1) with rfl | rfl
  · change (physicalPath (physical duskLive.world) (fun _ => code .east) 7).map
      (fun world => tile world.body.position.position) = some (39, 32)
    simpa [hstart, witnessWalkEnd, Host.Action.direction, Host.Direction.delta] using
      witness_physicalPath_const (physical duskLive.world) .east 7 hen hwin
        (hstart ▸ witness_east_walkable)
  · change (physicalPath (physical duskLive.world) (fun _ => code .west) 7).map
      (fun world => tile world.body.position.position) = some (25, 32)
    simpa [hstart, witnessWalkEnd, Host.Action.direction, Host.Direction.delta] using
      witness_physicalPath_const (physical duskLive.world) .west 7 hen hwin
        (hstart ▸ witness_west_walkable)

def partner (point : ℤ × ℤ) : ℤ × ℤ :=
  if 36 ≤ point.1 then (point.1 - 14, point.2)
  else if point.1 ≤ 28 then (point.1 + 14, point.2)
  else (78 - point.2, point.1)

theorem tile_point (point : ℤ × ℤ)
    (small : -100 ≤ point.1 ∧ point.1 ≤ 100 ∧ -100 ≤ point.2 ∧ point.2 ≤ 100) :
    tile (pointPosition point) = point := by
  refine Prod.ext ?_ ?_ <;> simp only [tile, pointPosition, clampCoordinate] <;> omega

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

theorem first_admitted (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    ¬ InGoalBox (pointPosition point) witnessLive.world.body.position.position := by
  rw [member_tile, witness_start, (witnessTiles_admitted point inside).1]
  exact (witnessTiles_admitted point inside).2

theorem first_feasible (mode : TaskFeatureMode) (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    Kernel.Feasible (completion witnessConfig mode 7)
      (member witnessLive (pointPosition point)) := by
  obtain ⟨visit, within, near⟩ := witnessTiles_near point inside
  refine ⟨witnessExplore visit, 7, by omega, Nat.le_refl 7,
    witness_meets mode 7 visit within _ ?_⟩
  rw [(witnessTiles_admitted point inside).1]
  exact near

theorem second_admitted (point : ℤ × ℤ) (inside : point ∈ witnessTiles) :
    ¬ InGoalBox (pointPosition (partner point)) duskLive.world.body.position.position := by
  rw [member_tile, dusk_start, (partner_spec point inside).1]
  exact (partner_spec point inside).2.1

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

def firstIndex (mode : TaskFeatureMode) (point : { point // point ∈ witnessTiles }) :
    (feasibleFind witnessConfig mode witnessLive 7).Index :=
  ⟨⟨pointPosition point.1, first_admitted point.1 point.2⟩, first_feasible mode point.1 point.2⟩

def secondIndex (mode : TaskFeatureMode) (point : { point // point ∈ witnessTiles }) :
    (feasibleFind witnessConfig mode duskLive 7).Index :=
  ⟨⟨pointPosition (partner point.1), second_admitted point.1 point.2⟩,
    second_feasible mode point.1 point.2⟩

def rungPair (mode : TaskFeatureMode) (point : { point // point ∈ witnessTiles }) :
    (rungForks mode).Index :=
  ⟨(firstIndex mode point, secondIndex mode point), pair_apart mode point.1 point.2⟩

theorem rungPair_key (mode : TaskFeatureMode) (one two : { point // point ∈ witnessTiles })
    (same : firstTarget mode witnessLive duskLive 7 (rungPair mode one) =
      firstTarget mode witnessLive duskLive 7 (rungPair mode two)) : one = two := by
  have tiles := congrArg
    (fun target : (feasibleFind witnessConfig mode witnessLive 7).Index => tile target.1.1) same
  change tile (pointPosition one.1) = tile (pointPosition two.1) at tiles
  rw [(witnessTiles_admitted one.1 one.2).1, (witnessTiles_admitted two.1 two.2).1] at tiles
  exact Subtype.ext tiles

theorem rungPair_injective (mode : TaskFeatureMode) : Function.Injective (rungPair mode) :=
  fun one two same => rungPair_key mode one two
    (congrArg (firstTarget mode witnessLive duskLive 7) same)

def rungPairs (mode : TaskFeatureMode) : Finset (rungForks mode).Index :=
  witnessTiles.attach.map ⟨rungPair mode, rungPair_injective mode⟩

theorem rungPairs_card (mode : TaskFeatureMode) : (rungPairs mode).card = 147 := by
  rw [rungPairs, Finset.card_map, Finset.card_attach, card_witnessTiles]

theorem rungPairs_distinct (mode : TaskFeatureMode) :
    ∀ one ∈ rungPairs mode, ∀ two ∈ rungPairs mode,
      firstTarget mode witnessLive duskLive 7 one =
        firstTarget mode witnessLive duskLive 7 two → one = two := by
  intro one inOne two inTwo same
  obtain ⟨first, -, rfl⟩ := Finset.mem_map.mp inOne
  obtain ⟨second, -, rfl⟩ := Finset.mem_map.mp inTwo
  exact congrArg (rungPair mode) (rungPair_key mode first second same)

def forkWitness : Kernel.Agent Grid.interface :=
  Kernel.switch showsDusk 7
    (fun _ => Kernel.replay Grid.interface 7 achievedSignal witnessExplore)

theorem witness_reads (mode : TaskFeatureMode) (pair : (rungForks mode).Index)
    (situation : Bool) :
    showsDusk (((rungForks mode).world pair).percept ((rungForks mode).start pair situation)) =
      situation := by
  cases situation
  · exact dawn_shown mode pair.1.1.1.1
  · exact dusk_shown mode pair.1.2.1.1

theorem witness_keeps (mode : TaskFeatureMode) (horizon : ℕ) :
    Kernel.KeepsBut (rungForks mode) (rungForkGoals mode) 7 horizon 0 forkWitness :=
  Kernel.switch_keeps (rungForks mode) (rungForkGoals mode) 7 showsDusk _ (witness_reads mode)
    (fun situation index visit later after solved =>
      Kernel.replay_solves ((rungForks mode).side situation) (rungForkGoals mode) 7
        achievedSignal witnessExplore index (achieved_decodes witnessConfig mode 7) visit later
        after solved)
    horizon

def alternate (visit : ℕ) : Bool :=
  decide (visit % 2 = 1)

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
