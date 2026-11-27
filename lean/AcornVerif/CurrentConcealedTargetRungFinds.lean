import AcornVerif.CurrentConcealedTargetRung

namespace AcornVerif.CurrentConcealedTargetRungFinds
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentConcealedTargetFinding
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentExplorer

def rungRows : List (List ℕ) := [
  [6, 1, 2, 8, 5, 8, 8, 8], [5, 6, 6, 8, 6, 2, 7, 2], [8, 1, 6, 5, 4, 5, 5, 3],
  [2, 5, 4, 7, 5, 7, 7, 1], [6, 7, 1, 4, 2, 1, 0, 7], [8, 1, 3, 2, 3, 3, 1, 2],
  [3, 8, 5, 0, 3, 6, 0, 6], [6, 2, 8, 3, 7, 8, 7, 8], [0, 7, 3, 8, 0, 3, 8, 2],
  [6, 4, 3, 6, 0, 1, 3, 7], [5, 6, 5, 2, 8, 2, 8, 6], [2, 0, 0, 3, 4, 7, 2, 2],
  [0, 2, 8, 0, 1, 5, 5, 0], [8, 1, 3, 5, 2, 6, 1, 7], [4, 0, 2, 4, 6, 1, 7, 5],
  [6, 1, 2, 5, 3, 0, 3, 3], [3, 4, 5, 4, 5, 6, 4, 4], [2, 3, 6, 2, 6, 6, 3, 5],
  [8, 6, 4, 3, 5, 6, 4, 6], [7, 0, 6, 2, 0, 1, 4, 1], [1, 0, 7, 1, 4, 6, 6, 7],
  [4, 0, 0, 1, 1, 1, 2, 1], [1, 4, 0, 4, 0, 7, 3, 1], [0, 6, 0, 6, 2, 5, 2, 5],
  [7, 1, 8, 0, 7, 4, 3, 0], [8, 8, 4, 4, 3, 5, 7, 0], [4, 7, 1, 8, 3, 5, 4, 6],
  [0, 3, 3, 1, 2, 4, 6, 7], [7, 5, 6, 0, 4, 0, 5, 4], [3, 5, 5, 2, 5, 2, 4, 1],
  [3, 3, 6, 2, 2, 0, 6, 4], [4, 6, 0, 2, 6, 7, 1, 4], [7, 3, 0, 1, 6, 4, 7, 0],
  [3, 5, 5, 2, 0, 5, 5, 7], [8, 5, 3, 1, 3, 0, 7, 4], [2, 6, 5, 6, 7, 7, 6, 2],
  [7, 6, 6, 4, 6, 2, 6, 0], [7, 0, 2, 7, 6, 0, 5, 6], [8, 1, 0, 8, 5, 2, 5, 3],
  [6, 3, 1, 2, 2, 6, 0, 5], [4, 4, 1, 2, 3, 6, 6, 1], [5, 5, 3, 8, 1, 3, 7, 4],
  [0, 3, 5, 7, 5, 0, 1, 6], [4, 3, 8, 2, 6, 6, 1, 3], [6, 2, 3, 0, 2, 5, 8, 6],
  [3, 1, 1, 1, 4, 5, 1, 6], [8, 5, 1, 7, 2, 1, 0, 2], [1, 7, 2, 2, 6, 0, 2, 4],
  [0, 3, 3, 7, 8, 2, 0, 7], [6, 7, 0, 5, 7, 6, 3, 3], [5, 6, 4, 0, 7, 5, 5, 8],
  [3, 8, 8, 2, 0, 6, 3, 4], [4, 4, 4, 2, 3, 6, 1, 0], [7, 0, 0, 8, 0, 7, 4, 6],
  [2, 8, 0, 8, 6, 4, 7, 7], [5, 2, 3, 2, 7, 4, 3, 4], [7, 1, 6, 2, 3, 5, 2, 5],
  [6, 2, 2, 0, 8, 6, 3, 6], [8, 2, 2, 0, 8, 7, 7, 7], [5, 5, 2, 8, 5, 6, 2, 6],
  [7, 3, 8, 0, 0, 2, 7, 0], [6, 3, 0, 1, 4, 0, 5, 1], [0, 6, 6, 6, 6, 1, 6, 2],
  [4, 5, 7, 3, 4, 0, 7, 1], [2, 3, 4, 8, 4, 2, 2, 4], [4, 4, 0, 1, 6, 3, 8, 8],
  [6, 4, 5, 1, 8, 8, 2, 3], [5, 4, 0, 8, 7, 0, 0, 5], [3, 1, 4, 4, 1, 4, 5, 2],
  [1, 4, 5, 4, 1, 5, 8, 5], [1, 8, 4, 3, 2, 8, 2, 6], [0, 4, 3, 3, 3, 3, 8, 6]]

theorem rung_actions :
    (rungExplorer.actions 576).map (fun action => action.val) = rungRows.flatten := by
  decide +kernel

theorem rung_action (time : ℕ) (within : time < 576) :
    (rungExplorer.actionAt time).val = rungRows.flatten.getD time 0 := by
  have listed := congrArg (fun actions : List ℕ => actions[time]?) rung_actions
  simp only [List.getElem?_map, rungExplorer.actions_get 576 time within, Option.map_some]
    at listed
  rw [List.getD_eq_getElem?_getD, ← listed]
  rfl

structure Walk where
  visit : ℕ
  actions : List Host.Action
  tiles : List (ℤ × ℤ)

def rungWalks : List Walk := [
  ⟨45, [.west, .south, .south, .south, .wait, .harvest, .south],
    [(31, 32), (31, 33), (31, 34), (31, 35), (31, 35), (31, 35), (31, 36)]⟩,
  ⟨47, [.south, .craftBoat, .east, .east, .craftAxe, .north, .east],
    [(32, 33), (32, 33), (33, 33), (34, 33), (34, 33), (34, 32), (35, 32)]⟩,
  ⟨53, [.craftBoat, .north, .north, .eat, .north, .craftBoat, .wait],
    [(32, 32), (32, 31), (32, 30), (32, 30), (32, 29), (32, 29), (32, 29)]⟩,
  ⟨71, [.north, .wait, .west, .west, .west, .west, .eat],
    [(32, 31), (32, 31), (31, 31), (30, 31), (29, 31), (28, 31), (28, 31)]⟩]

theorem walks_listed : ∀ walk ∈ rungWalks,
    walk.visit < 72 ∧ walk.actions.length = 7 ∧ walk.tiles.length = 7 ∧
      ∀ index, index < 7 →
        rungRows.flatten.getD (walk.visit * 8 + index) 0 =
          (walk.actions.getD index .wait).index.val := by
  decide +kernel

private def witnessWalkTiles (point : ℤ × ℤ) : List Host.Action → List (ℤ × ℤ)
  | [] => []
  | action :: rest =>
    let next := match action.direction with
      | some dir => (point.1 + dir.delta.1, point.2 + dir.delta.2)
      | none => point
    next :: witnessWalkTiles next rest

private theorem witness_tileTrace_fast (world : Host.World witnessConfig)
    (actions : List Host.Action) (energyOk : 4 * actions.length ≤ world.body.energy.val)
    (inWin : 25 ≤ (tile world.body.position.position).1 ∧
      (tile world.body.position.position).1 ≤ 39 ∧
      25 ≤ (tile world.body.position.position).2 ∧
      (tile world.body.position.position).2 ≤ 39)
    (ok : witnessWalkFast (tile world.body.position.position) actions = true) :
    tileTrace (some world) actions =
      (witnessWalkTiles (tile world.body.position.position) actions).map some := by
  induction actions generalizing world with
  | nil => rfl
  | cons action rest ih =>
    simp only [List.length_cons] at energyOk
    simp only [witnessWalkFast] at ok
    cases hdir : action.direction with
    | none =>
      simp only [hdir] at ok
      obtain ⟨next, hnext, hpos, hene⟩ := witness_physicalStep_fast world action (by omega) inWin
        (by simp [hdir])
      have hpos' : tile next.body.position.position = tile world.body.position.position := by
        simpa [hdir] using hpos
      rw [tileTrace_cons]
      change (physicalStep world (code action)).map
          (fun w => tile w.body.position.position) ::
        tileTrace (physicalStep world (code action)) rest = _
      rw [hnext, Option.map_some, ih next (by omega)
        ⟨by rw [hpos']; exact inWin.1, by rw [hpos']; exact inWin.2.1,
         by rw [hpos']; exact inWin.2.2.1, by rw [hpos']; exact inWin.2.2.2⟩
        (by rw [hpos']; exact ok)]
      simp only [witnessWalkTiles, hdir, hpos', List.map_cons]
    | some dir =>
      simp only [hdir] at ok
      split at ok
      · rename_i hx
        split at ok
        · rename_i hy
          simp only [Bool.and_eq_true] at ok
          obtain ⟨next, hnext, hpos, hene⟩ := witness_physicalStep_fast world action (by omega)
            inWin (by simp only [hdir]; exact ⟨hx, hy, ok.1⟩)
          have hpos' : tile next.body.position.position =
              ((tile world.body.position.position).1 + dir.delta.1,
               (tile world.body.position.position).2 + dir.delta.2) := by
            simpa [hdir] using hpos
          rw [tileTrace_cons]
          change (physicalStep world (code action)).map
              (fun w => tile w.body.position.position) ::
            tileTrace (physicalStep world (code action)) rest = _
          rw [hnext, Option.map_some, ih next (by omega)
            ⟨by rw [hpos']; exact hx.1, by rw [hpos']; exact hx.2,
             by rw [hpos']; exact hy.1, by rw [hpos']; exact hy.2⟩
            (by rw [hpos']; exact ok.2)]
          simp only [witnessWalkTiles, hdir, hpos', List.map_cons]
        · cases ok
      · cases ok

private theorem walks_fast : ∀ walk ∈ rungWalks,
    witnessWalkFast (32, 32) walk.actions = true ∧
      witnessWalkTiles (32, 32) walk.actions = walk.tiles := by
  decide +kernel

theorem walks_traced : ∀ walk ∈ rungWalks,
    tileTrace (some (physical witnessLive.world)) walk.actions = walk.tiles.map some := by
  intro walk hwalk
  have hstart : tile (physical witnessLive.world).body.position.position = (32, 32) := witness_start
  have hlen : walk.actions.length = 7 := (walks_listed walk hwalk).2.1
  have hen : 4 * walk.actions.length ≤ (physical witnessLive.world).body.energy.val := by
    rw [hlen]; decide
  have hwin : 25 ≤ (tile (physical witnessLive.world).body.position.position).1 ∧
      (tile (physical witnessLive.world).body.position.position).1 ≤ 39 ∧
      25 ≤ (tile (physical witnessLive.world).body.position.position).2 ∧
      (tile (physical witnessLive.world).body.position.position).2 ≤ 39 := by
    rw [hstart]; omega
  obtain ⟨hfast, htiles⟩ := walks_fast walk hwalk
  rw [witness_tileTrace_fast (physical witnessLive.world) walk.actions hen hwin (hstart ▸ hfast),
    hstart, htiles]

theorem rung_walk (walk : Walk) (listed : walk ∈ rungWalks) (step : ℕ) (within : step < 7) :
    (physicalPath (physical witnessLive.world)
        (fun index => rungExplorer.actionAt (walk.visit * 8 + index)) (step + 1)).map
      (fun world => tile world.body.position.position) =
        some (walk.tiles.getD step (0, 0)) := by
  obtain ⟨early, seven, tiled, coded⟩ := walks_listed walk listed
  have taken : ∀ index, index < walk.actions.length →
      rungExplorer.actionAt (walk.visit * 8 + (0 + index)) =
        code (walk.actions.getD index .wait) := by
    intro index inside
    rw [seven] at inside
    rw [Nat.zero_add]
    apply Fin.ext
    rw [rung_action _ (by omega), coded index inside]
    rfl
  have traced := tileTrace_path (physical witnessLive.world)
    (fun index => rungExplorer.actionAt (walk.visit * 8 + index)) walk.actions 0 taken step
    (by rw [seven]; exact within)
  have start : physicalPath (physical witnessLive.world)
      (fun index => rungExplorer.actionAt (walk.visit * 8 + index)) 0 =
        some (physical witnessLive.world) := rfl
  rw [start, walks_traced walk listed, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [tiled]; exact within), Option.map_some, Nat.zero_add]
    at traced
  rw [← Option.some.inj traced, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [tiled]; exact within)]
  rfl

def rungFound : List (ℤ × ℤ) := [
  (29, 26), (30, 26), (31, 26), (32, 26), (33, 26), (34, 26), (35, 26), (29, 27), (30, 27),
  (31, 27), (32, 27), (33, 27), (34, 27), (35, 27), (25, 28), (26, 28), (27, 28), (28, 28),
  (29, 28), (30, 28), (31, 28), (32, 28), (33, 28), (34, 28), (35, 28), (25, 29), (26, 29),
  (27, 29), (28, 29), (36, 29), (37, 29), (38, 29), (25, 30), (26, 30), (27, 30), (28, 30),
  (36, 30), (37, 30), (38, 30), (25, 31), (26, 31), (27, 31), (28, 31), (36, 31), (37, 31),
  (38, 31), (25, 32), (26, 32), (27, 32), (28, 32), (36, 32), (37, 32), (38, 32), (25, 33),
  (26, 33), (27, 33), (28, 33), (36, 33), (37, 33), (38, 33), (25, 34), (26, 34), (27, 34),
  (28, 34), (36, 34), (37, 34), (38, 34), (28, 35), (36, 35), (37, 35), (38, 35), (28, 36),
  (29, 36), (30, 36), (31, 36), (32, 36), (33, 36), (34, 36), (35, 36), (36, 36), (37, 36),
  (28, 37), (29, 37), (30, 37), (31, 37), (32, 37), (33, 37), (34, 37), (28, 38), (29, 38),
  (30, 38), (31, 38), (32, 38), (33, 38), (34, 38), (28, 39), (29, 39), (30, 39), (31, 39),
  (32, 39), (33, 39), (34, 39)]

theorem found_listed : ∀ point ∈ rungFound,
    tile (pointPosition point) = point ∧
      ¬ ((point.1 - 32).natAbs ≤ 3 ∧ (point.2 - 32).natAbs ≤ 3) ∧
      ∃ walk ∈ rungWalks, ∃ step, step < 7 ∧
        (point.1 - (walk.tiles.getD step (0, 0)).1).natAbs ≤ 3 ∧
          (point.2 - (walk.tiles.getD step (0, 0)).2).natAbs ≤ 3 := by
  decide +kernel

theorem found_distinct : rungFound.Nodup := by
  decide +kernel

theorem found_met (mode : TaskFeatureMode) (point : ℤ × ℤ) (listed : point ∈ rungFound) :
    ∃ visit, visit < 72 ∧
      (completion witnessConfig mode 7).MetBy (member witnessLive (pointPosition point))
        (fun step => rungExplorer.actionAt (visit * 8 + step)) := by
  obtain ⟨own, -, walk, walked, step, within, horizontal, vertical⟩ := found_listed point listed
  have near : tile (pointPosition point) ∈ box 3 (walk.tiles.getD step (0, 0)) := by
    rw [own]
    exact mem_box.mpr ⟨horizontal, vertical⟩
  exact ⟨walk.visit, (walks_listed walk walked).1, step + 1, by omega, by
    change step + 1 ≤ 7
    omega, find_near_met mode witnessLive 7 _ (step + 1) _ (rung_walk walk walked step within)
      (pointPosition point) near⟩

theorem rung_finds (planning : PlanningSelection) :
    ∃ counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index,
      counted.Nodup ∧ counted.length = 102 ∧
        (∀ index ∈ counted, ∃ visit, visit < 72 ∧
          Kernel.SolvesOnVisit
            (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
            (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
            (executedAgent (rungConstruction planning).initial.agent) visit index) ∧
        ExecutedFindsBy (rungConstruction planning).initial.agent witnessConfig witnessLive 7
          counted 72 3 := by
  classical
  let admit : { point // point ∈ rungFound } →
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
        7).Index :=
    fun point => ⟨⟨pointPosition point.1, by
      obtain ⟨own, far, -⟩ := found_listed point.1 point.2
      rw [member_tile, witness_start, own, mem_box]
      exact far⟩,
      (found_met (rungConstruction planning).profile.taskMode point.1 point.2).elim
        fun _ met => ⟨_, met.2⟩⟩
  have injective : Function.Injective admit := by
    intro first second same
    have tiles := congrArg (fun target :
        (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
          7).Index => tile target.1.1) same
    simp only [admit, (found_listed first.1 first.2).1, (found_listed second.1 second.2).1]
      at tiles
    exact Subtype.ext tiles
  have distinct : (rungFound.attach.map admit).Nodup :=
    (List.nodup_attach.mpr found_distinct).map injective
  have solved : ∀ index ∈ rungFound.attach.map admit, ∃ visit, visit < 72 ∧
      Kernel.SolvesOnVisit
        (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
        (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
        (executedAgent (rungConstruction planning).initial.agent) visit index := by
    intro index member
    obtain ⟨point, -, rfl⟩ := List.mem_map.mp member
    exact (cold_found_within (profile := (rungConstruction planning).profile) rfl rfl planning
      witnessLive rfl 7 72 (admit point)).mpr
        (found_met (rungConstruction planning).profile.taskMode point.1 point.2)
  exact ⟨rungFound.attach.map admit, distinct, by
    rw [List.length_map, List.length_attach]
    rfl, solved, Kernel.findsBy_of_each distinct (by
      rw [List.length_map, List.length_attach]
      decide) solved⟩

end AcornVerif.CurrentConcealedTargetRungFinds
