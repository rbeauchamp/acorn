/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.WorldObservation
import AcornVerif.CurrentTerrain
import AcornVerif.CurrentActions
import AcornVerif.CurrentSpawn
import AcornVerif.CurrentStep
import AcornVerif.FloatLibBridge
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Executed current-world storage and work bounds

These theorems concern the world used by `WorldDriver`, `Attempt` and `Runner`.
Legal state is carried by receiving types, including at arbitrary public writes;
no separate historical world model or bounded initial configuration is assumed.
The finite-container and compiler/runtime implementations remain trusted.
-/
namespace AcornVerif.CurrentWorld
open Acorn Acorn.Host

/-- Sparse harvesting has at most one timestamp for each site in the extended box. -/
theorem harvest_storage_bound {config : WorldConfig} (world : World config) :
    world.harvested.size ≤ (config.side + 2) * (config.side + 2) := by
  rw [← Std.TreeMap.length_keys]
  have h := List.Nodup.length_le_card world.harvested.nodup_keys
  simpa [HarvestKey] using h

/-- Every constructible state obeys the receiving population and body bounds. -/
theorem state_bounds {config : WorldConfig} (world : World config) :
    world.body.position.x.val < config.side ∧ world.body.position.y.val < config.side ∧
    world.body.energy.val ≤ FeatureConstants.energyMax ∧
    world.deer.entries.size ≤ config.raw.deerCap.toNat ∧
    world.food.entries.size ≤ config.raw.foodCap.toNat ∧
    world.harvested.size ≤ (config.side + 2) * (config.side + 2) :=
  ⟨world.body.position.x.isLt, world.body.position.y.isLt, by have := world.body.energy.isLt; omega,
    world.deer.bounded, world.food.bounded, harvest_storage_bound world⟩

/-- Logical variable-size records are bounded for the full raw admitted configuration.
This does not promise allocation success or bound allocator/node byte overhead. -/
theorem retained_records_bound {config : WorldConfig} (world : World config) :
    world.harvested.size + world.deer.entries.size + world.food.entries.size ≤
      (config.side + 2) * (config.side + 2) +
        config.raw.deerCap.toNat + config.raw.foodCap.toNat := by
  have := state_bounds world
  omega

/-- Every radius contributes four directed edges, each with 2r+1 visits. -/
theorem spiral_work (side : Nat) :
    (∑ radius ∈ Finset.range side, 4 * (2 * radius + 1)) = 4 * side * side := by
  induction side with
  | zero => simp
  | succ side ih => rw [Finset.sum_range_succ, ih]; ring

/-- Body-to-facing harvest admission is universal over the actual closed direction domain. -/
theorem facing_harvest_admission {config : WorldConfig} (world : World config) :
    ∃ key, harvestKey config (world.body.position.facingPosition world.body.facing) = some key :=
  world.body.position.facingKey_exists world.body.facing

theorem isPastLast_iff_pastLast (q : Binary32) :
    isPastLast q = true ↔ CurrentTerrain.PastLast q := by
  rw [FloatLibBridge.isPastLast_iff_units]
  unfold CurrentTerrain.PastLast
  rfl

theorem octaveScale_eq (scale : Binary32) (octave : Nat) :
    octaveScale scale octave = CurrentTerrain.octaveScale scale octave := by
  induction octave generalizing scale with
  | zero => rfl
  | succ k ih =>
    simp only [octaveScale, CurrentTerrain.octaveScale]
    exact ih _

private theorem admitBounds_nonempty (raw : RawWorldConfig) (hpos : 0 < raw.side.val)
    (hmax : raw.side.val ≤ RawWorldConfig.maxSide) :
    raw.admitLo.val < 0 ∧ 0 < raw.admitHi.val := by
  rw [raw.admitLo_val, raw.admitHi_val hpos hmax]
  by_cases hd : raw.deerCap = 0
  · rw [ite_eq_left hd, ite_eq_left hd]
    omega
  · rw [ite_eq_right hd, ite_eq_right hd]
    decide

theorem admissible_latticeAdmits {config : WorldConfig} (hadm : config.raw.admissible = true)
    (tile : Position)
    (hx : config.raw.admitLo.val ≤ tile.x.val ∧ tile.x.val ≤ config.raw.admitHi.val)
    (hy : config.raw.admitLo.val ≤ tile.y.val ∧ tile.y.val ≤ config.raw.admitHi.val) :
    CurrentTerrain.LatticeAdmits tile config.raw.baseScale := by
  obtain ⟨hpos, hmax, _, hrange⟩ := (RawWorldConfig.admissible_iff config.raw).mp hadm
  have hbounds := admitBounds_nonempty config.raw hpos hmax
  have hoct := (scaleAdmitsRange_iff config.raw.admitLo config.raw.admitHi
    config.raw.baseScale).mp hrange
  intro octave below
  obtain ⟨hlo_f, hhi_f⟩ := hoct octave below
  have hnot_past : ∀ c : Coordinate,
      config.raw.admitLo.val ≤ c.val → c.val ≤ config.raw.admitHi.val →
        ¬ CurrentTerrain.PastLast
          ((coordinateFloat c).div (CurrentTerrain.octaveScale config.raw.baseScale octave)) := by
    intro c hc_lo hc_hi hpl
    rw [← octaveScale_eq, ← isPastLast_iff_pastLast] at hpl
    have hfalse := FloatLibBridge.coordinateFloat_div_pastLast_interval
      config.raw.admitLo c config.raw.admitHi hbounds.1 hbounds.2 hc_lo hc_hi
      (octaveScale config.raw.baseScale octave) hlo_f hhi_f
    rw [hpl] at hfalse
    cases hfalse
  exact ⟨hnot_past tile.x hx.1 hx.2, hnot_past tile.y hy.1 hy.2⟩

theorem admissible_tileKind_isOk {config : WorldConfig} (hadm : config.raw.admissible = true)
    (world : World config) (tile : Position)
    (hx : config.raw.admitLo.val ≤ tile.x.val ∧ tile.x.val ≤ config.raw.admitHi.val)
    (hy : config.raw.admitLo.val ≤ tile.y.val ∧ tile.y.val ≤ config.raw.admitHi.val) :
    (world.tileKind tile).isOk = true :=
  (CurrentTerrain.tileKind_isOk world tile).mpr (admissible_latticeAdmits hadm tile hx hy)

theorem admissible_inBoxMargin {config : WorldConfig} (hadm : config.raw.admissible = true)
    (c : Coordinate) (hlo : -5 ≤ c.val) (hhi : c.val ≤ config.raw.side.val + 4) :
    config.raw.admitLo.val ≤ c.val ∧ c.val ≤ config.raw.admitHi.val := by
  obtain ⟨hpos, hmax, _, _⟩ := (RawWorldConfig.admissible_iff config.raw).mp hadm
  rw [config.raw.admitLo_val, config.raw.admitHi_val hpos hmax]
  by_cases hd : config.raw.deerCap = 0
  · rw [ite_eq_left hd, ite_eq_left hd]
    exact ⟨hlo, hhi⟩
  · rw [ite_eq_right hd, ite_eq_right hd]
    have hcb := c.property
    exact ⟨by omega, by omega⟩

theorem admissible_box_tileKind_isOk {config : WorldConfig} (hadm : config.raw.admissible = true)
    (world : World config) (tile : Position)
    (hx : -5 ≤ tile.x.val ∧ tile.x.val ≤ config.raw.side.val + 4)
    (hy : -5 ≤ tile.y.val ∧ tile.y.val ≤ config.raw.side.val + 4) :
    (world.tileKind tile).isOk = true :=
  admissible_tileKind_isOk hadm world tile
    (admissible_inBoxMargin hadm tile.x hx.1 hx.2)
    (admissible_inBoxMargin hadm tile.y hy.1 hy.2)

theorem admissible_translate_isSome {config : WorldConfig} (hadm : config.raw.admissible = true)
    (pos : BoxPosition config) (dx dy : Int)
    (hdx : -5 ≤ dx ∧ dx ≤ 5) (hdy : -5 ≤ dy ∧ dy ≤ 5) :
    ∃ tile, pos.position.translate dx dy = some tile ∧
      -5 ≤ tile.x.val ∧ tile.x.val ≤ config.raw.side.val + 4 ∧
      -5 ≤ tile.y.val ∧ tile.y.val ≤ config.raw.side.val + 4 := by
  obtain ⟨_, hmax, _, _⟩ := (RawWorldConfig.admissible_iff config.raw).mp hadm
  have hx_lo : 0 ≤ (pos.x.val : Int) := Int.natCast_nonneg pos.x.val
  have hy_lo : 0 ≤ (pos.y.val : Int) := Int.natCast_nonneg pos.y.val
  have hx_hi : (pos.x.val : Int) < config.raw.side.val := by
    have := pos.x.isLt
    change pos.x.val < config.raw.side.val.toNat at this
    have := config.positiveSide
    omega
  have hy_hi : (pos.y.val : Int) < config.raw.side.val := by
    have := pos.y.isLt
    change pos.y.val < config.raw.side.val.toNat at this
    have := config.positiveSide
    omega
  have hlim : RawWorldConfig.maxSide = 2 ^ 63 - 5 := rfl
  have hcx : Coordinate.checked (pos.x.val + dx) ≠ none := by
    intro hnone
    have hbad : pos.x.val + dx < -(2 ^ 63) ∨ 2 ^ 63 - 1 < pos.x.val + dx := by
      unfold Coordinate.checked at hnone
      split at hnone
      · cases hnone
      · omega
    omega
  have hcy : Coordinate.checked (pos.y.val + dy) ≠ none := by
    intro hnone
    have hbad : pos.y.val + dy < -(2 ^ 63) ∨ 2 ^ 63 - 1 < pos.y.val + dy := by
      unfold Coordinate.checked at hnone
      split at hnone
      · cases hnone
      · omega
    omega
  cases htx : Coordinate.checked (pos.x.val + dx) with
  | none => exact absurd htx hcx
  | some tx =>
    cases hty : Coordinate.checked (pos.y.val + dy) with
    | none => exact absurd hty hcy
    | some ty =>
      refine ⟨⟨tx, ty⟩, ?_, ?_⟩
      · unfold Position.translate
        have hpx : (pos.x.val : Int) = pos.position.x.val := rfl
        have hpy : (pos.y.val : Int) = pos.position.y.val := rfl
        rw [← hpx, ← hpy, htx, hty]
        rfl
      · have htx_v := Coordinate.checked_exact _ _ htx
        have hty_v := Coordinate.checked_exact _ _ hty
        change -5 ≤ tx.val ∧ tx.val ≤ config.raw.side.val + 4 ∧
          -5 ≤ ty.val ∧ ty.val ≤ config.raw.side.val + 4
        omega

theorem standard_admits (seed : UInt64) (side : Coordinate) (config : WorldConfig)
    (h : WorldConfig.standard seed side = .ok config) :
    config.raw.admissible = true ∧ WorldConfig.admit config.raw = .ok config := by
  have hsb := WorldConfig.standard_bounds seed side config h
  have hraw : config.raw = {
      seed := seed
      side := side
      dayLength := FeatureConstants.worldDayLength.toUInt64
      regrow := FeatureConstants.worldRegrow.toUInt64
      foodInterval := FeatureConstants.worldFoodInterval.toUInt64
      foodCap := FeatureConstants.worldFoodCap.toUInt32
      deerCap := (side.val.toNat * side.val.toNat / FeatureConstants.worldDeerArea).toUInt32
      baseScale := Binary32.ofUInt64 (max FeatureConstants.worldMinScale
        (side.val.toNat / FeatureConstants.worldScaleDivisor)).toUInt64 } := by
    unfold WorldConfig.standard at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases Except.ok.inj h
        rfl
  set sNat := max FeatureConstants.worldMinScale
    (side.val.toNat / FeatureConstants.worldScaleDivisor)
  have hs_lo : 8 ≤ sNat := by
    dsimp [sNat]
    change 8 ≤ max 8 _
    omega
  have hs_hi : sNat ≤ 2 ^ 28 := by
    dsimp [sNat]
    have hmax : side.val ≤ 3000000000 := hsb.2.2
    change max 8 (side.val.toNat / 16) ≤ 2 ^ 28
    omega
  have hbase_eq : config.raw.baseScale = Binary32.ofUInt64 sNat.toUInt64 := by
    rw [hraw]
  have hrange :
      scaleAdmitsRange config.raw.admitLo config.raw.admitHi config.raw.baseScale = true :=
    (scaleAdmitsRange_iff _ _ _).mpr fun octave below => by
      rw [hbase_eq]
      exact ⟨FloatLibBridge.octaveScale_ofNat_not_pastLast sNat hs_lo hs_hi
          config.raw.admitLo octave below,
        FloatLibBridge.octaveScale_ofNat_not_pastLast sNat hs_lo hs_hi
          config.raw.admitHi octave below⟩
  have hadm : config.raw.admissible = true := by
    rw [RawWorldConfig.admissible_iff]
    refine ⟨config.positiveSide, ?_, config.positiveDay, hrange⟩
    have hmax : side.val ≤ 3000000000 := hsb.2.2
    rw [hsb.1]
    change side.val ≤ 2 ^ 63 - 5
    omega
  refine ⟨hadm, ?_⟩
  unfold WorldConfig.admit
  have hbits := (RawWorldConfig.admissible_iff config.raw).mp hadm
  simp only [hbits.1, hbits.2.1, hbits.2.2.1, hbits.2.2.2]
  rfl

theorem admissible_boxPosition_tileKind_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) (pos : BoxPosition config) :
    (world.tileKind pos.position).isOk = true := by
  have hxs : pos.x.val < config.raw.side.val.toNat := pos.x.isLt
  have hys : pos.y.val < config.raw.side.val.toNat := pos.y.isLt
  have hpos := config.positiveSide
  apply admissible_box_tileKind_isOk hadm world pos.position
  · change -5 ≤ (pos.x.val : Int) ∧ (pos.x.val : Int) ≤ config.raw.side.val + 4
    omega
  · change -5 ≤ (pos.y.val : Int) ∧ (pos.y.val : Int) ≤ config.raw.side.val + 4
    omega

private theorem isOk_of_exists {ε α : Type} (e : Except ε α) (h : ∃ v, e = .ok v) :
    e.isOk = true := by
  obtain ⟨v, hv⟩ := h
  rw [hv]
  rfl

private theorem vector_ofFnM_isOk_iff {ε α : Type} :
    ∀ (n : Nat) (f : Fin n → Except ε α),
      (Vector.ofFnM f).isOk = true ↔ ∀ i, (f i).isOk = true
  | 0, f => by
    rw [Vector.ofFnM_zero]
    simp [pure, Except.pure, Except.isOk, Except.toBool]
  | n + 1, f => by
    rw [Vector.ofFnM_succ]
    have ih := vector_ofFnM_isOk_iff n (fun i => f i.castSucc)
    cases hpre : Vector.ofFnM (fun i : Fin n => f i.castSucc) with
    | error e =>
      constructor
      · intro hbad
        simp [bind, Except.bind, Except.isOk, Except.toBool] at hbad
      · intro hall
        have hok : (Vector.ofFnM fun i : Fin n => f i.castSucc).isOk = true :=
          ih.mpr fun i => hall i.castSucc
        rw [hpre] at hok
        cases hok
    | ok vec =>
      have hcast : ∀ i : Fin n, (f i.castSucc).isOk = true :=
        ih.mp (by rw [hpre]; rfl)
      cases hlast : f (Fin.last n) with
      | error e =>
        constructor
        · intro hbad
          simp [bind, Except.bind, Except.isOk, Except.toBool] at hbad
        · intro hall
          have hl := hall (Fin.last n)
          rw [hlast] at hl
          cases hl
      | ok a =>
        constructor
        · intro _ i
          by_cases hlt : i.val < n
          · have heq : i = Fin.castSucc ⟨i.val, hlt⟩ := Fin.ext rfl
            rw [heq]
            exact hcast ⟨i.val, hlt⟩
          · have hlt' := i.isLt
            have heq : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [heq, hlast]
            rfl
        · intro _
          simp [bind, Except.bind, pure, Except.pure, Except.isOk, Except.toBool]

private theorem forIn_range'_ok {ε σ : Type} (count : Nat)
    (body : Nat → σ → Except ε (ForInStep σ))
    (step : ∀ index state, index < count → ∃ next, body index state = .ok next) :
    ∀ remaining start init, start + remaining = count →
      ∃ result, forIn (List.range' start remaining 1) init body = .ok result
  | 0, start, init, _ => by
    refine ⟨init, ?_⟩
    simp [pure, Except.pure]
  | remaining + 1, start, init, total => by
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨next, hnext⟩ := step start init (by omega)
    rw [hnext]
    cases next with
    | done after =>
      refine ⟨after, ?_⟩
      simp [bind, Except.bind, pure, Except.pure]
    | yield after =>
      exact forIn_range'_ok count body step remaining (start + 1) after (by omega)

private theorem forIn_range_ok {ε σ : Type} (count : Nat)
    (body : Nat → σ → Except ε (ForInStep σ))
    (step : ∀ index state, index < count → ∃ next, body index state = .ok next) (init : σ) :
    ∃ result, forIn [:count] init body = .ok result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact forIn_range'_ok count body step count 0 init (Nat.zero_add count)

private theorem forIn_range_bind_ok {ε σ α : Type} (count : Nat) (init : σ)
    (body : Nat → σ → Except ε (ForInStep σ)) (cont : σ → Except ε α)
    (step : ∀ index state, index < count → ∃ next, body index state = .ok next)
    (hcont : ∀ res, ∃ val, cont res = .ok val) :
    ∃ val, (forIn [:count] init body >>= cont) = .ok val := by
  obtain ⟨res, hres⟩ := forIn_range_ok count body step init
  obtain ⟨val, hval⟩ := hcont res
  exact ⟨val, by simp [hres, hval, bind, Except.bind]⟩

private theorem mapM_list_stateT_ok {ε S α β : Type} (f : α → StateT S (Except ε) β) :
    ∀ (xs : List α) (s : S),
      (∀ x ∈ xs, ∀ s', ∃ res, f x s' = .ok res) →
        ∃ res, (List.mapM f xs).run s = .ok res
  | [], s, _ => ⟨([], s), rfl⟩
  | x :: xs, s, hf => by
    rw [List.mapM_cons]
    obtain ⟨⟨y, s'⟩, hy⟩ := hf x List.mem_cons_self s
    obtain ⟨⟨ys, s''⟩, hys⟩ :=
      mapM_list_stateT_ok f xs s' (fun z hz => hf z (List.mem_cons_of_mem x hz))
    refine ⟨(y :: ys, s''), ?_⟩
    change (do let a ← f x s; let b ← (List.mapM f xs).run a.2; pure (a.1 :: b.1, b.2)) =
      .ok (y :: ys, s'')
    rw [hy]
    dsimp only [bind, Except.bind]
    rw [hys]
    rfl

private theorem vector_mapM_stateT_isOk {ε S α β : Type} {n : Nat}
    (f : α → StateT S (Except ε) β) (xs : Vector α n) (s : S)
    (hf : ∀ x ∈ xs.toArray.toList, ∀ s', ∃ res, f x s' = .ok res) :
    ((Vector.mapM f xs).run s).isOk = true := by
  have h1 :
      ((Vector.toArray <$> Vector.mapM f xs).run s).isOk = ((Vector.mapM f xs).run s).isOk := by
    simp only [Functor.map, StateT.map, StateT.run, bind, Except.bind, pure, Except.pure,
      Except.isOk, Except.toBool]
    cases Vector.mapM f xs s <;> rfl
  have h2 :
      ((Array.toList <$> Array.mapM f xs.toArray).run s).isOk =
        ((Array.mapM f xs.toArray).run s).isOk := by
    simp only [Functor.map, StateT.map, StateT.run, bind, Except.bind, pure, Except.pure,
      Except.isOk, Except.toBool]
    cases Array.mapM f xs.toArray s <;> rfl
  rw [← h1, Vector.toArray_mapM, ← h2, Array.toList_mapM]
  obtain ⟨res, hres⟩ := mapM_list_stateT_ok f xs.toArray.toList s hf
  exact isOk_of_exists _ ⟨res, hres⟩

theorem admissible_observeTile_isOk {config : WorldConfig} (hadm : config.raw.admissible = true)
    (world : World config) (occupied : Occupancy)
    (row col : Fin Acorn.Host.patchSide) :
    (world.observeTile occupied row col).isOk = true := by
  have hps : Acorn.Host.patchSide = 11 := rfl
  have hr : col.val < 11 := hps ▸ col.isLt
  have hrv : row.val < 11 := hps ▸ row.isLt
  obtain ⟨tile, htr, hx_lo, hx_hi, hy_lo, hy_hi⟩ :=
    admissible_translate_isSome hadm world.body.position
      ((col.val : Int) - ↑(Acorn.Host.patchSide / 2))
      ((row.val : Int) - ↑(Acorn.Host.patchSide / 2))
      (by omega) (by omega)
  have htk := admissible_box_tileKind_isOk hadm world tile ⟨hx_lo, hx_hi⟩ ⟨hy_lo, hy_hi⟩
  unfold World.observeTile
  dsimp only
  rw [htr]
  cases hk : world.tileKind tile with
  | error e => rw [hk] at htk; cases htk
  | ok kind => simp only [hk]; rfl

theorem observe_isOk_iff_tiles {config : WorldConfig} (world : World config) :
    (world.observe).isOk = true ↔
      ∀ row col : Fin Acorn.Host.patchSide,
        (world.observeTile world.occupancy row col).isOk = true := by
  have hinner :
      (do
        let tiles ← Vector.ofFnM fun row => Vector.ofFnM (world.observeTile world.occupancy row)
        pure {
          tiles := tiles
          energy := (min (world.body.energy.val / 100) 10).toUInt8
          day := world.dayPhase.val.toUInt8
          task := world.taskObservation
          inventory := world.body.inventory } : Except WorldError Observation).isOk = true ↔
      (Vector.ofFnM fun row => Vector.ofFnM (world.observeTile world.occupancy row)).isOk =
        true := by
    cases hvec : Vector.ofFnM fun row => Vector.ofFnM (world.observeTile world.occupancy row) with
    | error e => simp [bind, Except.bind, Except.isOk, Except.toBool]
    | ok tiles => simp [bind, Except.bind, pure, Except.pure, Except.isOk, Except.toBool]
  have hobs : (world.observe).isOk = true ↔
      (Vector.ofFnM fun row => Vector.ofFnM (world.observeTile world.occupancy row)).isOk =
        true := by
    unfold World.observe
    exact hinner
  rw [hobs, vector_ofFnM_isOk_iff]
  constructor
  · intro h row col
    exact (vector_ofFnM_isOk_iff _ _).mp (h row) col
  · intro h row
    exact (vector_ofFnM_isOk_iff _ _).mpr (h row)

theorem admissible_observe_isOk {config : WorldConfig} (hadm : config.raw.admissible = true)
    (world : World config) : (world.observe).isOk = true :=
  (observe_isOk_iff_tiles world).mpr fun row col =>
    admissible_observeTile_isOk hadm world world.occupancy row col

private theorem bind_isOk_exist {ε α β : Type} (x : Except ε α) (f : α → Except ε β)
    (hx : x.isOk = true) (hf : ∀ a, x = .ok a → ∃ b, f a = .ok b) :
    ∃ b, (x >>= f) = .ok b := by
  cases h : x with
  | error e => rw [h] at hx; cases hx
  | ok a =>
    obtain ⟨b, hb⟩ := hf a h
    exact ⟨b, by simp only [bind, Except.bind, hb]⟩

private theorem observeTile_translate_none {config : WorldConfig} (world : World config)
    (occupied : Occupancy) (row col : Fin Acorn.Host.patchSide)
    (htr : world.body.position.position.translate
      (↑col.val - ↑(Acorn.Host.patchSide / 2))
      (↑row.val - ↑(Acorn.Host.patchSide / 2)) = none) :
    (world.observeTile occupied row col).isOk = false := by
  unfold World.observeTile
  dsimp only
  rw [htr]
  rfl

theorem observe_refuses_exceeds_maxSide {config : WorldConfig}
    (hbad : RawWorldConfig.maxSide < config.raw.side.val)
    (world : World config) (hpos : world.body.position.x.val = config.side - 1) :
    (world.observe).isOk = false := by
  have hside := config.positiveSide
  have hlim : RawWorldConfig.maxSide = 2 ^ 63 - 5 := rfl
  have hpx : world.body.position.position.x.val = (world.body.position.x.val : Int) := rfl
  have hside_eq : (config.side : Int) = config.raw.side.val := by
    unfold WorldConfig.side; omega
  have hover : Coordinate.checked (world.body.position.position.x.val + 5) = none := by
    unfold Coordinate.checked
    split
    · omega
    · rfl
  have h5 : 5 < Acorn.Host.patchSide := by decide
  have h10 : 10 < Acorn.Host.patchSide := by decide
  let r5 : Fin Acorn.Host.patchSide := ⟨5, h5⟩
  let c10 : Fin Acorn.Host.patchSide := ⟨10, h10⟩
  have hdx : (↑c10.val - ↑(Acorn.Host.patchSide / 2) : Int) = 5 := rfl
  have htr : world.body.position.position.translate
      (↑c10.val - ↑(Acorn.Host.patchSide / 2))
      (↑r5.val - ↑(Acorn.Host.patchSide / 2)) = none := by
    unfold Position.translate
    rw [hdx, hover]
    rfl
  have htile := observeTile_translate_none world world.occupancy r5 c10 htr
  have hfalse : ¬ (world.observe).isOk = true := by
    intro hobs
    have h := (observe_isOk_iff_tiles world).mp hobs r5 c10
    rw [htile] at h
    cases h
  exact Bool.eq_false_iff.mpr hfalse

theorem admissible_enterable_of_deerCap {config : WorldConfig}
    (hadm : config.raw.admissible = true) (hcap : config.raw.deerCap ≠ 0)
    (world : World config) (tile : Position) :
    (world.enterable tile).isOk = true := by
  obtain ⟨hpos, hmax, _, _⟩ := (RawWorldConfig.admissible_iff config.raw).mp hadm
  have hx := tile.x.property
  have hy := tile.y.property
  have hx_adm :
      config.raw.admitLo.val ≤ tile.x.val ∧ tile.x.val ≤ config.raw.admitHi.val := by
    rw [config.raw.admitLo_val, config.raw.admitHi_val hpos hmax,
      ite_eq_right hcap, ite_eq_right hcap]
    exact ⟨hx.1, by omega⟩
  have hy_adm :
      config.raw.admitLo.val ≤ tile.y.val ∧ tile.y.val ≤ config.raw.admitHi.val := by
    rw [config.raw.admitLo_val, config.raw.admitHi_val hpos hmax,
      ite_eq_right hcap, ite_eq_right hcap]
    exact ⟨hy.1, by omega⟩
  have htk := admissible_tileKind_isOk hadm world tile hx_adm hy_adm
  unfold World.enterable
  cases hk : world.tileKind tile with
  | error e => rw [hk] at htk; cases htk
  | ok kind => rfl

theorem admissible_wanderPopulation_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) :
    (wanderPopulation world).isOk = true := by
  unfold wanderPopulation
  dsimp only
  have hvec : ((Vector.mapM (m := StateT Rng.Xoshiro256 (Except WorldError))
      (fun position => wanderDeer world position)
      (⟨world.deer.entries, rfl⟩ : Vector Position world.deer.entries.size)).run
        world.rng).isOk = true := by
    apply vector_mapM_stateT_isOk
    intro pos hmem rng
    by_cases hcap : config.raw.deerCap = 0
    · have hsz := world.deer.bounded
      have hto : world.deer.entries.size = 0 := by
        have : config.raw.deerCap.toNat = 0 := by rw [hcap]; rfl
        omega
      have hempty : world.deer.entries.toList = [] := by
        cases h : world.deer.entries.toList with
        | nil => rfl
        | cons _ _ =>
          have hl : world.deer.entries.toList.length = world.deer.entries.size :=
            Array.length_toList
          rw [h] at hl
          simp at hl
          omega
      rw [hempty] at hmem
      cases hmem
    · unfold wanderDeer
      dsimp only
      by_cases hroll : rng.next.1 % 100 < 8
      · rw [ite_eq_left hroll]
        split
        · exact ⟨_, rfl⟩
        · rename_i candidate _
          have hent := admissible_enterable_of_deerCap hadm hcap world candidate
          unfold World.enterable at hent
          cases hk : world.tileKind candidate with
          | error e => rw [hk] at hent; cases hent
          | ok kind => exact ⟨_, rfl⟩
      · rw [ite_eq_right hroll]
        exact ⟨_, rfl⟩
  cases hrun : (Vector.mapM (m := StateT Rng.Xoshiro256 (Except WorldError))
      (fun position => wanderDeer world position)
      (⟨world.deer.entries, rfl⟩ : Vector Position world.deer.entries.size)).run world.rng with
  | error e => rw [hrun] at hvec; cases hvec
  | ok pair =>
    simp only [bind, Except.bind, pure, Except.pure, Except.isOk, Except.toBool]

theorem admissible_foodTrials_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) :
    ∀ (n : Nat) (rng : Rng.Xoshiro256), ∃ res, foodTrials world n rng = .ok res
  | 0, rng => ⟨(none, rng), foodTrials.eq_1 world rng⟩
  | n + 1, rng => by
    rw [foodTrials.eq_2]
    cases hdraw : drawBoxPosition config rng with
    | mk position nextRng =>
      dsimp only
      have htk := admissible_boxPosition_tileKind_isOk hadm world position
      cases hk : world.tileKind position.position with
      | error e => rw [hk] at htk; cases htk
      | ok kind =>
        by_cases hg : (kind == TileKind.grass) = true
        · exact ⟨(some position, nextRng), by simp [hg, bind, Except.bind, pure, Except.pure]⟩
        · obtain ⟨res, hres⟩ := admissible_foodTrials_isOk hadm world n nextRng
          exact ⟨res, by simp [hg, hres, bind, Except.bind]⟩

theorem admissible_spawnFood_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) (rng : Rng.Xoshiro256) :
    (spawnFood world rng).isOk = true := by
  unfold spawnFood
  by_cases hcond : (decide (FoodDue world.time config.raw.foodInterval) &&
      decide (world.food.entries.size < config.raw.foodCap.toNat)) = true
  · rw [ite_eq_left hcond]
    obtain ⟨res, hres⟩ := admissible_foodTrials_isOk hadm world 8 rng
    dsimp only
    rw [hres]
    rfl
  · rw [ite_eq_right hcond]
    rfl

theorem admissible_actionAdmits {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) (action : Action) :
    CurrentActions.ActionAdmits world action := by
  have hside_eq : (config.side : Int) = config.raw.side.val := by
    unfold WorldConfig.side
    have := config.positiveSide
    omega
  have hin_box : ∀ tile : Position,
      0 ≤ tile.x.val → tile.x.val < config.side →
      0 ≤ tile.y.val → tile.y.val < config.side →
        CurrentTerrain.LatticeAdmits tile config.raw.baseScale := by
    intro tile hx0 hxs hy0 hys
    rw [hside_eq] at hxs hys
    exact admissible_latticeAdmits hadm tile
      (admissible_inBoxMargin hadm tile.x (by omega) (by omega))
      (admissible_inBoxMargin hadm tile.y (by omega) (by omega))
  have hreads : ∀ dx dy : Int, -5 ≤ dx ∧ dx ≤ 5 → -5 ≤ dy ∧ dy ≤ 5 →
      CurrentActions.Reads world dx dy := by
    intro dx dy hdx hdy tile htx hty
    have hxs : (world.body.position.x.val : Int) < config.raw.side.val := by
      have := world.body.position.x.isLt
      omega
    have hys : (world.body.position.y.val : Int) < config.raw.side.val := by
      have := world.body.position.y.isLt
      omega
    have hpx : (world.body.position.x.val : Int) = world.body.position.position.x.val := rfl
    have hpy : (world.body.position.y.val : Int) = world.body.position.position.y.val := rfl
    exact admissible_latticeAdmits hadm tile
      (admissible_inBoxMargin hadm tile.x (by omega) (by omega))
      (admissible_inBoxMargin hadm tile.y (by omega) (by omega))
  cases action with
  | north => intro tile _ _ hx0 hxs hy0 hys; exact hin_box tile hx0 hxs hy0 hys
  | south => intro tile _ _ hx0 hxs hy0 hys; exact hin_box tile hx0 hxs hy0 hys
  | east => intro tile _ _ hx0 hxs hy0 hys; exact hin_box tile hx0 hxs hy0 hys
  | west => intro tile _ _ hx0 hxs hy0 hys; exact hin_box tile hx0 hxs hy0 hys
  | harvest =>
    unfold CurrentActions.ActionAdmits CurrentActions.Faces
    cases world.body.facing with
    | north => exact hreads 0 (-1) (by omega) (by omega)
    | south => exact hreads 0 1 (by omega) (by omega)
    | east => exact hreads 1 0 (by omega) (by omega)
    | west => exact hreads (-1) 0 (by omega) (by omega)
  | wait | craftAxe | craftBoat | eat => trivial

theorem admissible_payAndAct_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) (action : Action) :
    (payAndAct world action).isOk = true :=
  (CurrentActions.payAndAct_isOk world action).mpr fun _ =>
    admissible_actionAdmits hadm world action

theorem admissible_step_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) (action : Action) :
    (world.step action).isOk = true := by
  unfold World.step passiveChange
  apply isOk_of_exists
  have hpa := admissible_payAndAct_isOk hadm world action
  cases hact : payAndAct world action with
  | error e => rw [hact] at hpa; cases hpa
  | ok active =>
    dsimp only
    let acted : World config := {
      time := (world.applyActive active).time + 1
      body := (world.applyActive active).body
      goal := (world.applyActive active).goal
      goalStart := (world.applyActive active).goalStart
      harvested := (world.applyActive active).harvested
      deer := (world.applyActive active).deer
      food := (world.applyActive active).food
      rng := (world.applyActive active).rng }
    have hwp := admissible_wanderPopulation_isOk hadm acted
    cases hdeer : wanderPopulation acted with
    | error e => rw [hdeer] at hwp; cases hwp
    | ok deerPair =>
      have hsf := admissible_spawnFood_isOk hadm acted deerPair.2
      cases hfood : spawnFood acted deerPair.2 with
      | error e => rw [hfood] at hsf; cases hsf
      | ok foodPair =>
        dsimp only [bind, Except.bind, pure, Except.pure]
        rw [hdeer]
        dsimp only [bind, Except.bind]
        rw [hfood]
        exact ⟨_, rfl⟩

theorem admissible_advanceActions_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) (actions : List Action) :
    (world.advanceActions actions).isOk = true := by
  induction actions generalizing world with
  | nil => rw [World.advanceActions.eq_1]; rfl
  | cons action rest ih =>
    rw [World.advanceActions.eq_2]
    have hstep := admissible_step_isOk hadm world action
    cases hs : world.step action with
    | error e => rw [hs] at hstep; cases hstep
    | ok pair => exact ih pair.1

theorem admissible_countKindNear_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config)
    (pos : BoxPosition config) (radius : Nat) (hr : radius ≤ 5) (kind : TileKind) :
    (countKindNear world pos.position radius kind).isOk = true := by
  unfold countKindNear
  apply isOk_of_exists
  apply forIn_range_bind_ok
  · intro row count hrow
    apply forIn_range_bind_ok
    · intro col cnt hcol
      obtain ⟨tile, htr, hx_lo, hx_hi, hy_lo, hy_hi⟩ :=
        admissible_translate_isSome hadm pos
          ((col : Int) - radius) ((row : Int) - radius) (by omega) (by omega)
      have htk := admissible_box_tileKind_isOk hadm world tile ⟨hx_lo, hx_hi⟩ ⟨hy_lo, hy_hi⟩
      dsimp only
      rw [htr]
      dsimp only
      cases hk : world.tileKind tile with
      | error e => rw [hk] at htk; cases htk
      | ok found =>
        simp only [bind, Except.bind, pure, Except.pure]
        cases (found == kind) <;> exact ⟨_, rfl⟩
    · intro res; exact ⟨_, rfl⟩
  · intro res; exact ⟨_, rfl⟩

theorem admissible_considerSpawn_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config)
    (x y : Int) (best : Option (SpawnCandidate config)) :
    (considerSpawn world x y best).isOk = true := by
  unfold considerSpawn
  cases hbox : BoxPosition.checked config x y with
  | none => rfl
  | some pos =>
    dsimp only
    have ht := admissible_countKindNear_isOk hadm world pos 4 (by omega) .tree
    have hs := admissible_countKindNear_isOk hadm world pos 4 (by omega) .stone
    have hk := admissible_boxPosition_tileKind_isOk hadm world pos
    cases ht' : countKindNear world pos.position 4 .tree with
    | error e => rw [ht'] at ht; cases ht
    | ok trees =>
      cases hs' : countKindNear world pos.position 4 .stone with
      | error e => rw [hs'] at hs; cases hs
      | ok stone =>
        cases hk' : world.tileKind pos.position with
        | error e => rw [hk'] at hk; cases hk
        | ok kind =>
          simp only [bind, Except.bind]
          cases kind.walkable <;> rfl

theorem admissible_selectSpawn_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) :
    (selectSpawn world).isOk = true := by
  unfold selectSpawn
  apply isOk_of_exists
  apply forIn_range_bind_ok
  · intro radius state _
    apply forIn_range_bind_ok
    · intro dir st _
      dsimp only
      apply forIn_range_bind_ok
      · intro off inner _
        apply bind_isOk_exist
        · exact admissible_considerSpawn_isOk hadm world _ _ inner.snd
        · intro pair _
          cases pair.snd <;> exact ⟨_, rfl⟩
      · intro res; cases res.fst <;> exact ⟨_, rfl⟩
    · intro res; cases res.fst <;> exact ⟨_, rfl⟩
  · intro res; cases res.fst <;> exact ⟨_, rfl⟩

theorem admissible_initializeDeer_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) :
    (initializeDeer world).isOk = true := by
  unfold initializeDeer
  apply isOk_of_exists
  apply forIn_range_bind_ok
  · intro _ state _
    unfold placeDeer
    cases hdraw : drawBoxPosition config state.2 with
    | mk pos nextRng =>
      dsimp only
      rw [hdraw]
      have htk := admissible_boxPosition_tileKind_isOk hadm world pos
      cases hk : world.tileKind pos.position with
      | error e => rw [hk] at htk; cases htk
      | ok kind =>
        simp only [bind, Except.bind, pure, Except.pure]
        exact ⟨_, rfl⟩
  · intro res; exact ⟨_, rfl⟩

theorem admissible_initial_isOk {config : WorldConfig}
    (hadm : config.raw.admissible = true) : (World.initial config).isOk = true := by
  unfold World.initial
  simp only [hadm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  have hs := admissible_selectSpawn_isOk hadm (World.empty config)
  cases hspawn : selectSpawn (World.empty config) with
  | error e => rw [hspawn] at hs; cases hs
  | ok spawn =>
    have hd := admissible_initializeDeer_isOk hadm (World.empty config)
    cases hdeer : initializeDeer (World.empty config) with
    | error e => rw [hdeer] at hd; cases hd
    | ok pair => rfl

theorem initial_isOk_iff (config : WorldConfig) :
    (World.initial config).isOk = true ↔ config.raw.admissible = true := by
  constructor
  · intro ok
    cases hinit : World.initial config with
    | error e => rw [hinit] at ok; cases ok
    | ok world => exact World.initial_admissible config world hinit
  · exact admissible_initial_isOk

inductive Reachable {config : WorldConfig} (initial : World config) : World config → Prop
  | refl : Reachable initial initial
  | step {world next : World config} {events : StepResult} (action : Action) :
      Reachable initial world →
      world.step action = .ok (next, events) →
      Reachable initial next
  | setGoal {world : World config} (goal : Goal) :
      Reachable initial world →
      Reachable initial (world.setGoal goal)

theorem admitted_world_nonrefusal {config : WorldConfig}
    (hadm : config.raw.admissible = true) (world : World config) :
    (world.observe).isOk = true ∧
      (∀ action : Action, (world.step action).isOk = true) ∧
      (∀ actions : List Action, (world.advanceActions actions).isOk = true) :=
  ⟨admissible_observe_isOk hadm world,
    fun action => admissible_step_isOk hadm world action,
    fun actions => admissible_advanceActions_isOk hadm world actions⟩

theorem initial_reachable_nonrefusal {config : WorldConfig} (initial world : World config)
    (hinit : World.initial config = .ok initial) (_ : Reachable initial world) :
    (world.observe).isOk = true ∧
      (∀ action : Action, (world.step action).isOk = true) ∧
      (∀ actions : List Action, (world.advanceActions actions).isOk = true) :=
  admitted_world_nonrefusal (World.initial_admissible config initial hinit) world

theorem admitted_config_reachable_nonrefusal {raw : RawWorldConfig} {config : WorldConfig}
    (hadmit : WorldConfig.admit raw = .ok config) (initial world : World config)
    (_ : World.initial config = .ok initial) (_ : Reachable initial world) :
    (world.observe).isOk = true ∧
      (∀ action : Action, (world.step action).isOk = true) ∧
      (∀ actions : List Action, (world.advanceActions actions).isOk = true) :=
  admitted_world_nonrefusal (WorldConfig.admit_admissible raw config hadmit) world

end AcornVerif.CurrentWorld
