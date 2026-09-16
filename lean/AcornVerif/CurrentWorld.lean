/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.WorldObservation
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


/-- Every supported standard side is admitted, for every seed. Configuration
admission is separate from the terrain-dependent `World.initial` operation. -/
theorem standard_config_exists (seed : UInt64) (side : Coordinate)
    (lower : FeatureConstants.worldMinSide ≤ side.val)
    (upper : side.val ≤ FeatureConstants.worldMaxSide) :
    ∃ config, WorldConfig.standard seed side = .ok config := by
  unfold WorldConfig.standard
  split
  · omega
  · split
    · omega
    · exact ⟨_, rfl⟩

/-- Every standard-world body has representable coordinates throughout its
actual sensor neighborhood. This closes translation refusal, not terrain refusal. -/
theorem standard_body_translation (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (position : BoxPosition config) (dx dy : Int)
    (hx : -(patchShape.side / 2 : Nat) ≤ dx ∧ dx ≤ (patchShape.side / 2 : Nat))
    (hy : -(patchShape.side / 2 : Nat) ≤ dy ∧ dy ≤ (patchShape.side / 2 : Nat)) :
    ∃ next, position.position.translate dx dy = some next := by
  have fields := WorldConfig.standard_bounds seed side config standard
  have xs := position.x.isLt
  have ys := position.y.isLt
  have rawSide : config.side = side.val.toNat := by
    simp only [WorldConfig.side, fields.1]
  have xsBound : position.x.val < side.val.toNat := lt_of_lt_of_eq xs rawSide
  have ysBound : position.y.val < side.val.toNat := lt_of_lt_of_eq ys rawSide
  have maximum : side.val ≤ 3000000000 := fields.2.2
  have xbound : -(2^63 : Int) ≤ position.position.x.val + dx ∧
      position.position.x.val + dx < 2^63 := by
    dsimp only [BoxPosition.position]
    change -(5 : Int) ≤ dx ∧ dx ≤ 5 at hx
    omega
  have ybound : -(2^63 : Int) ≤ position.position.y.val + dy ∧
      position.position.y.val + dy < 2^63 := by
    dsimp only [BoxPosition.position]
    change -(5 : Int) ≤ dy ∧ dy ≤ 5 at hy
    omega
  have xok : Coordinate.checked (position.position.x.val + dx) =
      some (⟨_, xbound⟩ : Coordinate) := dif_pos xbound
  have yok : Coordinate.checked (position.position.y.val + dy) =
      some (⟨_, ybound⟩ : Coordinate) := dif_pos ybound
  exact ⟨⟨⟨_, xbound⟩, ⟨_, ybound⟩⟩, by
    simp only [Position.translate, xok, yok, Option.pure_def]
    rfl⟩

/-- The standard spawn spiral's actual pre-box signed admissions cannot overflow.
Outside-box candidates may still be skipped; terrain-dependent scoring is separate. -/
theorem standard_spiral_coordinates (seed : UInt64) (side : Coordinate)
    (config : WorldConfig) (standard : WorldConfig.standard seed side = .ok config)
    (radius offset : Nat) (hr : radius < config.side) (ho : offset < 2 * radius + 1)
    (direction : Direction) :
    let k : Int := (offset : Int) - radius
    let x := (config.side / 2 : Nat) + direction.delta.1 * radius + direction.delta.2 * k
    let y := (config.side / 2 : Nat) + direction.delta.2 * radius + direction.delta.1 * k
    ∃ cx cy, Coordinate.checked x = some cx ∧ Coordinate.checked y = some cy := by
  have fields := WorldConfig.standard_bounds seed side config standard
  have sideBound : config.side ≤ 3000000000 := by
    have h := fields.2.2
    change side.val ≤ 3000000000 at h
    simp only [WorldConfig.side, fields.1]
    omega
  have centerBound := Nat.div_le_self config.side 2
  dsimp only
  have bounds :
      (-(2^63 : Int) ≤ (config.side / 2 : Nat) + direction.delta.1 * radius +
        direction.delta.2 * ((offset : Int) - radius) ∧
      (config.side / 2 : Nat) + direction.delta.1 * radius +
        direction.delta.2 * ((offset : Int) - radius) < 2^63) ∧
      (-(2^63 : Int) ≤ (config.side / 2 : Nat) + direction.delta.2 * radius +
        direction.delta.1 * ((offset : Int) - radius) ∧
      (config.side / 2 : Nat) + direction.delta.2 * radius +
        direction.delta.1 * ((offset : Int) - radius) < 2^63) := by
    cases direction <;> simp only [Direction.delta, zero_mul, one_mul, neg_mul,
      add_zero] <;> omega
  exact ⟨⟨_, bounds.1⟩, ⟨_, bounds.2⟩, by
    simp only [Coordinate.checked, bounds.1, bounds.2, ↓reduceDIte, and_self]⟩

end AcornVerif.CurrentWorld
