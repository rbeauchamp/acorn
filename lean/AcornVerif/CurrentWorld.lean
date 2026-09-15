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


end AcornVerif.CurrentWorld
