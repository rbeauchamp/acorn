/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Campaign

/-!
# Current host curriculum

This is externally declared task content, outside the learned core. Targets
retain their deterministic seed/hash and two distance scales. The host defines
the target predicates; reachability depends on the generated world and box.
-/
namespace Acorn.Host

/-- A finite host curriculum pairs each goal with its difficulty tier. -/
abbrev Curriculum := Array (Goal × UInt8)

/-- Exact target coordinate around the campaign center at a bounded curriculum radius. -/
def curriculumCoordinate (side : Coordinate) (seed tag : UInt64)
    (radius : Fin 121) (positive : 0 < radius.val) : Coordinate :=
  let modulus : UInt64 := (2 * radius.val).toUInt64
  let draw := (Rng.hash2 seed tag 0xabcd % modulus).toNat
  have hm : modulus.toNat = 2 * radius.val := by
    change (2 * radius.val) % (2 ^ 64) = 2 * radius.val
    apply Nat.mod_eq_of_lt
    have := radius.isLt
    omega
  have hd : draw < 2 * radius.val := by
    dsimp [draw]
    rw [UInt64.toNat_mod, hm]
    exact Nat.mod_lt _ (by omega)
  let value : Int := side.val.tdiv 2 + (draw : Int) - radius.val
  ⟨value, by
    have hs := side.property
    have hlo := Int.tdiv_le_tdiv (c := 2) (by decide) hs.1
    have hhi := Int.tdiv_le_tdiv (c := 2) (by decide) (Int.le_of_lt hs.2)
    change -4611686018427387904 ≤ side.val.tdiv 2 at hlo
    change side.val.tdiv 2 ≤ 4611686018427387904 at hhi
    have hr := radius.isLt
    dsimp [value] at *
    omega⟩

/-- Standard ordered goals and tiers, coupled in one vector before array conversion. -/
def rawStandardCurriculum (side : Coordinate) (seed : UInt64) : Curriculum :=
  let near : Fin 121 := ⟨min 40 (max 12 (side.val.tdiv 12).toNat), by omega⟩
  let far : Fin 121 := ⟨min 120 (max 24 (side.val.tdiv 6).toNat), by omega⟩
  let first : Position :=
    ⟨curriculumCoordinate side seed 1 near (by dsimp [near]; omega),
      curriculumCoordinate side seed 2 near (by dsimp [near]; omega)⟩
  let second : Position :=
    ⟨curriculumCoordinate side seed 3 far (by dsimp [far]; omega),
      curriculumCoordinate side seed 4 far (by dsimp [far]; omega)⟩
  #[ (.survive 200, 0), (.collect .wood 2, 0), (.collect .stone 2, 1), (.reach first, 1),
     (.collect .wood 4, 1), (.craft .axe, 2), (.collect .food 3, 2), (.reach second, 3),
     (.collect .gold 2, 3), (.craft .boat, 4), (.collect .wood 8, 4), (.survive 800, 5),
     (.collect .gold 4, 5) ]

/-- Campaign construction reuses the complete signed public curriculum domain. -/
def standardCurriculum (config : WorldConfig) (seed : UInt64) : Curriculum :=
  rawStandardCurriculum config.raw.side seed

/-- Public indexing repeats the final goal and tier for every oversized index. -/
def standardCurriculumEntry (side : Coordinate) (seed : UInt64) (index : UInt64) : Goal × UInt8 :=
  (rawStandardCurriculum side seed)[min index.toNat 12]'(by change min index.toNat 12 < 13; omega)

/-- Standard curriculum size is independent of seed, geometry, and sampled target words. -/
theorem standardCurriculum_size (config : WorldConfig) (seed : UInt64) :
    (standardCurriculum config seed).size = 13 := rfl

end Acorn.Host
