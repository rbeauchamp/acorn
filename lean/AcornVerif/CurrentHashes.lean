/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Features
import Acorn.Host.AgentConstruction
import Acorn.Host.Task
import Acorn.Host.Terrain

/-!
# The first two words of the executed hashes

`Rng.hash3` and `Rng.hash2` mix their first word before the second enters. Two calls with one
last word agree exactly when their first two words agree after that mix (`Rng.hash3_eq_iff`,
`Rng.hash2_eq_iff`), so neither hash is a function of the XOR of its first two words
(`Rng.hash3_not_xor`, `Rng.hash2_not_xor`).

A hash that read its first two words only through their XOR would make each caller below
alias two inputs for every seed: the caller passes the two words as separate salts, and
inputs whose salts have one XOR would have one hash. Each theorem here refutes one such
aliasing with one input of the executed definitions, in the standard feature configuration at
seed 0 where it has a configuration. A refutation at one seed shows that the aliasing does not
follow from the definitions; whether two given inputs collide at another seed is a property of
the mixer at that seed, which nothing here states.

`unit_tag_tiling` states the one identity the mix leaves: the unit slot map hashes the words
that the tiled coder hashes for the word with channel `0x1D` in tiling `0x1D`.
-/

namespace AcornVerif.CurrentHashes
open Acorn Acorn.Host Acorn.Features

/-- The standard construction at seed 0: the ranked profile with the discounted criterion,
expectation planning and the learn-then-act order. Its feature configuration has 8 tilings
and 512 units, and its feature space 16384 indices. -/
def standard : Handcrafted.AgentConstruction :=
  Handcrafted.AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .expectation .learnThenAct

/-- The slot of a unit is not the slot, in every tiling below the tiling count, of the word
whose channel is the tiling's number and whose value is the unit's number: in the standard
configuration at seed 0, the slot of unit 0 is the slot of the word with channel 0 and value 0
in none of the 8 tilings. -/
theorem unit_not_tiled : ¬∀ (dimension : Dimension) (config : Features.Config)
    (unit : Fin config.units.count) (tiling : Nat), tiling < config.tilings.toNat →
      unitFeature dimension config unit ∈
        tiledFeatures dimension config [⟨tiling.toUInt64, unit.val.toUInt64⟩] := by
  intro tiled
  have member := tiled standard.dimension standard.config ⟨0, by decide⟩ 0 (by decide)
  rw [tiledFeatures_def] at member
  revert member
  decide +kernel

/-- When the tiling count exceeds `0x1D`, the slot of a unit is the slot of the word with
channel `0x1D` and the unit's number as value in tiling `0x1D`, for every dimension,
configuration and unit: the slot map hashes the seed XOR the tag `0x1D`, the tag and the unit's
number, which are the words that the tiled coder hashes for that word in that tiling. The
standard configuration has 8 tilings. -/
theorem unit_tag_tiling (dimension : Dimension) (config : Features.Config)
    (unit : Fin config.units.count) (more : 0x1D < config.tilings.toNat) :
    unitFeature dimension config unit ∈
      tiledFeatures dimension config [⟨0x1D, unit.val.toUInt64⟩] := by
  rw [tiledFeatures_def, List.mem_flatMap]
  exact ⟨0x1D, List.mem_range.mpr more, List.mem_singleton.mpr rfl⟩

/-- Under 8 tilings, a slot of the wood word (channel `0x43`) is not a slot of the stone word
(channel `0x44`) with the same value for every dimension and configuration: in the standard
configuration at seed 0, the slot of the wood word with value 0 in tiling 0 is a slot of the
stone word with value 0 in none of the 8 tilings. -/
theorem wood_not_stone : ¬∀ (dimension : Dimension) (config : Features.Config),
    config.tilings.toNat = 8 → ∀ (value : UInt64) (slot : FeatIdx dimension),
      slot ∈ tiledFeatures dimension config [⟨0x43, value⟩] →
        slot ∈ tiledFeatures dimension config [⟨0x44, value⟩] := by
  intro shared
  have wood : FeatIdx.fromHash standard.dimension (Rng.hash3 0 0x43 0) ∈
      tiledFeatures standard.dimension standard.config [⟨0x43, 0⟩] := by
    rw [tiledFeatures_def]
    decide +kernel
  have stone := shared standard.dimension standard.config (by decide) 0 _ wood
  rw [tiledFeatures_def] at stone
  revert stone
  decide +kernel

/-- A reach goal to (4, 0) has a cue other than the cue of every find goal. -/
theorem reach_not_find_cue (target : Position) :
    Goal.cue (.reach ⟨⟨4, by decide⟩, ⟨0, by decide⟩⟩) ≠ Goal.cue (.find target) := by
  simp only [Goal.cue]
  decide +kernel

/-- The moisture lattice at a column is not, for every seed, the elevation lattice at the
column whose word differs in the two low bits: at seed 0 and row 0, the moisture lattice at
column 0 and the elevation lattice at column 3 differ. The kernel evaluates the two binary32
lattice values. -/
theorem moisture_not_elevation : ¬∀ (x x' y : Coordinate) (seed : UInt64),
    coordinateWord x' = coordinateWord x ^^^ 3 →
      lattice x y (seed ^^^ 0xe1e0e1e000000002) = lattice x' y (seed ^^^ 0xe1e0e1e000000001) :=
  fun same => absurd
    (same ⟨0, by decide⟩ ⟨3, by decide⟩ ⟨0, by decide⟩ 0 (by decide +kernel))
    (by decide +kernel)

/-- The tree dither draw at a column is not, for every seed, the ore dither draw at the column
whose word differs in the bits of `7 ^^^ 9`: at seed 0 and row 0, the tree draw at column 0
and the ore draw at column 14 differ. -/
theorem tree_not_ore_draw : ¬∀ (x x' y : Coordinate) (seed : UInt64),
    coordinateWord x' = coordinateWord x ^^^ 14 →
      Rng.hash2 (coordinateWord x) (coordinateWord y) (seed ^^^ 7) =
        Rng.hash2 (coordinateWord x') (coordinateWord y) (seed ^^^ 9) :=
  fun same => absurd
    (same ⟨0, by decide⟩ ⟨14, by decide⟩ ⟨0, by decide⟩ 0 (by decide +kernel))
    (by decide +kernel)

/-- The shape with one input position. -/
def single : PatchShape := ⟨1, by decide, by decide⟩

/-- Sample `j` of unit `u` and sample `j ^^^ k` of unit `u ^^^ k` do not contribute one term
for every seed, patch and sample: at seed 0, a positive sample of the code 0 contributes one as
sample 2 of unit 0 and zero as sample 3 of unit 1. -/
theorem sample_not_xor : ¬∀ (shape : PatchShape) (seed : UInt64) (unit sampleNumber k : Nat)
    (patch : Patch shape) (sample : Sample shape),
      sampleTerm seed unit sampleNumber patch sample =
        sampleTerm seed (unit ^^^ k) (sampleNumber ^^^ k) patch sample :=
  fun same => absurd (same single 0 0 2 1 #v[0] ⟨⟨0, by decide⟩, true⟩) (by decide +kernel)

end AcornVerif.CurrentHashes
