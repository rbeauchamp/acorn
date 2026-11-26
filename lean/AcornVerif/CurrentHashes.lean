import Acorn.Features
import Acorn.Host.AgentConstruction
import Acorn.Host.Task
import Acorn.Host.Terrain

namespace AcornVerif.CurrentHashes
open Acorn Acorn.Host Acorn.Features

def standard : Handcrafted.AgentConstruction :=
  Handcrafted.AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .expectation .learnThenAct

theorem unit_not_tiled : ¬∀ (dimension : Dimension) (config : Features.Config)
    (unit : Fin config.units.count) (tiling : Nat), tiling < config.tilings.toNat →
      unitFeature dimension config unit ∈
        tiledFeatures dimension config [⟨tiling.toUInt64, unit.val.toUInt64⟩] := by
  intro tiled
  have member := tiled standard.dimension standard.config ⟨0, by decide⟩ 0 (by decide)
  rw [tiledFeatures_def] at member
  revert member
  decide +kernel

theorem unit_tag_tiling (dimension : Dimension) (config : Features.Config)
    (unit : Fin config.units.count) (more : 0x1D < config.tilings.toNat) :
    unitFeature dimension config unit ∈
      tiledFeatures dimension config [⟨0x1D, unit.val.toUInt64⟩] := by
  rw [tiledFeatures_def, List.mem_flatMap]
  exact ⟨0x1D, List.mem_range.mpr more, List.mem_singleton.mpr rfl⟩

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

theorem reach_not_find_cue (target : Position) :
    Goal.cue (.reach ⟨⟨4, by decide⟩, ⟨0, by decide⟩⟩) ≠ Goal.cue (.find target) := by
  simp only [Goal.cue]
  decide +kernel

theorem moisture_not_elevation : ¬∀ (x x' y : Coordinate) (seed : UInt64),
    coordinateWord x' = coordinateWord x ^^^ 3 →
      lattice x y (seed ^^^ 0xe1e0e1e000000002) = lattice x' y (seed ^^^ 0xe1e0e1e000000001) :=
  fun same => absurd
    (same ⟨0, by decide⟩ ⟨3, by decide⟩ ⟨0, by decide⟩ 0 (by decide +kernel))
    (by decide +kernel)

theorem tree_not_ore_draw : ¬∀ (x x' y : Coordinate) (seed : UInt64),
    coordinateWord x' = coordinateWord x ^^^ 14 →
      Rng.hash2 (coordinateWord x) (coordinateWord y) (seed ^^^ 7) =
        Rng.hash2 (coordinateWord x') (coordinateWord y) (seed ^^^ 9) :=
  fun same => absurd
    (same ⟨0, by decide⟩ ⟨14, by decide⟩ ⟨0, by decide⟩ 0 (by decide +kernel))
    (by decide +kernel)

def single : PatchShape := ⟨1, by decide, by decide⟩

theorem sample_not_xor : ¬∀ (shape : PatchShape) (seed : UInt64) (unit sampleNumber k : Nat)
    (patch : Patch shape) (sample : Sample shape),
      sampleTerm seed unit sampleNumber patch sample =
        sampleTerm seed (unit ^^^ k) (sampleNumber ^^^ k) patch sample :=
  fun same => absurd (same single 0 0 2 1 #v[0] ⟨⟨0, by decide⟩, true⟩) (by decide +kernel)

end AcornVerif.CurrentHashes
