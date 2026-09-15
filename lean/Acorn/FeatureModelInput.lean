/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.FeatureConsumers

/-!
# Current age-augmented option-model features

Wan, Naik and Sutton, *Average-Reward Learning and Planning with Options*,
NeurIPS 34 (2021), section 5, equations (18)–(23),
https://proceedings.neurips.cc/paper_files/paper/2021/file/c058f544c737782deacefa532d9add4c-Paper.pdf.
The current adaptation adds one hashed age indicator to the model input.
Its bounded index and binary feature contract do not imply injectivity,
Markov sufficiency, or the paper's convergence hypotheses.
-/
namespace Acorn.Features

/-- Completed transitions, including the final permitted option age. -/
abbrev ModelAge := Fin (Acorn.FeatureConstants.optionMaxDuration + 1)

/-- The current saturating successor preserves the activation's fixed domain. -/
def ModelAge.advance (age : ModelAge) : ModelAge :=
  ⟨min (age.val + 1) Acorn.FeatureConstants.optionMaxDuration, by
    have := Nat.min_le_right (age.val + 1) Acorn.FeatureConstants.optionMaxDuration
    omega⟩

/-- Completed transitions cannot move backwards or wrap. -/
theorem ModelAge.advance_bounds (age : ModelAge) :
    age.val ≤ age.advance.val ∧ age.advance.val ≤ age.val + 1 := by
  have := age.isLt
  simp only [ModelAge.advance]
  omega

/-- The age slot uses the current domain-separated hash and receiving dimension. -/
def ModelAge.feature (dimension : Dimension) (age : ModelAge) : FeatIdx dimension :=
  FeatIdx.fromHash dimension (Rng.hash3 0x6f7074696d65 0 age.val.toUInt64)

/-- Discounted input is unchanged; differential input inserts at most one new slot. -/
def modelInput {dimension : Dimension} (criterion : Criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) : SwiftTd.ActiveSet dimension :=
  match criterion with
  | .discounted => base
  | .differential => insert base (age.feature dimension)

/-- Age aliases preserve the existing first-occurrence position of the slot. -/
theorem modelInput_order {dimension : Dimension} (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (modelInput .differential base age).indices = base.indices ++
      (if age.feature dimension ∈ base.indices then [] else [age.feature dimension]) :=
  insert_order base (age.feature dimension)

/-- Every base feature remains active under either criterion. -/
theorem modelInput_preserves {dimension : Dimension} (criterion : Criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (feature : FeatIdx dimension)
    (member : feature ∈ base.indices) : feature ∈ (modelInput criterion base age).indices := by
  cases criterion
  · exact member
  · exact (mem_insert _ _ _).mpr (Or.inl member)

/-- The exact differential membership includes all collisions, without an injectivity premise. -/
theorem modelInput_membership {dimension : Dimension} (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (feature : FeatIdx dimension) :
    feature ∈ (modelInput .differential base age).indices ↔
      feature ∈ base.indices ∨ feature = age.feature dimension := mem_insert _ _ _

end Acorn.Features
