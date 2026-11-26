import Acorn.FeatureConstants
import Acorn.FeatureConsumers

namespace Acorn.Features

abbrev ModelAge := Fin (Acorn.FeatureConstants.optionMaxDuration + 1)

def ModelAge.advance (age : ModelAge) : ModelAge :=
  ⟨min (age.val + 1) Acorn.FeatureConstants.optionMaxDuration, by
    have := Nat.min_le_right (age.val + 1) Acorn.FeatureConstants.optionMaxDuration
    omega⟩

theorem ModelAge.advance_bounds (age : ModelAge) :
    age.val ≤ age.advance.val ∧ age.advance.val ≤ age.val + 1 := by
  have := age.isLt
  simp only [ModelAge.advance]
  omega

def ModelAge.feature (dimension : Dimension) (age : ModelAge) : FeatIdx dimension :=
  FeatIdx.fromHash dimension (Rng.hash3 0x6f7074696d65 0 age.val.toUInt64)

def modelInputCosted {dimension : Dimension} (criterion : Criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    Costed (SwiftTd.ActiveSet dimension) :=
  match criterion with
  | .discounted => Costed.pure base
  | .differential => do
    let slot ← Costed.op .hashFeature (age.feature dimension)
    insertCosted base slot

def modelInput {dimension : Dimension} (criterion : Criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) : SwiftTd.ActiveSet dimension :=
  (modelInputCosted criterion base age).val

theorem modelInput_def {dimension : Dimension} (criterion : Criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    modelInput criterion base age = match criterion with
      | .discounted => base
      | .differential => insert base (age.feature dimension) := by
  cases criterion <;> rfl

theorem modelInput_order {dimension : Dimension} (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (modelInput .differential base age).indices = base.indices ++
      (if age.feature dimension ∈ base.indices then [] else [age.feature dimension]) :=
  insert_order base (age.feature dimension)

theorem modelInput_preserves {dimension : Dimension} (criterion : Criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (feature : FeatIdx dimension)
    (member : feature ∈ base.indices) : feature ∈ (modelInput criterion base age).indices := by
  cases criterion
  · exact member
  · exact (mem_insert _ _ _).mpr (Or.inl member)

theorem modelInput_membership {dimension : Dimension} (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (feature : FeatIdx dimension) :
    feature ∈ (modelInput .differential base age).indices ↔
      feature ∈ base.indices ∨ feature = age.feature dimension := mem_insert _ _ _

end Acorn.Features
