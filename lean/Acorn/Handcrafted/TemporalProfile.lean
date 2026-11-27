import Acorn.Interface
import Acorn.Handcrafted.FeatureProfile

namespace Acorn.Handcrafted
open Features

def _root_.Acorn.Features.Frame.declared {interface : Interface} (frame : Frame interface) :
    DeclaredPotentials :=
  ⟨.spatialPotentials, frame.potentials⟩

def declaredRate : SwiftTd.ExploreRate := ⟨⟨Acorn.Constants.exploreRate1e2Bits⟩, by decide⟩

def annealedRange : Interval32 :=
  ⟨⟨Acorn.Constants.epsMinBits⟩, .one, by decide, by decide, by decide⟩

inductive RateState : RatePolicy → Type where
  | declared : RateState .declared
  | perLearner : RateState .perLearner
  | shared : RateState .shared
  | annealed (rate : Bounded32 annealedRange) : RateState .annealed

instance (policy : RatePolicy) : Provenance (RateState policy) := ⟨some .explorationRate⟩

def RateState.initial : (policy : RatePolicy) → RateState policy
  | .declared => .declared
  | .perLearner => .perLearner
  | .shared => .shared
  | .annealed => .annealed (Bounded32.project annealedRange ⟨Acorn.Constants.epsStartBits⟩)

def RateState.advance {policy : RatePolicy} : RateState policy → RateState policy
  | .declared => .declared
  | .perLearner => .perLearner
  | .shared => .shared
  | .annealed rate => .annealed (Bounded32.project annealedRange
      (rate.value.mul ⟨Acorn.Constants.epsDecayBits⟩))

def RateState.controller {policy : RatePolicy} (state : RateState policy)
    (own primitive : Unit → SwiftTd.ExploreRate) : SwiftTd.ExploreRate :=
  match state with
  | .declared => declaredRate
  | .perLearner => own ()
  | .shared => primitive ()
  | .annealed rate => SwiftTd.ExploreRate.project rate.value

def RateState.skill {policy : RatePolicy} (state : RateState policy)
    (primitive : Unit → SwiftTd.ExploreRate) : ConsumerRate :=
  match state with
  | .declared => .fixed declaredRate
  | .perLearner => .own
  | .shared => .fixed (primitive ())
  | .annealed _ => .fixed (SwiftTd.ExploreRate.project ⟨Acorn.Constants.optionEpsilonBits⟩)

def RateState.controllerCosted {policy : RatePolicy} (state : RateState policy)
    (own primitive : Unit → Costed SwiftTd.ExploreRate) : Costed SwiftTd.ExploreRate :=
  match state with
  | .declared => Costed.pure declaredRate
  | .perLearner => own ()
  | .shared => primitive ()
  | .annealed rate => Costed.op .rateClose (SwiftTd.ExploreRate.project rate.value)

theorem RateState.controllerCosted_val {policy : RatePolicy} (state : RateState policy)
    (own primitive : Unit → Costed SwiftTd.ExploreRate) :
    (state.controllerCosted own primitive).val =
      state.controller (fun unused => (own unused).val) fun unused => (primitive unused).val := by
  cases state <;> rfl

def RateState.skillCosted {policy : RatePolicy} (state : RateState policy)
    (primitive : Unit → Costed SwiftTd.ExploreRate) : Costed ConsumerRate :=
  match state with
  | .declared => Costed.pure (.fixed declaredRate)
  | .perLearner => Costed.pure .own
  | .shared => do
    let rate ← primitive ()
    Costed.pure (.fixed rate)
  | .annealed _ =>
    Costed.pure (.fixed (SwiftTd.ExploreRate.project ⟨Acorn.Constants.optionEpsilonBits⟩))

theorem RateState.skillCosted_val {policy : RatePolicy} (state : RateState policy)
    (primitive : Unit → Costed SwiftTd.ExploreRate) :
    (state.skillCosted primitive).val = state.skill fun unused => (primitive unused).val := by
  cases state <;> rfl

theorem RateState.declared_controller {policy : RatePolicy} (state : RateState policy)
    (declared : policy = .declared) (own primitive : Unit → SwiftTd.ExploreRate) :
    state.controller own primitive = declaredRate := by
  cases state <;> first | rfl | cases declared

theorem RateState.declared_skill {policy : RatePolicy} (state : RateState policy)
    (declared : policy = .declared) (primitive : Unit → SwiftTd.ExploreRate) :
    state.skill primitive = .fixed declaredRate := by
  cases state <;> first | rfl | cases declared

theorem annealed_write (rate : Bounded32 annealedRange) :
    annealedRange.Contains (Bounded32.project annealedRange
      (rate.value.mul ⟨Acorn.Constants.epsDecayBits⟩)).value := Bounded32.legal _

theorem spatial_admitted {interface : Interface} {config : Features.Config} {dimension : Dimension}
    (tag : Fin Acorn.FeatureConstants.skillCount) (features : SwiftTd.ActiveSet dimension)
    (frame : Frame interface) :
    (Interest.declared (config := config) .spatialPotentials tag).potential features frame.declared =
      some (frame.potentials.get tag) := by simp [Interest.potential_def, Frame.declared]

end Acorn.Handcrafted
