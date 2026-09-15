/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Options
import Acorn.Handcrafted.FeatureProfile
import Acorn.Host.Terrain

/-!
# Declared temporal comparison profiles

D2 is the raw spatial indicator; D3 supplies the annealed comparison and
persistent-duration law. Ranked targets and per-consumer rates reuse their
learned owners. These declarations preserve research choices without promoting
any profile or claiming a new exploration law.
-/
namespace Acorn.Handcrafted
open Features

/-- Current raw spatial potential observations, in option table order. -/
def spatialPotentials (obs : Host.Observation) : DeclaredPotentials :=
  let kind := fun code => obs.tiles.any (fun row => row.any (fun tile => tile.kind == code))
  ⟨.spatialPotentials, #v[
    kind Host.TileKind.tree.code,
    kind Host.TileKind.ore.code || kind Host.TileKind.stone.code,
    obs.tiles.any (fun row => row.any (fun tile => tile.food != 0))]⟩

/-- The schedule stores its actual closed interval, including the minimum. -/
def annealedRange : Interval32 :=
  ⟨⟨AcornSpec.Constants.epsMinBits⟩, .one, by decide, by decide, by decide⟩

/-- Schedule state exists only in the schedule-carrying rate policy. -/
inductive RateState : RatePolicy → Type where
  /-- Each consumer reads its own learner. -/
  | perLearner : RateState .perLearner
  /-- Every consumer reads the primitive learner. -/
  | shared : RateState .shared
  /-- Stored minimum-bounded current rate. -/
  | annealed (rate : Bounded32 annealedRange) : RateState .annealed

instance (policy : RatePolicy) : Provenance (RateState policy) := ⟨some .explorationDuration⟩

/-- Current initial clock state, with no arbitrary schedule parameters. -/
def RateState.initial : (policy : RatePolicy) → RateState policy
  | .perLearner => .perLearner
  | .shared => .shared
  | .annealed => .annealed (Bounded32.project annealedRange ⟨AcornSpec.Constants.epsStartBits⟩)

/-- Advance once per decision, before either the primitive-only or hierarchy path. -/
def RateState.advance {policy : RatePolicy} : RateState policy → RateState policy
  | .perLearner => .perLearner
  | .shared => .shared
  | .annealed rate => .annealed (Bounded32.project annealedRange
      (rate.value.mul ⟨AcornSpec.Constants.epsDecayBits⟩))

/-- Controller rates are resolved lazily under the immutable policy. -/
def RateState.controller {policy : RatePolicy} (state : RateState policy)
    (own primitive : Unit → SwiftTd.ExploreRate) : SwiftTd.ExploreRate :=
  match state with
  | .perLearner => own ()
  | .shared => primitive ()
  | .annealed rate => SwiftTd.ExploreRate.project rate.value

/-- Options have their own fixed epsilon only in the annealed comparison. -/
def RateState.skill {policy : RatePolicy} (state : RateState policy)
    (primitive : Unit → SwiftTd.ExploreRate) : ConsumerRate :=
  match state with
  | .perLearner => .own
  | .shared => .fixed (primitive ())
  | .annealed _ => .fixed (SwiftTd.ExploreRate.project ⟨AcornSpec.Constants.optionEpsilonBits⟩)

/-- The actual schedule write is bounded at storage for all prior legal rates. -/
theorem annealed_write (rate : Bounded32 annealedRange) :
    annealedRange.Contains (Bounded32.project annealedRange
      (rate.value.mul ⟨AcornSpec.Constants.epsDecayBits⟩)).value := Bounded32.legal _

/-- Declared spatial producers match every current spatial assignment. -/
theorem spatial_admitted {config : Features.Config} {dimension : Dimension}
    (tag : Fin Acorn.FeatureConstants.skillCount) (features : SwiftTd.ActiveSet dimension)
    (obs : Host.Observation) :
    (Interest.declared (config := config) .spatialPotentials tag).potential features (spatialPotentials obs) =
      some ((spatialPotentials obs).values.get tag) := by simp [Interest.potential, spatialPotentials]

end Acorn.Handcrafted
