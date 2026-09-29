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

D2 is the raw spatial indicator. D6 supplies the declared exploration rate and
the annealed comparison's schedule; the persistent-duration law is D3 in
`Acorn.Exploration`. Ranked targets and PAR-10 per-consumer rates reuse their
learned owners. These declarations select the recorded research profiles.

Dabney, Ostrovski & Barreto, *Temporally-Extended ε-Greedy Exploration*, ICLR
(2021), arXiv:2006.01782v1, §4.2, PDF p. 5, describes εz-greedy by "two
parameters, ϵ dictating when/how often to explore, and z dictating the degree
of persistence". D6's ε = 0.01 is the paper's linear Sarsa(λ) CartPole setting
(Appendix A, PDF p. 14) and the constant its Atari training schedule keeps
after decay (Appendix B.3, PDF p. 15). A continuing, clock-free agent keeps
only the constant.
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

/-- D6's rate: the binary32 word nearest 0.01, admitted without projection. -/
def declaredRate : SwiftTd.ExploreRate := ⟨⟨Acorn.Constants.exploreRate1e2Bits⟩, by decide⟩

/-- The schedule stores its actual closed interval, including the minimum. -/
def annealedRange : Interval32 :=
  ⟨⟨Acorn.Constants.epsMinBits⟩, .one, by decide, by decide, by decide⟩

/-- Schedule state exists only in the schedule-carrying rate policy. -/
inductive RateState : RatePolicy → Type where
  /-- Every consumer reads the declared rate; there is no schedule state. -/
  | declared : RateState .declared
  /-- Each consumer reads its own learner. -/
  | perLearner : RateState .perLearner
  /-- Every consumer reads the primitive learner. -/
  | shared : RateState .shared
  /-- Stored minimum-bounded current rate. -/
  | annealed (rate : Bounded32 annealedRange) : RateState .annealed

instance (policy : RatePolicy) : Provenance (RateState policy) := ⟨some .explorationRate⟩

/-- Current initial clock state, with no arbitrary schedule parameters. -/
def RateState.initial : (policy : RatePolicy) → RateState policy
  | .declared => .declared
  | .perLearner => .perLearner
  | .shared => .shared
  | .annealed => .annealed (Bounded32.project annealedRange ⟨Acorn.Constants.epsStartBits⟩)

/-- Advance once per decision, before either the primitive-only or hierarchy path. -/
def RateState.advance {policy : RatePolicy} : RateState policy → RateState policy
  | .declared => .declared
  | .perLearner => .perLearner
  | .shared => .shared
  | .annealed rate => .annealed (Bounded32.project annealedRange
      (rate.value.mul ⟨Acorn.Constants.epsDecayBits⟩))

/-- Controller rates are resolved lazily under the immutable policy. -/
def RateState.controller {policy : RatePolicy} (state : RateState policy)
    (own primitive : Unit → SwiftTd.ExploreRate) : SwiftTd.ExploreRate :=
  match state with
  | .declared => declaredRate
  | .perLearner => own ()
  | .shared => primitive ()
  | .annealed rate => SwiftTd.ExploreRate.project rate.value

/-- Options read the declared rate, their own learner, the shared primitive
rate, or the annealed comparison's fixed option epsilon. -/
def RateState.skill {policy : RatePolicy} (state : RateState policy)
    (primitive : Unit → SwiftTd.ExploreRate) : ConsumerRate :=
  match state with
  | .declared => .fixed declaredRate
  | .perLearner => .own
  | .shared => .fixed (primitive ())
  | .annealed _ => .fixed (SwiftTd.ExploreRate.project ⟨Acorn.Constants.optionEpsilonBits⟩)

/-- Under the declared policy every controller read is the declared word, for
every rate state and whatever the learners would derive. -/
theorem RateState.declared_controller {policy : RatePolicy} (state : RateState policy)
    (declared : policy = .declared) (own primitive : Unit → SwiftTd.ExploreRate) :
    state.controller own primitive = declaredRate := by
  cases state <;> first | rfl | cases declared

/-- Under the declared policy every option receives the declared word as a fixed rate. -/
theorem RateState.declared_skill {policy : RatePolicy} (state : RateState policy)
    (declared : policy = .declared) (primitive : Unit → SwiftTd.ExploreRate) :
    state.skill primitive = .fixed declaredRate := by
  cases state <;> first | rfl | cases declared

/-- The actual schedule write is bounded at storage for all prior legal rates. -/
theorem annealed_write (rate : Bounded32 annealedRange) :
    annealedRange.Contains (Bounded32.project annealedRange
      (rate.value.mul ⟨Acorn.Constants.epsDecayBits⟩)).value := Bounded32.legal _

/-- Declared spatial producers match every current spatial assignment. -/
theorem spatial_admitted {config : Features.Config} {dimension : Dimension}
    (tag : Fin Acorn.FeatureConstants.skillCount) (features : SwiftTd.ActiveSet dimension)
    (obs : Host.Observation) :
    (Interest.declared (config := config) .spatialPotentials tag).potential features (spatialPotentials obs) =
      some ((spatialPotentials obs).values.get tag) := by simp [Interest.potential, spatialPotentials]

end Acorn.Handcrafted
