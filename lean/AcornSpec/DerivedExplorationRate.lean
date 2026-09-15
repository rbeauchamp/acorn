/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.IntraOptionCredit

/-!
# derived-exploration-rate analysis in exact rationals

This module defines the derived-exploration-rate comparison over explicit paired rows.
The functions below specify its reductions and thresholds; the caller supplies
the observations and their provenance.

Everything statistical is the agent-baseline registered machinery reused
verbatim — `occScore`, `commonPrimary`, `stratifiedScore`, `winCredit`,
`percentile`, `resampleOnce` — over the shared twin-row collapse
(`TwinRow`, `collapseTwinRows`), which reads exactly the fields the rows
twins carry. There are two registered differences from intra-option-credit:

- the resample stream is domain-separated by the tag
  `Constants.Compatibility.Domain.derivedExplorationRateBootstrap.value` at the same base seed;
- the thresholded conjunction is over final vs `ablated_annealed_schedule`
  (the primary ablation: the incumbent hand-set schedule), final vs frozen
  and final vs random. The `ablated_shared_rate` comparison and the
  continual-improvement lower bound are computed and reported as registered
  observational values with no threshold.

The thresholds are intra-option-credit's (`poiThreshold`, `probLowerThreshold`),
unchanged, for the reason stated there. The derived reporting (continual
win credit, Reach `rm − fm`) has the same status as in intra-option-credit.
-/

namespace AcornSpec

/-- The derived-exploration-rate bootstrap stream tag (`derived_exploration_rate::BOOTSTRAP_TAG`). -/
def derivedExplorationRateBootstrapDomain : UInt64 := Constants.Compatibility.Domain.derivedExplorationRateBootstrap.value

/-- The derived-exploration-rate registered paired summary: the agent-baseline machinery at the
derived-exploration-rate resample stream. -/
def derivedExplorationRatePairedSummary (diffs : SeedDiffs) : PairedSummary :=
  pairedSummaryAt derivedExplorationRateBootstrapDomain diffs

/-- The registered derived-exploration-rate values: three thresholded paired comparisons,
the registered observational measures, and the derived reporting. Every
paired summary carries its outcome tally, from which its `poi` is formed. -/
structure DerivedExplorationRateResult where
  /-- Final vs `ablated_annealed_schedule`. -/
  schedule : PairedSummary
  /-- Final vs frozen. -/
  frozen : PairedSummary
  /-- Final vs random. -/
  random : PairedSummary
  /-- Observational — final vs `ablated_shared_rate`. -/
  shared : PairedSummary
  /-- Final-arm later-cycle minus first-cycle stratified efficiency. The
  registered value is its lower bound, `continual.effectLower`; its paired
  win credit and tally are derived reporting. -/
  continual : PairedSummary
  /-- Derived — Reach stratum vs the blind comparator, `rm − fm`. -/
  reachVsRandom : ReachReport
  deriving Repr

/-- The complete registered derived-exploration-rate collapse over the five arms. `none`
reproduces the pipeline's hard failure on any empty required stratum. -/
def derivedExplorationRateResult (final random frozen schedule shared : ArmOccs) :
    Option DerivedExplorationRateResult := do
  let vsSchedule ← scoreComparison final schedule
  let vsFrozen ← scoreComparison final frozen
  let vsRandom ← scoreComparison final random
  let vsShared ← scoreComparison final shared
  let continual ← (continualDiffs final).toOption
  some { schedule := derivedExplorationRatePairedSummary vsSchedule
         frozen := derivedExplorationRatePairedSummary vsFrozen
         random := derivedExplorationRatePairedSummary vsRandom
         shared := derivedExplorationRatePairedSummary vsShared
         continual := derivedExplorationRatePairedSummary continual
         reachVsRandom := reachReport final random }

/-- The registered derived-exploration-rate acceptance: the conjunction over the three
thresholded comparisons. -/
def derivedExplorationRateAccepts (r : DerivedExplorationRateResult) : Bool :=
  r.schedule.passes && r.frozen.passes && r.random.passes

end AcornSpec
