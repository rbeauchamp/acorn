/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.IntraOptionCredit

/-!
# stomp-planning analysis in exact rationals

This module defines the stomp-planning comparison over explicit paired rows.
The functions below specify its reductions and thresholds; the caller supplies
the observations and their provenance.

Everything statistical is the agent-baseline registered machinery reused
verbatim — `occScore`, `commonPrimary`, `stratifiedScore`, `winCredit`,
`percentile`, `resampleOnce` — over the shared twin-row collapse
(`TwinRow`, `collapseTwinRows`), which reads exactly the fields the rows
twins carry. There are two registered differences from derived-exploration-rate:

- the resample stream is domain-separated by the tag
  `Constants.Compatibility.Domain.stompPlanningBootstrap.value` at the same base seed;
- the thresholded conjunction is over final vs
  `ablated_hand_authored_subtasks` (the primary ablation: the incumbent
  hand-authored spatial regions),
  final vs frozen and final vs random. The `ablated_temporal_abstraction`
  comparison and the continual-improvement lower bound are computed and
  reported as registered observational values with no threshold.

The thresholds are intra-option-credit's (`poiThreshold`, `probLowerThreshold`),
unchanged, for the reason stated there. The derived reporting (continual
win credit, Reach `rm − fm`) has the same status as in intra-option-credit.
-/

namespace AcornSpec

/-- The stomp-planning bootstrap stream tag (`stomp_planning::BOOTSTRAP_TAG`). -/
def stompPlanningBootstrapDomain : UInt64 := Constants.Compatibility.Domain.stompPlanningBootstrap.value

/-- The stomp-planning registered paired summary: the agent-baseline machinery at the
stomp-planning resample stream. -/
def stompPlanningPairedSummary (diffs : SeedDiffs) : PairedSummary :=
  pairedSummaryAt stompPlanningBootstrapDomain diffs

/-- The registered stomp-planning values: three thresholded paired comparisons,
the registered observational measures, and the derived reporting. Every
paired summary carries its outcome tally, from which its `poi` is formed. -/
structure StompPlanningResult where
  /-- Final vs `ablated_hand_authored_subtasks`. -/
  subtasks : PairedSummary
  /-- Final vs frozen. -/
  frozen : PairedSummary
  /-- Final vs random. -/
  random : PairedSummary
  /-- Observational — final vs `ablated_temporal_abstraction`. -/
  temporal : PairedSummary
  /-- Final-arm later-cycle minus first-cycle stratified efficiency. The
  registered value is its lower bound, `continual.effectLower`; its paired
  win credit and tally are derived reporting. -/
  continual : PairedSummary
  /-- Derived — Reach stratum vs the blind comparator, `rm − fm`. -/
  reachVsRandom : ReachReport
  deriving Repr

/-- The complete registered stomp-planning collapse over the five arms. `none`
reproduces the pipeline's hard failure on any empty required stratum. -/
def stompPlanningResult (final random frozen subtasks temporal : ArmOccs) :
    Option StompPlanningResult := do
  let vsSubtasks ← scoreComparison final subtasks
  let vsFrozen ← scoreComparison final frozen
  let vsRandom ← scoreComparison final random
  let vsTemporal ← scoreComparison final temporal
  let continual ← (continualDiffs final).toOption
  some { subtasks := stompPlanningPairedSummary vsSubtasks
         frozen := stompPlanningPairedSummary vsFrozen
         random := stompPlanningPairedSummary vsRandom
         temporal := stompPlanningPairedSummary vsTemporal
         continual := stompPlanningPairedSummary continual
         reachVsRandom := reachReport final random }

/-- The registered stomp-planning acceptance: the conjunction over the three
thresholded comparisons. -/
def stompPlanningAccepts (r : StompPlanningResult) : Bool :=
  r.subtasks.passes && r.frozen.passes && r.random.passes

end AcornSpec
