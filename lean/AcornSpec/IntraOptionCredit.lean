/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Collapse

/-!
# intra-option-credit analysis in exact rationals

This module defines the intra-option-credit comparison over explicit paired rows.
The functions below specify its reductions and thresholds; the caller supplies
the observations and their provenance.

Everything statistical is the agent-baseline registered machinery reused
verbatim — `occScore`, `commonPrimary`, `stratifiedScore`, `winCredit`,
`percentile`, `resampleOnce` — with exactly two registered differences:

- the resample stream is domain-separated by the tag
  `Constants.Compatibility.Domain.intraOptionCreditBootstrap.value` at the same base seed;
- the acceptance is the conjunction over **three** paired comparisons —
  final vs `ablated_intra_option` (the primary ablation: the pre-PAR-9
  incumbent), final vs frozen, final vs random — each requiring
  P(improvement) ≥ `poiThreshold` (3/4) and registered lower interval
  bound > `probLowerThreshold` (1/2). The `ablated_span_credit`
  comparison, the pooled Reach successes and the continual-improvement
  lower bound are computed and reported as registered observational
  values with no threshold.

Two further quantities are **derived, not registered**: the paired win
credit of the continual-improvement differences and the Reach `rm − fm`
paired summary against the blind comparator. They apply the registered
per-seed functional to the same rows, were first computed after the run
(post-hoc reporting), and carry no registration status; the report prints them under
their own heading and `ReachReport` says whether the Reach one exists.
-/

namespace AcornSpec

/-- The intra-option-credit bootstrap stream tag (`intra_option_credit::BOOTSTRAP_TAG`). -/
def intraOptionCreditBootstrapDomain : UInt64 := Constants.Compatibility.Domain.intraOptionCreditBootstrap.value

/-- The intra-option-credit registered paired summary: the agent-baseline machinery at the
intra-option-credit resample stream. -/
def intraOptionCreditPairedSummary (diffs : SeedDiffs) : PairedSummary :=
  pairedSummaryAt intraOptionCreditBootstrapDomain diffs

/-- The registered point threshold every thresholded comparison's
probability of improvement must reach (`≥`). derived-exploration-rate keeps it unchanged,
deliberately: choosing a narrower bar after seeing which of intra-option-credit's
conjuncts failed would select the threshold from a known prior outcome. -/
def poiThreshold : Rat := 3/4

/-- The registered threshold every thresholded comparison's lower interval
bound must exceed (strict `>`). -/
def probLowerThreshold : Rat := 1/2

/-- One thresholded comparison's two conjuncts: the point estimate reaches
`poiThreshold` and the registered lower bound exceeds `probLowerThreshold`. -/
def PairedSummary.passes (s : PairedSummary) : Bool :=
  decide (poiThreshold ≤ s.poi) && decide (probLowerThreshold < s.probLower)

/-- Whether the derived Reach report over the population exists. It is the
outcome tally of the `rm − fm` differences and nothing more: no interval of
this comparison is registered or printed, so none is resampled. -/
inductive ReachReport where
  /-- Every seed has a Reach-restricted primary stratum: the tally of the
  `rm − fm` differences, and the point probability it forms. -/
  | complete (tally : Tally)
  /-- The first seed (in population order) whose Reach-restricted primary
  stratum is empty. The derived comparison has no value; the registered
  conjunction is unaffected, because this measure never entered it. -/
  | incomplete (seed : Fin studySeeds)
  deriving Repr

/-- The derived Reach `rm − fm` tally of final against `control`, or the
seed that has none. -/
def reachReport (final control : ArmOccs) : ReachReport :=
  match reachTimeDiffs final control with
  | .ok diffs => .complete (tally diffs.toArray)
  | .error seed => .incomplete seed

/-- The registered intra-option-credit values: three thresholded paired comparisons,
the registered observational measures, and the derived reporting. Every
paired summary carries its outcome tally, from which its `poi` is formed. -/
structure IntraOptionCreditResult where
  /-- Final vs `ablated_intra_option`. -/
  ablation : PairedSummary
  /-- Final vs frozen. -/
  frozen : PairedSummary
  /-- Final vs random. -/
  random : PairedSummary
  /-- Observational — final vs `ablated_span_credit`. -/
  span : PairedSummary
  /-- Observational — pooled Reach successes on the final arm over the
  ablation pairing's Reach-restricted primary stratum. -/
  reachFinal : Nat
  /-- Observational — the ablation arm's pooled Reach successes. -/
  reachAblation : Nat
  /-- Observational — the ablation pairing's Reach stratum size. -/
  reachTotal : Nat
  /-- Final-arm later-cycle minus first-cycle stratified efficiency. The
  registered value is its lower bound, `continual.effectLower`; its paired
  win credit and tally are derived reporting. -/
  continual : PairedSummary
  /-- Derived — Reach stratum vs the blind comparator, `rm − fm`. -/
  reachVsRandom : ReachReport
  deriving Repr

/-- The complete registered intra-option-credit collapse over the five arms. `none`
reproduces the pipeline's hard failure on any empty required stratum. -/
def intraOptionCreditResult (final random frozen ablation span : ArmOccs) :
    Option IntraOptionCreditResult := do
  let vsAblation ← scoreComparison final ablation
  let vsFrozen ← scoreComparison final frozen
  let vsRandom ← scoreComparison final random
  let vsSpan ← scoreComparison final span
  let (reachFinal, reachAblation, reachTotal) := reachPooled final ablation
  let continual ← (continualDiffs final).toOption
  some { ablation := intraOptionCreditPairedSummary vsAblation
         frozen := intraOptionCreditPairedSummary vsFrozen
         random := intraOptionCreditPairedSummary vsRandom
         span := intraOptionCreditPairedSummary vsSpan
         reachFinal, reachAblation, reachTotal
         continual := intraOptionCreditPairedSummary continual
         reachVsRandom := reachReport final random }

/-- The registered intra-option-credit acceptance: the conjunction over the three
thresholded comparisons. -/
def intraOptionCreditAccepts (r : IntraOptionCreditResult) : Bool :=
  r.ablation.passes && r.frozen.passes && r.random.passes

end AcornSpec
