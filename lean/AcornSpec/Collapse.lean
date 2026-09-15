/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.StudySchema

/-!
# Agent-baseline analysis in exact rationals

This functional computes over explicit paired inputs:

- occurrences collapse to capped cumulative first-success times
  (`elapsed = min(cap, Σ steps)`), failure scores exactly zero;
- comparison-local union exclusion (a paired occurrence is primary only when
  it is non-survival and neither arm satisfied it on first observation);
- equal goal occurrences within a family, then equal nonempty families;
- probability of improvement = mean win credit (tie = ½) over the 30 paired
  seeds. Each paired difference is classified once into the closed
  `Outcome` (win, tie, loss); the population's `Tally` of those outcomes is
  the record, and the point probability is `(wins + ties/2) / seeds` **by
  definition** (`Tally.poi`), so the published decomposition and the
  published rational are one value. `AcornVerif.tally_poi_eq_mean_credit`
  is the identity between that definition and the mean of per-seed credits;
- the registered interval = linearly interpolated percentiles at 1/40 and
  39/40 over 10,000 paired-seed resamples, drawing
  resample indices from the repository's own xoshiro256** seeded
  from the generated `bootstrapSeed` and sealed `bootstrapDomain` (one fresh
  generator per paired summary), with every
  statistic computed in exact ℚ;
- Reach success pooled over the Reach-restricted primary stratum; Reach
  capped times use the cap-plus-one failure time; per-seed medians;
- continual improvement compares later-cycle stratified efficiency with the
  first cycle over goals never initially satisfied in any cycle.

The population is fixed by type. An arm is exactly `studySeeds` shards of
exactly `occurrenceCount` occurrences each (`ArmOccs`), every occurrence is
addressed by a `Fin` key, and every paired statistic takes two `ArmOccs` —
so a truncated, padded or misaligned population cannot reach a paired
comparison at all. Raw rows are validated once, at the IO boundary
(`AcornSpec.Rows`), and nothing after it indexes with a default.

A `none` result is a hard failure on an empty required stratum: the registered
computation has no value there, and no
acceptance can hold. Seedwise statistics say *which* seed had no value
(`Except (Fin studySeeds) _`) so a derived report can name it.

Sums and means over exact rationals do not depend on accumulation order.
Resampling consumes the fixed seed order, and occurrence collapse consumes
canonical attempt order; those are separate, order-sensitive inputs.
-/

namespace AcornSpec

/-- `agent_baseline::STEPS_PER_GOAL` — the cumulative occurrence cap. -/
def occurrenceCap : Nat := 12000
/-- `agent_baseline::REACH_FAILURE_TIME` — cap plus one. -/
def reachFailureTime : Nat := 12001
/-- `agent_baseline::BOOTSTRAP_SAMPLES`. -/
def bootstrapSamples : Nat := 10000
/-- `agent_baseline::BOOTSTRAP_SEED` (generated). -/
def bootstrapSeed : UInt64 := Constants.bootstrapSeedValue
/-- The registered numeric domain, generated from the preserved historical bytes. -/
def bootstrapDomain : UInt64 := Constants.Compatibility.Domain.agentBaselineBootstrap.value
/-- `agent_baseline::SEED_COUNT` — the registered paired population. Every study
draws exactly this many held-out seeds, one shard per arm each. -/
def studySeeds : Nat := 30

/-- Goal occurrences per shard: one per `(cycle, goal)`. -/
abbrev occurrenceCount : Nat := studyCycles * studyGoals

/-- The occurrence index of `(cycle, goal)`, in `(cycle, goal)` order. Both
coordinates are bounded by their types, so the key always exists. -/
def occKey (cycle : Fin studyCycles) (goal : Fin studyGoals) : Fin occurrenceCount :=
  ⟨cycle.val * studyGoals + goal.val, by
    have hc := cycle.isLt
    have hg := goal.isLt
    simp only [occurrenceCount, studyCycles, studyGoals] at hc hg ⊢
    omega⟩

/-- `n` as an index below `bound`, when it is one. -/
def boundedIndex? (n bound : Nat) : Option (Fin bound) :=
  if h : n < bound then some ⟨n, h⟩ else none

/-- One collapsed goal occurrence. -/
structure Occ where
  /-- Goal family. -/
  family : Family
  /-- Cumulative capped steps through first success (the cap for failures). -/
  elapsed : Nat
  /-- Whether any attempt achieved the goal. -/
  achieved : Bool
  /-- Whether the goal was satisfied on the occurrence's first observation. -/
  initiallySatisfied : Bool
  deriving Repr, Inhabited

/-- One shard collapsed: exactly one occurrence per key. -/
abbrev ShardOccs := Vector Occ occurrenceCount
/-- One arm over the registered population: exactly one shard per seed. -/
abbrev ArmOccs := Vector ShardOccs studySeeds
/-- One per-seed paired statistic over the population. -/
abbrev SeedDiffs := Vector Rat studySeeds

/-- One attempt row reduced to exactly the fields the registered statistics
read — the rows-twin line format `intra_option_credit`/`derived_exploration_rate` write — with every
coordinate bounded by its type. A row outside the protocol's
`cycle × goal × attempt` grid is unrepresentable, so the occurrence a row
names always exists. -/
structure TwinRow where
  /-- Curriculum cycle. -/
  cycle : Fin studyCycles
  /-- Goal index within the cycle. -/
  goalIndex : Fin studyGoals
  /-- Goal family. -/
  family : Family
  /-- Attempt index within the occurrence. -/
  attempt : Fin attemptsPerGoal
  /-- Whether the goal was satisfied on the occurrence's first observation. -/
  initiallySatisfied : Bool
  /-- Environment steps consumed by this attempt. -/
  steps : Nat
  /-- Whether this attempt achieved the goal. -/
  achieved : Bool
  deriving Repr

/-- The occurrence a row belongs to. -/
def TwinRow.key (r : TwinRow) : Fin occurrenceCount := occKey r.cycle r.goalIndex

/-- A `agent_baseline::AttemptRow` as a twin row; `none` when a coordinate lies
outside the protocol grid. -/
def Row.twin? (r : Row) : Option TwinRow := do
  let cycle ← boundedIndex? r.cycle.toNat studyCycles
  let goalIndex ← boundedIndex? r.goalIndex studyGoals
  let attempt ← boundedIndex? r.attempt attemptsPerGoal
  pure { cycle, goalIndex, family := r.family, attempt
         initiallySatisfied := r.initiallySatisfied, steps := r.steps.toNat
         achieved := r.achieved }

/-- Collapse one shard's attempt rows into its goal occurrences. Attempt 0
opens an occurrence; later attempts accumulate capped elapsed time until
the first achieving attempt. The one fold behind every study's collapse. -/
def collapseTwinRows (rows : Array TwinRow) : ShardOccs :=
  let empty : Occ := ⟨.reach, 0, false, false⟩
  rows.foldl (init := Vector.replicate occurrenceCount empty) fun occs row =>
    let key := row.key
    let occ := occs[key]
    let occ :=
      if row.attempt.val == 0 then
        { family := row.family, elapsed := 0, achieved := false
          initiallySatisfied := row.initiallySatisfied }
      else occ
    let occ :=
      if occ.achieved then occ
      else
        let elapsed := min occurrenceCap (occ.elapsed + row.steps)
        { occ with elapsed, achieved := row.achieved }
    occs.set key.val occ key.isLt

/-- `collapseTwinRows` over `agent_baseline::AttemptRow`s; `none` if any row names a
coordinate outside the protocol grid. -/
def collapseOccurrences (rows : Array Row) : Option ShardOccs :=
  (rows.mapM Row.twin?).map collapseTwinRows

/-- The primary capped efficiency score of one occurrence. -/
def occScore (o : Occ) : Rat :=
  1 - ((if o.achieved then o.elapsed else occurrenceCap : Nat) : Rat) / (occurrenceCap : Rat)

/-- The Reach time-to-goal metric of one occurrence (cap-plus-one failure). -/
def occReachTime (o : Occ) : Rat :=
  ((if o.achieved then o.elapsed else reachFailureTime : Nat) : Rat)

/-- Comparison-local union exclusion: the primary occurrence keys of a
paired comparison. -/
def commonPrimary (left right : ShardOccs) : Array (Fin occurrenceCount) :=
  (Array.finRange occurrenceCount).filter fun k =>
    left[k].family != Family.survive &&
      !left[k].initiallySatisfied && !right[k].initiallySatisfied

/-- The Reach-restricted primary keys of a pairing. -/
def reachPrimary (left right : ShardOccs) : Array (Fin occurrenceCount) :=
  (commonPrimary left right).filter fun k => left[k].family == Family.reach

/-- Mean of a rational list; `none` on empty (the Python pipeline raises). -/
def ratMean (values : Array Rat) : Option Rat :=
  if values.isEmpty then none
  else some (values.foldl (· + ·) 0 / (values.size : Rat))

/-- Equal-family stratified score over the selected occurrence keys:
average within each nonempty family, then average the family means.
`none` when no family is nonempty. -/
def stratifiedScore (occs : ShardOccs) (keys : Array (Fin occurrenceCount)) : Option Rat :=
  let sumCount (fam : Family) : Rat × Nat :=
    keys.foldl (init := ((0 : Rat), 0)) fun (s, n) k =>
      if occs[k].family == fam then (s + occScore occs[k], n + 1) else (s, n)
  let fams := [Family.reach, Family.collect, Family.craft, Family.survive]
  let means := fams.foldl (init := #[]) fun acc fam =>
    let (s, n) := sumCount fam
    if n == 0 then acc else acc.push (s / (n : Rat))
  ratMean means

/-- The closed outcome of one paired difference, final minus control. -/
inductive Outcome where
  /-- The final arm's statistic strictly exceeded the control's. -/
  | win
  /-- The two statistics were equal. -/
  | tie
  /-- The control's statistic strictly exceeded the final arm's. -/
  | loss
  deriving DecidableEq, Repr

/-- Classify one paired difference. Every difference is exactly one
outcome, so a seed cannot be counted twice or not at all. -/
def Outcome.ofDiff (d : Rat) : Outcome :=
  if 0 < d then .win else if d == 0 then .tie else .loss

/-- Win credit of an outcome: 1 for a win, ½ for a tie, 0 for a loss. -/
def Outcome.credit : Outcome → Rat
  | .win => 1
  | .tie => 1/2
  | .loss => 0

/-- Win credit of one paired difference — the credit of its outcome.
The point probability of improvement is the mean of these credits over the
population; `Tally.poi` forms the same value from the outcome counts, and
`AcornVerif.tally_poi_eq_mean_credit` is the identity between the two. The
bootstrap resamples credits directly (`resampleOnce`). -/
def winCredit (d : Rat) : Rat := (Outcome.ofDiff d).credit

/-- The outcome counts of a population. The three counts are the whole
per-seed record of a paired comparison; the point probability of
improvement is a function of them, not a separate measurement, so a
report cannot publish the rational in one unit and the counts in another. -/
structure Tally where
  /-- Seeds on which the final arm's statistic strictly exceeded the control's. -/
  wins : Nat
  /-- Seeds on which the two statistics were equal. -/
  ties : Nat
  /-- Seeds on which the control's statistic strictly exceeded the final arm's. -/
  losses : Nat
  deriving Repr, DecidableEq

/-- No outcomes recorded. -/
def Tally.zero : Tally := ⟨0, 0, 0⟩

/-- Record one outcome: exactly one count grows, by one. -/
def Tally.record (t : Tally) : Outcome → Tally
  | .win => { t with wins := t.wins + 1 }
  | .tie => { t with ties := t.ties + 1 }
  | .loss => { t with losses := t.losses + 1 }

/-- Seeds recorded. -/
def Tally.seeds (t : Tally) : Nat := t.wins + t.ties + t.losses

/-- Point probability of improvement: `(wins + ties/2) / seeds`, by
definition. -/
def Tally.poi (t : Tally) : Rat :=
  ((t.wins : Rat) + (t.ties : Rat) / 2) / (t.seeds : Rat)

/-- The outcome tally of a population of paired differences: one
classification per difference, folded into the counts. -/
def tally (diffs : Array Rat) : Tally :=
  diffs.foldl (fun t d => t.record (Outcome.ofDiff d)) Tally.zero

/-- One fold over `winCredit`: the point probability of improvement and its
win/tie/loss decomposition. `none` on empty (the registered hard failure). -/
def poiFromDiffs (diffs : Array Rat) : Option (Rat × Nat × Nat × Nat) :=
  if diffs.isEmpty then none
  else
    let (sum, wins, ties, losses) :=
      diffs.foldl (init := ((0 : Rat), 0, 0, 0)) fun (s, w, t, l) d =>
        let c := winCredit d
        if 0 < d then (s + c, w + 1, t, l)
        else if d == 0 then (s + c, w, t + 1, l)
        else (s + c, w, t, l + 1)
    some (sum / (diffs.size : Rat), wins, ties, losses)

/-- Median of a rational list (`none` on empty): sort, take the middle, or
the mean of the two middles. -/
def ratMedian (values : Array Rat) : Option Rat :=
  if values.isEmpty then none
  else
    let sorted := values.qsort (· < ·)
    let n := sorted.size
    if n % 2 == 1 then some sorted[n / 2]!
    else some ((sorted[n / 2 - 1]! + sorted[n / 2]!) / 2)

/-- Linearly interpolated percentile over a nonempty sample, exactly the
registered `probability · (n − 1)` position rule, in ℚ. -/
def percentile (values : Array Rat) (probability : Rat) : Rat :=
  let sorted := values.qsort (· < ·)
  let position := probability * ((sorted.size - 1 : Nat) : Rat)
  let lower := position.floor.toNat
  let upper := position.ceil.toNat
  if lower == upper then sorted[lower]!
  else
    let weight := position - (lower : Rat)
    sorted[lower]! * (1 - weight) + sorted[upper]! * weight

/-- One paired summary's acceptance-relevant values. -/
structure PairedSummary where
  /-- Per-seed outcomes over the fixed seeds; `poi` is derived from them. -/
  tally : Tally
  /-- Registered lower interval bound of the resampled win probability. -/
  probLower : Rat
  /-- Registered lower interval bound of the resampled mean difference. -/
  effectLower : Rat
  deriving Repr

/-- Point probability of improvement over the fixed seeds. -/
def PairedSummary.poi (s : PairedSummary) : Rat := s.tally.poi

/-- One bootstrap resample: `n` index draws, the resampled mean difference
and the resampled mean win credit. -/
def resampleOnce (diffs : Array Rat) (rng : Xoshiro256) :
    Rat × Rat × Xoshiro256 :=
  let n := diffs.size
  let rec
    go (rng : Xoshiro256) (sumD sumW : Rat) : Nat → Rat × Rat × Xoshiro256
      | 0 => (sumD / (n : Rat), sumW / (n : Rat), rng)
      | fuel + 1 =>
        let (idx, rng) := rng.nextBelow n.toUInt64
        let d := diffs[idx.toNat]!
        go rng (sumD + d) (sumW + winCredit d) fuel
  go rng 0 0 n

/-- The registered paired summary over the seed differences: the outcome
tally (and so the point probability of improvement), plus the two
registered lower interval bounds from 10,000 resamples drawn from a fresh
generator at `domain`. Agent-baseline uses `bootstrapDomain`; each later
study has its own generated historical domain at the same base seed. Total: the
population is nonempty by type. -/
def pairedSummaryAt (domain : UInt64) (diffs : SeedDiffs) : PairedSummary :=
  let diffs := diffs.toArray
  let rng := Xoshiro256.new (Xoshiro256.streamKey bootstrapSeed domain)
  let rec
    /-- Accumulate the effect and probability resamples. -/
    go (rng : Xoshiro256) (effects probs : Array Rat) : Nat → Array Rat × Array Rat
      | 0 => (effects, probs)
      | fuel + 1 =>
        let (eff, prob, rng) := resampleOnce diffs rng
        go rng (effects.push eff) (probs.push prob) fuel
  let resamples := go rng (Array.emptyWithCapacity bootstrapSamples)
    (Array.emptyWithCapacity bootstrapSamples) bootstrapSamples
  { tally := tally diffs
    probLower := percentile resamples.2 (1/40)
    effectLower := percentile resamples.1 (1/40) }

/-- The agent-baseline registered paired summary: `pairedSummaryAt` at
`bootstrapDomain`. -/
def pairedSummary (diffs : SeedDiffs) : PairedSummary :=
  pairedSummaryAt bootstrapDomain diffs

/-- One per-seed statistic over the population, or the first seed (in
population order) at which it has no value. -/
def seedwise {α : Type} (f : α → Option Rat) (arm : Vector α studySeeds) :
    Except (Fin studySeeds) SeedDiffs :=
  (Vector.finRange studySeeds).mapM fun s =>
    match f arm[s] with
    | some d => .ok d
    | none => .error s

/-- One paired statistic, final versus control, seed by seed. The two arms
are the same population by type. -/
def pairSeeds (f : ShardOccs → ShardOccs → Option Rat) (final control : ArmOccs) :
    Except (Fin studySeeds) SeedDiffs :=
  seedwise (fun p => f p.1 p.2) (Vector.zip final control)

/-- One seed's primary score difference, final minus control, over the
comparison-local primary stratum. -/
def scoreDiff (final control : ShardOccs) : Option Rat := do
  let keys := commonPrimary final control
  let fs ← stratifiedScore final keys
  let cs ← stratifiedScore control keys
  pure (fs - cs)

/-- One score-based paired comparison (final versus one control) over the
population; `none` if any seed's primary stratum is empty. -/
def scoreComparison (final control : ArmOccs) : Option SeedDiffs :=
  (pairSeeds scoreDiff final control).toOption

/-- One seed's Reach-stratum difference: control median capped time minus
final median capped time over the Reach-restricted primary keys. The
polarity is `rm − fm` (a positive difference is a win for the final arm:
it reached faster). `none` when the stratum is empty. -/
def reachTimeDiff (final control : ShardOccs) : Option Rat := do
  let keys := reachPrimary final control
  let fm ← ratMedian (keys.map fun k => occReachTime final[k])
  let cm ← ratMedian (keys.map fun k => occReachTime control[k])
  pure (cm - fm)

/-- Per-seed Reach-stratum differences over the population, or the first
seed whose Reach-restricted primary stratum is empty. -/
def reachTimeDiffs (final control : ArmOccs) : Except (Fin studySeeds) SeedDiffs :=
  pairSeeds reachTimeDiff final control

/-- Pooled Reach successes over one pairing's Reach-restricted primary
stratum: `(final successes, control successes, stratum size)`. -/
def reachPooled (final control : ArmOccs) : Nat × Nat × Nat :=
  (Vector.zipWith (fun f c =>
      let keys := reachPrimary f c
      ((keys.filter fun k => f[k].achieved).size,
       (keys.filter fun k => c[k].achieved).size,
       keys.size))
    final control).foldl
    (fun (f, c, t) (f', c', t') => (f + f', c + c', t + t')) (0, 0, 0)

/-- One seed's later-minus-first-cycle stratified efficiency on one arm —
the continual-improvement measure. Its eligible goals are the non-Survive
ones no cycle of that seed found already satisfied. -/
def continualDiff (arm : ShardOccs) : Option Rat := do
  let firstCycle : Fin studyCycles := ⟨0, by decide⟩
  let eligible := (Array.finRange studyGoals).filter fun g =>
    arm[occKey firstCycle g].family != Family.survive &&
      ((Array.finRange studyCycles).all fun c => !arm[occKey c g].initiallySatisfied)
  let firstKeys := eligible.map (occKey firstCycle)
  let laterKeys := (Array.finRange (studyCycles - 1)).flatMap fun c =>
    eligible.map fun g => occKey ⟨c.val + 1, by have := c.isLt; omega⟩ g
  let first ← stratifiedScore arm firstKeys
  let later ← stratifiedScore arm laterKeys
  pure (later - first)

/-- The continual-improvement differences over the population, or the
first seed at which a cycle's eligible stratum is empty. -/
def continualDiffs (arm : ArmOccs) : Except (Fin studySeeds) SeedDiffs :=
  seedwise continualDiff arm

/-- The seven acceptance values of the registered computation, in exact
rationals — the value `AcornVerif.StudyResult` is instantiated with. -/
structure Result7 where
  /-- Final-vs-random probability of improvement. -/
  randomPoi : Rat
  /-- Final-vs-random registered probability lower bound. -/
  randomProbLower : Rat
  /-- Final-vs-frozen probability of improvement. -/
  frozenPoi : Rat
  /-- Final-vs-frozen registered probability lower bound. -/
  frozenProbLower : Rat
  /-- Pooled held-out Reach success rate. -/
  reachSuccess : Rat
  /-- Registered lower bound of (random − final) capped Reach time. -/
  reachTimeLower : Rat
  /-- Registered lower bound of later-cycle minus first-cycle efficiency. -/
  continualLower : Rat
  deriving Repr, DecidableEq

/-- One arm's shards as the registered population; `none` unless there are
exactly `studySeeds` shards of well-formed rows. -/
def population (shards : Array Shard) : Option ArmOccs := do
  let occs ← shards.mapM fun sh => collapseOccurrences sh.rows
  if h : occs.size = studySeeds then some ⟨occs, h⟩ else none

/-- The complete registered collapse: the 30 final/random/frozen occurrence
sets to the seven acceptance values. `none` reproduces the pipeline's hard
failure on any empty required stratum. -/
def collapseResult (finalShards randomShards frozenShards : Array Shard) :
    Option Result7 := do
  let finalOccs ← population finalShards
  let randomOccs ← population randomShards
  let frozenOccs ← population frozenShards
  -- Final versus random, final versus frozen.
  let vsRandom ← scoreComparison finalOccs randomOccs
  let vsFrozen ← scoreComparison finalOccs frozenOccs
  let sRandom := pairedSummary vsRandom
  let sFrozen := pairedSummary vsFrozen
  -- Reach: pooled success and per-seed median capped-time differences.
  let reachDiffs ← (reachTimeDiffs finalOccs randomOccs).toOption
  let (successes, _, total) := reachPooled finalOccs randomOccs
  if total == 0 then none
  else
    let sReach := pairedSummary reachDiffs
    -- Continual improvement on the final arm.
    let continual ← (continualDiffs finalOccs).toOption
    let sContinual := pairedSummary continual
    some { randomPoi := sRandom.poi, randomProbLower := sRandom.probLower
           frozenPoi := sFrozen.poi, frozenProbLower := sFrozen.probLower
           reachSuccess := (successes : Rat) / (total : Rat)
           reachTimeLower := sReach.effectLower
           continualLower := sContinual.effectLower }

end AcornSpec
