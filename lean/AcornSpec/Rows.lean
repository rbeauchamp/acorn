/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.DerivedExplorationRate
import AcornSpec.StompPlanning
import Lean.Data.Json

/-!
# Rows-twin reader and report renderer (untrusted tooling)

The intra-option-credit, derived-exploration-rate and stomp-planning analyses
read the same rows-twin format (`shard`/`row` lines) and original configuration
manifest shape, and print the same report shape. Their runners share this
reader and renderer. Nothing here establishes registration timing:
the registered definitions are `AcornSpec.intraOptionCreditResult`,
`AcornSpec.derivedExplorationRateResult` and `AcornSpec.stompPlanningResult`.
This module only moves bytes into and out of them.

The reader is the IO boundary of the registered population. It validates
raw text once into the fixed-cardinality types the functional is defined
over, refusing anything it cannot bind: a manifest that does not describe
the registered population shape, an arm the manifest does not register, a
shard header that names another shard, a coordinate outside the protocol
grid, and any occurrence whose rows are not one canonical attempt sequence.
The original configuration manifest contains no row hashes, and a row carries
no seed. This reader binds shape and index; the caller must establish content
identity and provenance separately.

The renderer produces every comparison's complete block from its key and
its `PairedSummary`, so a report cannot omit a line or label one with the
wrong key while still typechecking.
-/

namespace AcornSpec.Rows

open AcornSpec

/-! ## The manifest -/

/-- The population shape an original configuration manifest records. Its provenance fields
(`commit`, `audit_digest`, `held_out_seeds`) name the run; nothing in a rows
twin can be checked against them. The reader binds shape and index; content
identity is a separate caller obligation. -/
structure Manifest where
  /-- `seed_count`. -/
  seedCount : Nat
  /-- The number of `held_out_seeds` listed. -/
  heldOutSeeds : Nat
  /-- `cycles`. -/
  cycles : Nat
  /-- `goals`. -/
  goals : Nat
  /-- `attempts_per_goal`. -/
  attemptsPerGoal : Nat
  /-- `steps_per_attempt`. -/
  stepsPerAttempt : Nat
  /-- The registered arms. -/
  arms : Array String
  deriving Repr

/-- Parse the manifest fields the reader binds the rows to. -/
def parseManifest (text : String) : Except String Manifest := do
  let json ← Lean.Json.parse text
  let field (key : String) : Except String Lean.Json := json.getObjVal? key
  let nat (key : String) : Except String Nat := do (← field key).getNat?
  let arms ← (← (← field "arms").getArr?).mapM (·.getStr?)
  let heldOut ← (← field "held_out_seeds").getArr?
  pure { seedCount := ← nat "seed_count", heldOutSeeds := heldOut.size
         cycles := ← nat "cycles", goals := ← nat "goals"
         attemptsPerGoal := ← nat "attempts_per_goal"
         stepsPerAttempt := ← nat "steps_per_attempt", arms }

/-- Refuse a manifest that does not describe the population the registered
functional is defined over. Each mismatch names the field and both values. -/
def Manifest.bindsPopulation (m : Manifest) : Except String Unit := do
  let expect (field : String) (recorded registered : Nat) : Except String Unit :=
    if recorded == registered then pure ()
    else throw s!"{field} is {recorded}; the registered population has {registered}"
  expect "seed_count" m.seedCount studySeeds
  expect "held_out_seeds" m.heldOutSeeds studySeeds
  expect "cycles" m.cycles studyCycles
  expect "goals" m.goals studyGoals
  expect "attempts_per_goal" m.attemptsPerGoal AcornSpec.attemptsPerGoal
  expect "steps_per_attempt" m.stepsPerAttempt AcornSpec.stepsPerAttempt.toNat

/-- Read and bind the explicitly supplied original run manifest. -/
def readManifest (path : String) : IO Manifest := do
  let text ← IO.FS.readFile path
  match parseManifest text >>= fun m => m.bindsPopulation *> pure m with
  | .ok m => pure m
  | .error e => throw (IO.userError s!"{path}: {e}")

/-! ## Rows -/

/-- `n` as an index below `bound`, or why it is not one. -/
def bounded (label : String) (n bound : Nat) : Except String (Fin bound) :=
  match boundedIndex? n bound with
  | some i => pure i
  | none => throw s!"{label} {n} is outside 0..{bound}"

/-- A decimal field. -/
def natField (label : String) (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw s!"{label} {s} is not a number"

/-- A `0`/`1` field. -/
def flagField (label : String) (s : String) : Except String Bool :=
  match s with
  | "0" => pure false
  | "1" => pure true
  | other => throw s!"{label} {other} is not 0 or 1"

/-- Parse one rows-twin `row` line's fields into a bounded row. -/
def parseRow (fields : List String) : Except String TwinRow :=
  match fields with
  | [cycle, goalIndex, family, attempt, init, steps, achieved] => do
    let cycle ← bounded "cycle" (← natField "cycle" cycle) studyCycles
    let goalIndex ← bounded "goal" (← natField "goal" goalIndex) studyGoals
    let family ←
      match family with
      | "reach" => pure Family.reach
      | "collect" => pure Family.collect
      | "craft" => pure Family.craft
      | "survive" => pure Family.survive
      | other => throw s!"family {other} is not a goal family"
    let attempt ← bounded "attempt" (← natField "attempt" attempt) attemptsPerGoal
    let initiallySatisfied ← flagField "initially_satisfied" init
    let steps ← natField "steps" steps
    if stepsPerAttempt.toNat < steps then
      throw s!"steps {steps} exceeds the attempt cap {stepsPerAttempt}"
    let achieved ← flagField "achieved" achieved
    pure { cycle, goalIndex, family, attempt, initiallySatisfied, steps, achieved }
  | _ => throw s!"expected 7 row fields, found {fields.length}"

/-- The canonical attempt sequence of one occurrence, as the study loop
writes it: attempts `0, 1, …` in file order, the same family and initial
status on every row, no row after an achieving attempt, and an unachieved
occurrence running every attempt. The collapse fold is order-sensitive
within an occurrence (attempt 0 opens it), so a duplicate, missing or
reordered attempt would change a registered value in silence; this is the
check that makes the fold's input canonical. Every occurrence must be
present: a missing one would otherwise collapse to an unachieved
occurrence with the worst attainable score and enter the primary stratum. -/
def canonicalOccurrence (rows : Array TwinRow) (key : Fin occurrenceCount) :
    Except String Unit := do
  let seq := rows.filter fun r => r.key == key
  let some head := seq[0]? | throw s!"occurrence {key.val} has no rows"
  let mut due := 0
  for r in seq do
    unless r.attempt.val == due do
      throw s!"occurrence {key.val}: attempt {r.attempt.val} where attempt {due} was due (one ordered attempt sequence per occurrence)"
    unless r.family == head.family && r.initiallySatisfied == head.initiallySatisfied do
      throw s!"occurrence {key.val}: family or initial status changes between attempts"
    if r.achieved && due + 1 != seq.size then
      throw s!"occurrence {key.val}: rows continue after an achieving attempt"
    due := due + 1
  unless (seq.back?.map (·.achieved)).getD false || seq.size == attemptsPerGoal do
    throw s!"occurrence {key.val}: unachieved after {seq.size} of {attemptsPerGoal} attempts"

/-- Read one shard's rows twin, refusing anything that is not a complete
canonical record of this exact (seed, arm) shard. -/
def readShard (dir : String) (seedIndex : Nat) (arm : String) :
    IO (Array TwinRow) := do
  let index := if seedIndex < 10 then s!"0{seedIndex}" else s!"{seedIndex}"
  let path := s!"{dir}/seed-{index}-{arm}.rows"
  let text ← IO.FS.readFile path
  let mut rows : Array TwinRow := #[]
  let mut header := false
  for line in text.splitOn "\n" do
    let fields := (line.splitOn " ").filter (· ≠ "")
    match fields with
    | ["shard", idx, armName] =>
      -- The header identifies the shard, so it is compared rather than
      -- skipped: a twin renamed or copied over another is otherwise accepted
      -- in silence. Compare the index numerically — the writer emits it
      -- unpadded while the filename pads it.
      if idx.toNat? != some seedIndex || armName != arm then
        throw (IO.userError
          s!"{path}: header says shard {idx} {armName}, not {seedIndex} {arm}")
      header := true
    | [] => pure ()
    | "row" :: rest =>
      match parseRow rest with
      | .ok row => rows := rows.push row
      | .error e => throw (IO.userError s!"{path}: {e} in row line {line}")
    | _ => throw (IO.userError s!"{path}: unexpected line {line}")
  if !header then
    throw (IO.userError s!"{path}: no shard header")
  for key in Array.finRange occurrenceCount do
    if let .error e := canonicalOccurrence rows key then
      throw (IO.userError s!"{path}: {e}")
  pure rows

/-- Read one registered arm's shards, in seed order, as the population. The
arm must be one the manifest registers; the count is the type's. -/
def readArm (dir : String) (manifest : Manifest) (arm : String) : IO ArmOccs := do
  unless manifest.arms.contains arm do
    throw (IO.userError s!"manifest: {arm} is not a registered arm")
  Vector.ofFnM fun (s : Fin studySeeds) => do
    let rows ← readShard dir s.val arm
    pure (collapseTwinRows rows)

/-! ## The report -/

/-- Exact decimal rendering of a rational (numerator/denominator plus a
short decimal approximation for the reader). -/
def ratLine (name : String) (v : Rat) : String :=
  let approx := (Float.ofInt v.num) / (Float.ofNat v.den)
  s!"{name} = {v.num}/{v.den} ≈ {approx}"

/-- English count label: `1 win` / `2 wins`. The instrument prints a
quantity, not a table of inflected nouns, so the singular is the one
place the wording has to follow the number. -/
def labelledCount (n : Nat) (singular plural : String) : String :=
  if n == 1 then s!"{n} {singular}" else s!"{n} {plural}"

/-- One comparison's outcome tally line. The published decomposition of its
`poi`: the same counts the rational is formed from. -/
def decompLine (name : String) (t : Tally) : String :=
  s!"{name}: {labelledCount t.wins "win" "wins"}, {labelledCount t.ties "tie" "ties"}, {labelledCount t.losses "loss" "losses"} of {t.seeds} seeds"

/-- One thresholded conjunct's report line. -/
def conjunct (name : String) (v : Rat) (threshold : Rat) (strict : Bool) :
    String :=
  let holds := if strict then threshold < v else threshold ≤ v
  let rel := if strict then ">" else "≥"
  let outcome := if holds then "pass" else "FAIL"
  s!"{ratLine name v} [{rel} {threshold.num}/{threshold.den}: {outcome}]"

/-- The complete block of one thresholded comparison: the point conjunct,
its outcome tally, and the lower-bound conjunct, at the registered
thresholds. -/
def thresholdedBlock (key : String) (s : PairedSummary) : List String :=
  [conjunct s!"  {key}.poi" s.poi poiThreshold false,
   decompLine s!"  {key}" s.tally,
   conjunct s!"  {key}.prob_lower" s.probLower probLowerThreshold true]

/-- The complete block of one registered observational comparison: the
point estimate, its outcome tally, and the lower bound. -/
def observationalBlock (key : String) (s : PairedSummary) : List String :=
  [ratLine s!"  {key}.poi" s.poi,
   decompLine s!"  {key}" s.tally,
   ratLine s!"  {key}.prob_lower" s.probLower]

/-- The derived Reach lines: the `rm − fm` summary, or which seed has no
Reach-restricted primary stratum. -/
def reachLines : ReachReport → List String
  | .complete t =>
    [ratLine "  reach_vs_random" t.poi, decompLine "  reach_vs_random" t]
  | .incomplete seed =>
    [s!"  reach_vs_random: INCOMPLETE — seed {seed.val} has no Reach-restricted primary occurrence"]

/-- The post-hoc block: quantities no registration named, derived after the
run from the registered per-seed values (post-hoc reporting). They print under their
own heading so the record does not lend them a registration status. -/
def derivedBlock (continual : PairedSummary) (reach : ReachReport) : List String :=
  "derived reporting (post-hoc, not registered):" ::
  ratLine "  later_minus_first" continual.poi ::
  decompLine "  later_minus_first" continual.tally ::
  reachLines reach

/-- Exit status of a run whose registered functional had a value: `0`, or
`3` when the derived Reach report is incomplete — the verdict is printed
either way, and automation must not read success into an absent
deliverable. -/
def reachExitCode : ReachReport → UInt32
  | .complete _ => 0
  | .incomplete _ => 3

/-- What a study prints: its thresholded and observational comparisons by
key, any extra observational lines, the continual summary, and the derived
Reach report. -/
structure StudyReport where
  /-- Thresholded comparisons, in registration order. -/
  thresholded : List (String × PairedSummary)
  /-- Registered observational paired comparisons. -/
  observational : List (String × PairedSummary)
  /-- Registered observational lines that are not paired summaries. -/
  observationalExtra : List String
  /-- The continual-improvement summary. -/
  continual : PairedSummary
  /-- The derived Reach report. -/
  reach : ReachReport

/-- Every line of a study's report, from the blocks above. -/
def render (r : StudyReport) (accepted : Bool) : List String :=
  ("registered conjuncts (acceptance = all six):" ::
    r.thresholded.flatMap fun (key, s) => thresholdedBlock key s) ++
  ("registered observational (no thresholds):" ::
    r.observational.flatMap fun (key, s) => observationalBlock key s) ++
  r.observationalExtra ++
  [ratLine "  final_continual_lower" r.continual.effectLower] ++
  derivedBlock r.continual r.reach ++
  [s!"verdict: {if accepted then "ACCEPTED" else "REFUTED"}"]

/-- intra-option-credit's report. -/
def intraOptionCreditReport (r : IntraOptionCreditResult) : StudyReport :=
  { thresholded := [("final_vs_ablated_intra_option", r.ablation),
                    ("final_vs_frozen", r.frozen),
                    ("final_vs_random", r.random)]
    observational := [("final_vs_ablated_span_credit", r.span)]
    observationalExtra :=
      [s!"  reach_successes (ablation pairing stratum): final {r.reachFinal}, ablated_intra_option {r.reachAblation}, of {r.reachTotal}"]
    continual := r.continual
    reach := r.reachVsRandom }

/-- derived-exploration-rate's report. -/
def derivedExplorationRateReport (r : DerivedExplorationRateResult) : StudyReport :=
  { thresholded := [("final_vs_ablated_annealed_schedule", r.schedule),
                    ("final_vs_frozen", r.frozen),
                    ("final_vs_random", r.random)]
    observational := [("final_vs_ablated_shared_rate", r.shared)]
    observationalExtra := []
    continual := r.continual
    reach := r.reachVsRandom }

/-- stomp-planning's report. -/
def stompPlanningReport (r : StompPlanningResult) : StudyReport :=
  { thresholded := [("final_vs_ablated_hand_authored_subtasks", r.subtasks),
                    ("final_vs_frozen", r.frozen),
                    ("final_vs_random", r.random)]
    observational := [("final_vs_ablated_temporal_abstraction", r.temporal)]
    observationalExtra := []
    continual := r.continual
    reach := r.reachVsRandom }

end AcornSpec.Rows
