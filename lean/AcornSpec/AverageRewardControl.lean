/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Rows
import Lean.Data.Json
import Init.Data.Rat

/-!
# Exact analysis of the differential-control comparison

This calculator reduces explicit paired summaries using the population and
schedule constants in `AcornSpec.Constants`. Input admission checks the whole
population, each arm, the complete cycle shape and shared provenance fields.
The caller supplies the summaries; matching fields alone does not establish
that their values were observed.

The paired score is host achievements divided by actual environment steps.
An exact two-sided sign tail describes paired-win evidence; it is not an
interval for mean effect magnitude. Missing or malformed pairs fail the
analysis rather than contributing an invented zero outcome.
-/

namespace AcornSpec.AverageRewardControl

/-- Closed protocol revisions; no caller supplies a wider population or budget. -/
inductive Protocol where
  /-- Preserved eight-pair screening run with optional sampled memory. -/
  | v1
  /-- Twenty-pair revision requiring isolated-process resource accounting. -/
  | v2
  deriving DecidableEq

/-- Registered observation schema for a revision. -/
def Protocol.schema : Protocol → String
  | .v1 => "acorn-average-reward-control-observations-v1"
  | .v2 => "acorn-average-reward-control-observations-v2"

/-- Complete population from the model constants for each revision. -/
def Protocol.seeds : Protocol → List Nat
  | .v1 => Constants.averageRewardSeeds
  | .v2 => Constants.averageRewardRevisionSeeds

/-- Raw capacity belonging to the selected registered revision. -/
def Protocol.rawBudget : Protocol → Nat
  | .v1 => Constants.averageRewardRawBudget
  | .v2 => Constants.averageRewardRevisionRawBudget

/-- Read a required natural-number field. -/
def natField (json : Lean.Json) (key : String) : Except String Nat := do
  ((← json.getObjVal? key).getNat?).mapError (fun error => s!"{key}: {error}")

/-- Read a required string field. -/
def strField (json : Lean.Json) (key : String) : Except String String := do
  ((← json.getObjVal? key).getStr?).mapError (fun error => s!"{key}: {error}")

/-- Fixed-width lowercase seed spelling used by the summary format. -/
def seedHex (seed : Nat) : String :=
  let digits := String.ofList (Nat.toDigits 16 seed)
  String.ofList (List.replicate (16 - digits.length) '0') ++ digits

/-- Completed failed goals consume every capped attempt; a success consumes at
least one step. This lower bound is derived in `AverageRewardControlSemantics`. -/
def minimumCycleSteps (achieved : Nat) : Nat :=
  (Constants.averageRewardGoals - achieved) * Constants.averageRewardAttempts *
    Constants.averageRewardStepCap + achieved

/-- Sampled RSS is either unavailable or an ordered numeric range. -/
inductive RssRange where
  /-- No usable sample was reported. -/
  | unavailable
  /-- Both endpoints are actual numeric samples within the completed-run budget. -/
  | measured (lower upper : Nat) (ordered : lower ≤ upper)
      (bounded : upper ≤ Constants.averageRewardRssBudget)

/-- Render the admitted resource observation without inventing a measurement. -/
def RssRange.render : RssRange → String
  | .unavailable => "unavailable"
  | .measured lower upper _ _ => s!"{lower}..{upper}"

/-- Reject a half-missing, nonnumeric, reversed or over-budget RSS range. -/
def parseRss (json : Lean.Json) : Except String RssRange := do
  let lower ← json.getObjVal? "min_rss"
  let upper ← json.getObjVal? "max_rss"
  match lower, upper with
  | .null, .null => pure .unavailable
  | _, _ =>
    let lo ← lower.getNat? |>.mapError (fun error => s!"min_rss: {error}")
    let hi ← upper.getNat? |>.mapError (fun error => s!"max_rss: {error}")
    if ordered : lo ≤ hi then
      if bounded : hi ≤ Constants.averageRewardRssBudget then
        pure (.measured lo hi ordered bounded)
      else throw "max_rss exceeds the completed-run budget"
    else throw "min_rss exceeds max_rss"

/-- One complete cycle, with its exposure, goal-shape and resource obligations. -/
structure Cycle where
  /-- Actual environment steps. -/
  steps : Nat
  /-- A completed cycle always has a positive denominator. -/
  positive : 0 < steps
  /-- Per-goal achievement counts. -/
  goals : Array Nat
  /-- Every registered goal occurs exactly once. -/
  shape : goals.size = Constants.averageRewardGoals
  /-- A goal occurrence contributes zero or one achievement. -/
  binary : goals.all (· ≤ 1) = true
  /-- Failed goals cannot be declared complete before exhausting their attempts. -/
  exposure : minimumCycleSteps (goals.foldl (· + ·) 0) ≤ steps
  /-- Complete exposure never exceeds the opportunity budget. -/
  capped : steps ≤ Constants.averageRewardGoals * Constants.averageRewardAttempts *
    Constants.averageRewardStepCap
  /-- Sum of measured agent update microseconds. -/
  updateMicros : Nat
  /-- Largest measured single-update latency. -/
  maxUpdateMicros : Nat
  /-- The maximum is an observed summand and bounds every measured update. -/
  latency : maxUpdateMicros ≤ updateMicros ∧ updateMicros ≤ steps * maxUpdateMicros
  /-- Sampled process RSS bounds, explicitly unavailable when absent. -/
  rss : RssRange

/-- Total achievements are derived from the admitted per-goal counts. -/
def Cycle.achieved (cycle : Cycle) : Nat := cycle.goals.foldl (· + ·) 0

/-- Admit one complete cycle under the fixed opportunity schedule. -/
def parseCycle (json : Lean.Json) (index : Nat) : Except String Cycle := do
  unless (← natField json "cycle") == index do throw "cycle identity mismatch"
  let steps ← natField json "steps"
  if h : 0 < steps then
    let goals ← (← (← json.getObjVal? "goals").getArr?).mapM (·.getNat?)
    let achieved ← natField json "achieved"
    unless achieved == goals.foldl (· + ·) 0 do
      throw "cycle achievement total mismatch"
    let updateMicros ← natField json "update_us"
    let maxUpdateMicros ← natField json "max_update_us"
    if shape : goals.size = Constants.averageRewardGoals then
      if binary : goals.all (· ≤ 1) = true then
        if exposure : minimumCycleSteps (goals.foldl (· + ·) 0) ≤ steps then
          if capped : steps ≤ Constants.averageRewardGoals * Constants.averageRewardAttempts *
              Constants.averageRewardStepCap then
            if latency : maxUpdateMicros ≤ updateMicros ∧
                updateMicros ≤ steps * maxUpdateMicros then
              pure { steps, positive := h, goals, shape, binary, exposure, capped,
                     updateMicros, maxUpdateMicros, latency, rss := ← parseRss json }
            else throw "update_us/max_update_us disagree with the step count"
          else throw "cycle step cap exceeded"
        else throw "incomplete failed-goal exposure"
      else throw "goal achievement is not zero or one"
    else throw "goal shape mismatch"
  else throw "completed cycle has no steps"

/-- Mandatory completed-process measurement; zero and over-budget peaks have no constructor. -/
structure ProcessResources where
  /-- Maximum resident memory reported by the shell in KiB. -/
  peakKiB : Nat
  /-- A missing measurement cannot become a zero. -/
  positive : 0 < peakKiB
  /-- Process-resource acceptance bound derived from the registered byte limit. -/
  bounded : peakKiB * 1024 ≤ Constants.averageRewardRssBudget
  /-- Elapsed child setup and execution, measured by the supervisor. -/
  wallMillis : Nat
  /-- A complete worker has a positive observed duration. -/
  wallPositive : 0 < wallMillis
  /-- No complete individual stream can exceed the whole invocation budget. -/
  wallBounded : wallMillis ≤ Constants.averageRewardWallBudget * 1000
  /-- Shared source/build/executable/protocol content identities. -/
  identity : List String

/-- A v2 summary cannot inhabit the admitted input type without process resources. -/
inductive Resources : Protocol → Type where
  /-- Historical memory reporting retains its original limitation. -/
  | historical : Resources .v1
  /-- Revised evidence carries the positive bounded resource record. -/
  | observed (value : ProcessResources) : Resources .v2

/-- Resource identity is bound whenever this protocol requires a measurement. -/
def Resources.binds {protocol : Protocol} (resources : Resources protocol)
    (identity : List String) : Bool :=
  match resources with
  | .historical => true
  | .observed value => value.identity == identity

/-- Only an observed process contributes a resource line to the canonical report. -/
def Resources.render {protocol : Protocol} (resources : Resources protocol) (arm : String) :
    Option String :=
  match resources with
  | .historical => none
  | .observed value => some s!"  {arm} process: peak_rss_kib={value.peakKiB} wall_ms={value.wallMillis}"

/-- One complete arm in a pair, with its source/build/protocol identity. -/
structure Summary (protocol : Protocol) where
  /-- Canonical ordered cycles. -/
  cycles : Vector Cycle Constants.averageRewardCycles
  /-- Protocol-indexed evidence prevents omission of mandatory process memory. -/
  resources : Resources protocol
  /-- Source, build, executable and protocol digests. -/
  identity : List String

/-- Total environment exposure is derived from the complete cycles. -/
def Summary.steps {protocol : Protocol} (summary : Summary protocol) : Nat :=
  summary.cycles.foldl (fun n row => n + row.steps) 0

/-- Total achievements are derived from the complete cycles. -/
def Summary.achieved {protocol : Protocol} (summary : Summary protocol) : Nat :=
  summary.cycles.foldl (fun n row => n + row.achieved) 0

/-- Common content identities in both configuration and observation summaries. -/
def parseIdentity (json : Lean.Json) : Except String (List String) :=
  ["source_sha256", "build_sha256", "executable_sha256", "protocol_sha256"].mapM
    fun key => do
      let value ← strField json key
      unless value.length == 64 && value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
        throw s!"malformed {key}"
      pure value

/-- Required execution context, admitted before any paired result is calculated. -/
structure Configuration where
  /-- Closed registered revision. -/
  protocol : Protocol
  /-- Content identities to which every summary must belong. -/
  identity : List String
  /-- Captured compiler/tool-pin/machine descriptions, in the named order. -/
  environment : List (String × String)

/-- Bind the configuration to the generated protocol and require host context. -/
def parseConfiguration (text : String) : Except String Configuration := do
  let json ← Lean.Json.parse text
  let protocol ← match ← strField json "schema" with
    | "acorn-average-reward-control-observations-v1" => pure Protocol.v1
    | "acorn-average-reward-control-observations-v2" => pure Protocol.v2
    | _ => throw "configuration schema mismatch"
  for (key, expected) in
      [("world_side", Constants.averageRewardWorldSide),
       ("agent_seed", Constants.averageRewardAgentSeed),
       ("seed_count", protocol.seeds.length),
       ("cycles", Constants.averageRewardCycles), ("goals", Constants.averageRewardGoals),
       ("attempts", Constants.averageRewardAttempts), ("step_cap", Constants.averageRewardStepCap),
       ("wall_budget_seconds", Constants.averageRewardWallBudget),
       ("rss_budget_bytes", Constants.averageRewardRssBudget),
       ("raw_budget_bytes", protocol.rawBudget)] do
    unless (← natField json key) == expected do throw s!"configuration {key} mismatch"
  let seeds ← (← (← json.getObjVal? "seeds").getArr?).mapM (·.getStr?)
  unless seeds.toList == protocol.seeds.map seedHex do
    throw "configuration population mismatch"
  let arms ← (← (← json.getObjVal? "arms").getArr?).mapM (·.getStr?)
  unless arms == #["average-reward", "discounted"] do throw "configuration arms mismatch"
  if protocol == .v2 then
    unless (← strField json "resource_method") == "zsh-time-M-kib" do
      throw "resource method mismatch"
  let env ← json.getObjVal? "environment"
  let keys := ["rustc", "kani_pin", "lean_pin", "machine"] ++
    (if protocol == .v2 then ["resource_shell"] else [])
  let environment ← keys.mapM fun key => do
    let value ← strField env key
    unless !value.trimAscii.toString.isEmpty do throw s!"missing environment {key}"
    pure (key, value)
  pure { protocol, identity := ← parseIdentity json, environment }

/-- Admit the complete resource record for this exact seed, arm and protocol. -/
def parseResources (text : String) (index seed : Nat) (arm : String) :
    Except String ProcessResources := do
  let json ← Lean.Json.parse text
  unless (← strField json "schema") == Protocol.v2.schema &&
      (← strField json "kind") == "process-resources" &&
      (← natField json "seed_index") == index &&
      (← strField json "seed") == seedHex seed &&
      (← strField json "arm") == arm do throw "process-resource identity mismatch"
  let peakKiB ← natField json "peak_rss_kib"
  let wallMillis ← natField json "process_wall_ms"
  if positive : 0 < peakKiB then
    if bounded : peakKiB * 1024 ≤ Constants.averageRewardRssBudget then
      if wallPositive : 0 < wallMillis then
        if wallBounded : wallMillis ≤ Constants.averageRewardWallBudget * 1000 then
          pure { peakKiB, positive, bounded, wallMillis, wallPositive, wallBounded,
                 identity := ← parseIdentity json }
        else throw "process wall time exceeds invocation budget"
      else throw "missing positive process wall time"
    else throw "process peak exceeds memory budget"
  else throw "missing positive process peak"

/-- Parse and bind a summary to one generated seed and one criterion. -/
def parseSummary (protocol : Protocol) (resources : Resources protocol) (text : String) (index seed : Nat) (arm : String) (criterion : Nat) :
    Except String (Summary protocol) := do
  let json ← Lean.Json.parse text
  unless (← strField json "kind") == "complete" &&
      (← strField json "schema") == protocol.schema do
    throw "not a complete selected-protocol summary"
  unless (← natField json "seed_index") == index &&
      (← strField json "seed") == seedHex seed &&
      (← strField json "arm") == arm &&
      (← natField json "criterion") == criterion do throw "seed/arm identity mismatch"
  let rows ← (← json.getObjVal? "cycles").getArr?
  if count : rows.size = Constants.averageRewardCycles then
    let input : Vector Lean.Json Constants.averageRewardCycles := ⟨rows, count⟩
    let cycles ← input.zipIdx.mapM fun (row, i) =>
      (parseCycle row i).mapError (fun error => s!"cycle {i}: {error}")
    let identity ← parseIdentity json
    unless resources.binds identity do throw "process-resource provenance mismatch"
    let summary := { cycles, resources, identity : Summary protocol }
    unless (← natField json "total_steps") == summary.steps &&
        (← natField json "achieved") == summary.achieved do
      throw "summary totals differ from cycle totals"
    pure summary
  else throw "missing/extra cycle"

/-- Exact per-stream host reward rate; input admission ensures positive exposure. -/
def Summary.rate {protocol : Protocol} (summary : Summary protocol) : Rat := summary.achieved / (summary.steps : Rat)

/-- Exact per-cycle host reward rate. -/
def Cycle.rate (cycle : Cycle) : Rat := cycle.achieved / (cycle.steps : Rat)

/-- Finite factorial used by the core-only exact counting calculator. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Exact factorial quotient, universally linked to `Nat.choose` in the proof module.
Work is linear in the arguments; the calculator does not load Mathlib or expand
an exponential Pascal tree for each report. -/
def binomial (n k : Nat) : Nat :=
  if k ≤ n then factorial n / (factorial k * factorial (n - k)) else 0

/-- Two-sided paired sign tail after removing exact ties; all ties gives one. -/
def signTail (wins losses : Nat) : Rat :=
  let n := wins + losses
  let numerator := 2 * ((List.range (min wins losses + 1)).map (binomial n)).sum
  min 1 ((numerator : Rat) / (2 ^ n : Nat))

/-- Render exact rationals without rounding the decision statistic. -/
def rational (value : Rat) : String := s!"{value.num}/{value.den}"

/-- Scientific assessment of the positive-effect hypothesis, shared by every label. -/
inductive Assessment where
  /-- Positive mean and paired-win evidence meet the registered rule. -/
  | supported
  /-- Negative mean and paired-loss evidence meet the registered rule. -/
  | refuted
  /-- The registered directional rule does not resolve the comparison. -/
  | inconclusive
  deriving DecidableEq

/-- Dossier-compatible assessment spelling. -/
def Assessment.verdict : Assessment → String
  | .supported => "supported"
  | .refuted => "refuted"
  | .inconclusive => "inconclusive"

/-- Direction of the same scientific assessment. -/
def Assessment.direction : Assessment → String
  | .supported => "positive"
  | .refuted => "negative"
  | .inconclusive => "inconclusive"

/-- Registered sign-tail and mean-direction rule; disagreements remain inconclusive. -/
def assessment (counts : Tally) (mean : Rat) : Assessment :=
  if signTail counts.wins counts.losses ≤ (1 : Rat) / 20 ∧
      0 < mean ∧ counts.losses < counts.wins then .supported
  else if signTail counts.wins counts.losses ≤ (1 : Rat) / 20 ∧
      mean < 0 ∧ counts.wins < counts.losses then .refuted
  else .inconclusive

/-- Stable canonical comparison key. -/
def comparisonKey : String := "average_reward_vs_discounted"

/-- The full registered population is required before producing a primary report. -/
def comparisonReport {population : Nat} (differences : Vector Rat population) : List String :=
  let counts := tally differences.toArray
  let mean := differences.foldl (· + ·) 0 / (differences.size : Rat)
  let result := assessment counts mean
  [s!"mean paired reward-rate difference={rational mean}",
   Rows.ratLine s!"  {comparisonKey}.poi" counts.poi,
   Rows.decompLine s!"  {comparisonKey}" counts,
   s!"exact two-sided sign tail={rational (signTail counts.wins counts.losses)}",
   s!"evidence direction: {result.direction}", s!"verdict: {result.verdict}"]

/-- The protocol index selects whether a resource file is mandatory. -/
def readResources : (protocol : Protocol) → String → Nat → Nat → String → IO (Resources protocol)
  | .v1, _, _, _, _ => pure .historical
  | .v2, path, index, seed, arm => do
    match parseResources (← IO.FS.readFile path) index seed arm with
    | .ok value => pure (.observed value)
    | .error error => throw (IO.userError s!"{path}: {error}")

/-- A completed v2 invocation carries all forty streams and both whole-run budgets. -/
structure InvocationComplete where
  /-- Number of completed isolated streams. -/
  streams : Nat
  /-- Every seed has both arms. -/
  population : streams = Constants.averageRewardRevisionSeeds.length * 2
  /-- Wall duration recorded before parent completion publication. -/
  wallMillis : Nat
  /-- Completion precedes the registered stop threshold. -/
  wallBounded : wallMillis < Constants.averageRewardWallBudget * 1000
  /-- Actual aggregate raw-file lengths. -/
  rawBytes : Nat
  /-- Complete output respects the registered capacity. -/
  rawBounded : rawBytes ≤ Constants.averageRewardRevisionRawBudget

/-- Closed revision-specific parent-completion obligations. -/
inductive Completion : Protocol → Type where
  /-- The preserved v1 reader retains its original lifecycle contract. -/
  | historical : Completion .v1
  /-- Revised reports require an admitted whole-invocation completion. -/
  | complete (value : InvocationComplete) : Completion .v2

/-- Reject an absent, mismatched or over-budget parent-completion record. -/
def parseCompletion (text : String) (identity : List String) : Except String InvocationComplete := do
  let json ← Lean.Json.parse text
  unless (← strField json "schema") == Protocol.v2.schema &&
      (← strField json "kind") == "invocation-complete" &&
      (← parseIdentity json) == identity do throw "parent completion identity mismatch"
  let streams ← natField json "streams"
  let wallMillis ← natField json "wall_ms"
  let rawBytes ← natField json "raw_bytes"
  if population : streams = Constants.averageRewardRevisionSeeds.length * 2 then
    if wallBounded : wallMillis < Constants.averageRewardWallBudget * 1000 then
      if rawBounded : rawBytes ≤ Constants.averageRewardRevisionRawBudget then
        pure { streams, population, wallMillis, wallBounded, rawBytes, rawBounded }
      else throw "invocation raw budget exceeded"
    else throw "invocation wall threshold reached"
  else throw "incomplete invocation population"

/-- A v2 primary analysis cannot start without successful parent admission. -/
def readCompletion : (protocol : Protocol) → String → List String → IO (Completion protocol)
  | .v1, _, _ => pure .historical
  | .v2, path, identity => do
    match parseCompletion (← IO.FS.readFile path) identity with
    | .ok value => pure (.complete value)
    | .error error => throw (IO.userError s!"{path}: {error}")

/-- Revised canonical output exposes the whole-invocation resource observation. -/
def Completion.render {protocol : Protocol} (completion : Completion protocol) : Option String :=
  match completion with
  | .historical => none
  | .complete value => some s!"invocation: streams={value.streams} wall_ms={value.wallMillis} raw_bytes={value.rawBytes}"

/-- Read one canonical paired input or fail with the affected file's identity. -/
def readSummary (protocol : Protocol) (dir : String) (index seed : Nat) (arm : String) (criterion : Nat) :
    IO (Summary protocol) := do
  let idx := if index < 10 then s!"0{index}" else toString index
  let path := s!"{dir}/seed-{idx}-{arm}.json"
  let text ← IO.FS.readFile path
  let resources ← readResources protocol s!"{dir}/../resources/seed-{idx}-{arm}.json" index seed arm
  match parseSummary protocol resources text index seed arm criterion with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{path}: {error}")

/-- Print the complete paired calculation, including all exploratory cycle data. -/
def analyze (dir : String) : IO Unit := do
  let configurationPath := s!"{dir}/../configuration.json"
  let configuration ← match parseConfiguration (← IO.FS.readFile configurationPath) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"{configurationPath}: {error}")
  let completion ← readCompletion configuration.protocol s!"{dir}/../invocation-complete.json" configuration.identity
  if let some line := completion.render then IO.println line
  for (key, value) in configuration.environment do
    IO.println s!"environment {key}: {Lean.Json.str value |>.compress}"
  let mut differences : Array Rat := #[]
  let mut gains : List Rat := []
  for (seed, index) in configuration.protocol.seeds.zipIdx do
    let treatment ← readSummary configuration.protocol dir index seed "average-reward" 1
    let comparator ← readSummary configuration.protocol dir index seed "discounted" 0
    unless treatment.identity == comparator.identity do
      throw (IO.userError s!"seed {index}: paired provenance differs")
    unless treatment.identity == configuration.identity do
      throw (IO.userError s!"seed {index}: provenance differs from configuration")
    let difference := treatment.rate - comparator.rate
    differences := differences.push difference
    IO.println s!"seed {index}: average-reward={treatment.achieved}/{treatment.steps} discounted={comparator.achieved}/{comparator.steps} difference={rational difference}"
    for (arm, summary) in [("average-reward", treatment), ("discounted", comparator)] do
      if let some line := summary.resources.render arm then IO.println line
      for (cycle, i) in summary.cycles.toArray.zipIdx do
        IO.println s!"  {arm} cycle {i}: reward_rate={rational cycle.rate} steps={cycle.steps} achieved={cycle.achieved} goals={cycle.goals} mean_update_us={rational ((cycle.updateMicros : Rat) / cycle.steps)} max_update_us={cycle.maxUpdateMicros} sampled_rss_bytes={cycle.rss.render}"
    let some firstT := treatment.cycles.toArray[0]? | throw (IO.userError "missing first cycle")
    let some lastT := treatment.cycles.toArray.back? | throw (IO.userError "missing last cycle")
    let some firstC := comparator.cycles.toArray[0]? | throw (IO.userError "missing first cycle")
    let some lastC := comparator.cycles.toArray.back? | throw (IO.userError "missing last cycle")
    let gain := (lastT.rate - firstT.rate) - (lastC.rate - firstC.rate)
    gains := gains ++ [gain]
    IO.println s!"  exploratory difference in final-minus-first rate change={rational gain}"
  IO.println s!"exploratory mean adaptation contrast={rational (gains.sum / (gains.length : Rat))}"
  if configuration.protocol == .v2 then
    IO.println "inference target: conditional paired-win probability; null=1/2 under independent common-probability world signs"
    IO.println "mean paired difference: descriptive effect summary and direction veto; no population-mean inference"
  if count : differences.size = configuration.protocol.seeds.length then
    for line in comparisonReport ⟨differences, count⟩ do IO.println line
  else throw (IO.userError "incomplete paired population")

end AcornSpec.AverageRewardControl
