/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Runner
import Acorn.Planning

/-!
# Current command admission and composition boundary

The demo parser retains the complete current flag domain and its refusals.
ANSI selection has a separate value type, so ignored streaming-only flags cannot
reach that loop. Other commands retain their distinct maintained owner rather
than being interpreted as a demo or running a substitute learning composition.
-/
namespace Acorn.Host.Cli

/-- Every current CLI dispatch branch, including the isolated study subprocess. -/
inductive Command where
  /-- Ordinary or ANSI demonstration. -/
  | demo
  /-- Pinned deterministic mutation audit. -/
  | audit
  /-- Generate compiler-linked constants. -/
  | emitLean
  /-- Preserve execution identity without learning. -/
  | executionIdentity
  /-- Baseline study, probe, emission and verification modes. -/
  | agentBaseline
  /-- Intra-option credit study or probe. -/
  | intraOptionCredit
  /-- Exploration-rate study or probe. -/
  | derivedExplorationRate
  /-- Planning study or probe. -/
  | stompPlanning
  /-- Paired differential control study. -/
  | averageRewardControl
  /-- Isolated differential control arm. -/
  | averageRewardControlArm
  /-- Operational study and timed attempt-boundary shutdown. -/
  | enduranceStability
  deriving DecidableEq

/-- CLI refusals preserve the offending field rather than silently taking a default. -/
inductive Error where
  /-- Unrecognized command name. -/
  | command (name : String)
  /-- Unrecognized option. -/
  | unknown (name : String)
  /-- Missing required value. -/
  | missing (name : String)
  /-- Repeated option. -/
  | repeated (name : String)
  /-- Invalid value or incompatible combination. -/
  | invalid (name value : String)
  /-- Standard world admission failure. -/
  | world (error : WorldConfigError)
  deriving DecidableEq

/-- Admission errors retain the offending command/option and its supplied value. -/
def Error.message : Error → String
  | .command name => s!"unknown command {name}"
  | .unknown name => s!"unknown option {name}"
  | .missing name => s!"missing value for {name}"
  | .repeated name => s!"repeated option {name}"
  | .invalid name value => s!"invalid {name}: {value}"
  | .world _ => "world configuration refused"

/-- No command and flag-first invocation retain the demo shorthand. -/
def command (arguments : List String) : Except Error Command :=
  match arguments.head? with
  | none => .ok .demo
  | some name => match name with
    | "demo" => .ok .demo
    | "audit" => .ok .audit
    | "emit-lean" => .ok .emitLean
    | "execution-identity" => .ok .executionIdentity
    | "agent-baseline" => .ok .agentBaseline
    | "intra-option-credit" => .ok .intraOptionCredit
    | "derived-exploration-rate" => .ok .derivedExplorationRate
    | "stomp-planning" => .ok .stompPlanning
    | "average-reward-control" => .ok .averageRewardControl
    | "average-reward-control-arm" => .ok .averageRewardControlArm
    | "endurance-stability" => .ok .enduranceStability
    | _ => if name.startsWith "--" then .ok .demo else .error (.command name)

/-- The current 21-option schema; the boolean determines value consumption. -/
def demoFlags : List (String × Bool) :=
  [("--seed", true), ("--side", true), ("--steps", true), ("--attempts", true),
    ("--goals", true), ("--cycles", true), ("--view", true), ("--csv", true),
    ("--criterion", true), ("--research-profile", true), ("--planning", true),
    ("--step-order", true), ("--checkpoint", true),
    ("--checkpoint-every", true), ("--baseline", false), ("--telemetry", false),
    ("--control-stdin", false), ("--run-id", true), ("--agent-epoch", true),
    ("--new-agent-epoch", true), ("--cleared", false)]

/-- Structural scan refuses repeated/unknown options and recognized options used as values.
Unrecognized positional tokens retain the source parser's ignored-positional policy. -/
def scan (schema : List (String × Bool)) : List String → List String → Except Error Unit
  | [], _ => .ok ()
  | name :: rest, seen =>
    match schema.lookup name with
    | none => if name.startsWith "--" then .error (.unknown name) else scan schema rest seen
    | some takesValue =>
      if seen.contains name then .error (.repeated name)
      else if takesValue then
        match rest with
        | [] => .error (.missing name)
        | value :: tail =>
          if (schema.lookup value).isSome then .error (.missing name)
          else scan schema tail (name :: seen)
      else scan schema rest (name :: seen)

/-- Read the first occurrence, including values containing arbitrary path text. -/
def value : List String → String → Except Error (Option String)
  | [], _ => .ok none
  | name :: rest, wanted =>
    if name == wanted then match rest with
      | [] => .error (.missing wanted)
      | text :: _ => .ok (some text)
    else value rest wanted

/-- Required string admission agrees with the lifecycle protocol's Unicode trim. -/
def required (arguments : List String) (name : String) : Except Error String := do
  let some text ← value arguments name | .error (.missing name)
  if (trimControlLine text).isEmpty || text.startsWith "--" then .error (.invalid name text)
  else return text

/-- Decimal unsigned syntax includes an optional leading plus but no whitespace. -/
def natural (text : String) : Option Nat :=
  let digits := if text.startsWith "+" then String.ofList text.toList.tail else text
  if digits.isEmpty || !digits.toList.all (fun c => '0' ≤ c && c ≤ '9') then none
  else digits.toNat?

/-- Integer width is checked before conversion; textual overflow never wraps. -/
def unsigned (arguments : List String) (name : String) (width fallback : Nat) : Except Error Nat := do
  match ← value arguments name with
  | none => return fallback
  | some text =>
    let some number := natural text | .error (.invalid name text)
    if number < 2 ^ width then return number else .error (.invalid name text)

/-- Signed standard-side text is admitted over the entire i64 parse domain first. -/
def side (arguments : List String) : Except Error Coordinate := do
  match ← value arguments "--side" with
  | none => return ⟨1024, by decide⟩
  | some text =>
    let negative := text.startsWith "-"
    let digits := if negative then String.ofList text.toList.tail else text
    let some magnitude := natural digits | .error (.invalid "--side" text)
    if negative && digits.startsWith "+" then .error (.invalid "--side" text)
    let number : Int := if negative then -(magnitude : Int) else magnitude
    let some coordinate := Coordinate.checked number | .error (.invalid "--side" text)
    return coordinate

/-- Stable research profile vocabulary; there is no implicit promotion. -/
def profile (text : String) : Except Error ResearchProfile :=
  match text with
  | "ranked" => .ok .ranked | "primitive" => .ok .primitive
  | "boundary-credit" => .ok .boundaryCredit | "annealed" => .ok .annealed
  | "spatial" => .ok .spatial | _ => .error (.invalid "--research-profile" text)

/-- Criterion absence is preserved for the authoritative full-agent default owner. -/
def criterion (arguments : List String) : Except Error (Option Features.Criterion) := do
  match ← value arguments "--criterion" with
  | none => return none
  | some "discounted" => return some .discounted
  | some "average-reward" => return some .differential
  | some text => .error (.invalid "--criterion" text)

/-- Explicit planning admission delegates the single closed spelling rule to
`Features.PlanningSelection.parse`; this layer owns only its error vocabulary
and performs no substitution. -/
def planningValue (text : String) : Except Error Features.PlanningSelection :=
  match Features.PlanningSelection.parse text with
  | some selection => .ok selection
  | Option.none => .error (.invalid "--planning" text)

/-- Omission selects expectation-model planning; explicit values use the same checked admission. -/
def planningSelection (arguments : List String) : Except Error Features.PlanningSelection := do
  match ← value arguments "--planning" with
  | none => return .expectation
  | some text => planningValue text

/-- Every omitted planning value selects expectation-model planning, independently of other arguments. -/
theorem planningSelection_absent (arguments : List String)
    (absent : value arguments "--planning" = .ok none) :
    planningSelection arguments = .ok .expectation := by
  simp [planningSelection, absent]
  rfl

/-- Every supplied planning value reaches the closed-domain parser without substitution. -/
theorem planningSelection_provided (arguments : List String) (text : String)
    (provided : value arguments "--planning" = .ok (some text)) :
    planningSelection arguments = planningValue text := by
  simp [planningSelection, provided]
  rfl

/-- Explicit step-order admission delegates the single closed spelling rule to
`StepOrder.parse`; this layer owns only its error vocabulary and performs no
substitution. -/
def stepOrderValue (text : String) : Except Error StepOrder :=
  match StepOrder.parse text with
  | some order => .ok order
  | Option.none => .error (.invalid "--step-order" text)

/-- Omission selects learn-then-act: both parts of a step precede the world's
transition. Explicit values use the same checked admission. -/
def stepOrder (arguments : List String) : Except Error StepOrder := do
  match ← value arguments "--step-order" with
  | none => return .learnThenAct
  | some text => stepOrderValue text

/-- **The value admission accepts exactly the spelled orders.** For every text and order,
the admission returns the order exactly when the text spells it
(`StepOrder.Spelled`, a specification with no executed function). -/
theorem stepOrderValue_iff (text : String) (order : StepOrder) :
    stepOrderValue text = .ok order ↔ StepOrder.Spelled text order := by
  rw [← StepOrder.parse_spelled]
  unfold stepOrderValue
  cases StepOrder.parse text with
  | none => simp
  | some found => simp

/-- **The value admission refuses exactly the texts that spell no order,** with the one
error that names the flag and the text. -/
theorem stepOrderValue_refused (text : String) (error : Error) :
    stepOrderValue text = .error error ↔
      (∀ order, ¬ StepOrder.Spelled text order) ∧ error = .invalid "--step-order" text := by
  rw [← StepOrder.parse_refused]
  unfold stepOrderValue
  cases StepOrder.parse text with
  | none =>
    simp only [Except.error.injEq, true_and]
    exact eq_comm
  | some found => simp

/-- **The step order of a command line.** For every argument list and order, the
admission returns the order exactly when the flag is absent and the order is the
default, or the flag has a text that spells the order. The reading of the flag is the
option reader's; the default and the spelling are this decision's. -/
theorem stepOrder_iff (arguments : List String) (order : StepOrder) :
    stepOrder arguments = .ok order ↔
      (value arguments "--step-order" = .ok none ∧ order = .learnThenAct) ∨
        ∃ text, value arguments "--step-order" = .ok (some text) ∧
          StepOrder.Spelled text order := by
  unfold stepOrder
  cases read : value arguments "--step-order" with
  | error refusal => simp [bind, Except.bind]
  | ok found =>
    cases found with
    | none =>
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, true_and, reduceCtorEq,
        false_and, exists_false, or_false]
      exact eq_comm
    | some text =>
      simp only [bind, Except.bind, Except.ok.injEq, Option.some.injEq, reduceCtorEq, false_and,
        false_or, exists_eq_left']
      exact stepOrderValue_iff text order

/-- Every omitted step order selects learn-then-act, independently of other arguments. -/
theorem stepOrder_absent (arguments : List String)
    (absent : value arguments "--step-order" = .ok none) :
    stepOrder arguments = .ok .learnThenAct := by
  simp [stepOrder, absent]
  rfl

/-- Every supplied step order reaches the closed-domain parser without substitution. -/
theorem stepOrder_provided (arguments : List String) (text : String)
    (provided : value arguments "--step-order" = .ok (some text)) :
    stepOrder arguments = stepOrderValue text := by
  simp [stepOrder, provided]
  rfl

/-- Shared world and finite/unbounded goal schedule, with no agent construction side effect. -/
structure Common where
  /-- Explicit research profile. -/
  profile : ResearchProfile
  /-- Admitted receiving world. -/
  world : WorldConfig
  /-- Requested per-attempt steps. -/
  steps : UInt64
  /-- Requested goal count, later clipped to the receiving curriculum. -/
  goals : UInt64
  /-- Zero denotes unbounded repetitions. -/
  cycles : UInt64
  /-- Immutable planning selection shared by streaming and ANSI construction. -/
  planning : Features.PlanningSelection

/-- Streaming-only options forwarded to their actual full-agent/persistence/telemetry owners. -/
structure Streaming where
  /-- Shared configuration. -/
  common : Common
  /-- Requested attempt count, with campaign admission normalizing zero. -/
  attempts : UInt64
  /-- Explicit criterion override, if supplied. -/
  criterion : Option Features.Criterion
  /-- Checkpoint destination. -/
  checkpoint : Option String
  /-- Positive schedules write; zero is load-only. -/
  checkpointEvery : UInt32
  /-- Post-campaign random baseline selection. -/
  baseline : Bool
  /-- Stream telemetry selection. -/
  telemetry : Bool
  /-- Outcome CSV destination. -/
  csv : Option String
  /-- Detached stdin control reader selection. -/
  controlStdin : Bool
  /-- Supplied durable run identity. -/
  runId : UInt64
  /-- Receiving logical agent epoch. -/
  agentEpoch : UInt64
  /-- Epoch for a fresh agent after absent/refused load. -/
  newAgentEpoch : UInt64
  /-- Explicit cleared origin instead of fresh origin. -/
  cleared : Bool
  /-- Declared order of the agent's two step parts around the world's transition. -/
  order : StepOrder

/-- The separate ANSI domain has no ignored streaming-only option. -/
inductive Demo where
  /-- Ordinary streaming attempt/campaign protocol. -/
  | streaming (options : Streaming)
  /-- ANSI loop with a positive rendering period. -/
  | ansi (common : Common) (period : Word.Count)

/-- Ordinary CLI terrain seed, shared with legacy checkpoint adoption. -/
def defaultSeed : UInt64 := 42

/-- Complete current demo admission, with domain checks before world construction. -/
def demo (arguments : List String) : Except Error Demo := do
  scan demoFlags arguments []
  if arguments.contains "--checkpoint-every" && !(arguments.contains "--checkpoint") then
    .error (.missing "--checkpoint")
  for (first, second) in [("--checkpoint", "--csv"), ("--control-stdin", "--baseline")] do
    if arguments.contains first && arguments.contains second then
      .error (.invalid second s!"unsupported with {first}")
  if arguments.contains "--baseline" then
    if (← unsigned arguments "--cycles" 64 1) == 0 then
      .error (.invalid "--baseline" "unsupported with unbounded --cycles 0")
  let goals ← unsigned arguments "--goals" 64 10
  if goals == 0 then
    if (← unsigned arguments "--cycles" 64 1) == 0 then
      .error (.invalid "--goals" "zero with unbounded --cycles 0")
  let selected ← profile (← required arguments "--research-profile")
  if !selected.resumable && arguments.contains "--checkpoint" then
    .error (.invalid "--checkpoint" "selected research profile has no checkpoint encoding")
  let epoch ← unsigned arguments "--agent-epoch" 64 0
  let criterion ← criterion arguments
  let planning ← planningSelection arguments
  let order ← stepOrder arguments
  let view ← unsigned arguments "--view" 64 0
  if view > 0 then
    for (name, _) in demoFlags do
      if !(["--seed", "--side", "--steps", "--goals", "--cycles", "--view", "--research-profile", "--planning"].contains name) &&
          arguments.contains name then
        .error (.invalid name "unsupported with ANSI --view")
  let seed := (← unsigned arguments "--seed" 64 defaultSeed.toNat).toUInt64
  let coordinate ← side arguments
  let steps := (← unsigned arguments "--steps" 64 3000).toUInt64
  let attempts := (← unsigned arguments "--attempts" 64 3).toUInt64
  let cycles ← unsigned arguments "--cycles" 64 1
  let checkpointEvery := (← unsigned arguments "--checkpoint-every" 32 4).toUInt32
  let csv ← value arguments "--csv"
  let checkpoint ← value arguments "--checkpoint"
  let runId := (← unsigned arguments "--run-id" 64 seed.toNat).toUInt64
  let newEpoch := (← unsigned arguments "--new-agent-epoch" 64 epoch).toUInt64
  let world ← (WorldConfig.standard seed coordinate).mapError Error.world
  let common : Common := ⟨selected, world, steps, goals.toUInt64, cycles.toUInt64, planning⟩
  if hv : 0 < view ∧ view < 2 ^ 64 then
    return .ansi common ⟨view.toUInt64, by change 0 < view % (2 ^ 64); rw [Nat.mod_eq_of_lt hv.2]; exact hv.1⟩
  else
    return .streaming ⟨common, attempts, criterion, checkpoint, checkpointEvery,
      arguments.contains "--baseline", arguments.contains "--telemetry", csv,
      arguments.contains "--control-stdin", runId, epoch.toUInt64, newEpoch, arguments.contains "--cleared",
      order⟩

/-- Streaming schedule is a direct projection, without a second set of defaults. -/
def Streaming.campaign (options : Streaming) : CampaignSpec :=
  ⟨options.common.steps, options.attempts, options.common.goals, options.common.cycles⟩

/-- Later owners receive the untouched arguments of their own distinct command. -/
inductive Dispatch where
  /-- Current runner admission has completed. -/
  | demo (options : Demo)
  /-- A distinct command retains its source owner and exact argument list. -/
  | external (command : { selected : Command // selected ≠ .demo }) (arguments : List String)

/-- Exhaustive command routing never substitutes a demo for a study or an unknown command. -/
def dispatch (arguments : List String) : Except Error Dispatch := do
  let selected ← command arguments
  if h : selected = .demo then return .demo (← demo arguments)
  else return .external ⟨selected, h⟩ arguments

end Acorn.Host.Cli
