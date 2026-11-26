import Acorn.Digits
import Acorn.Host.Runner
import Acorn.Planning

namespace Acorn.Host.Cli

inductive Command where
  | demo
  | audit
  | emitLean
  | executionIdentity
  | agentBaseline
  | intraOptionCredit
  | derivedExplorationRate
  | stompPlanning
  | averageRewardControl
  | averageRewardControlArm
  | enduranceStability
  | visits
  deriving DecidableEq

inductive Error where
  | command (name : String)
  | unknown (name : String)
  | missing (name : String)
  | repeated (name : String)
  | invalid (name value : String)
  | world (error : WorldConfigError)
  deriving DecidableEq

def Error.message : Error → String
  | .command name => s!"unknown command {name}"
  | .unknown name => s!"unknown option {name}"
  | .missing name => s!"missing value for {name}"
  | .repeated name => s!"repeated option {name}"
  | .invalid name value => s!"invalid {name}: {value}"
  | .world _ => "world configuration refused"

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
    | "visits" => .ok .visits
    | _ => if name.startsWith "--" then .ok .demo else .error (.command name)

def demoFlags : List (String × Bool) :=
  [("--seed", true), ("--side", true), ("--steps", true), ("--attempts", true),
    ("--goals", true), ("--cycles", true), ("--view", true), ("--csv", true),
    ("--criterion", true), ("--research-profile", true), ("--planning", true),
    ("--step-order", true), ("--checkpoint", true),
    ("--checkpoint-every", true), ("--baseline", false), ("--telemetry", false),
    ("--control-stdin", false), ("--run-id", true), ("--agent-epoch", true),
    ("--new-agent-epoch", true), ("--cleared", false)]

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

def value : List String → String → Except Error (Option String)
  | [], _ => .ok none
  | name :: rest, wanted =>
    if name == wanted then match rest with
      | [] => .error (.missing wanted)
      | text :: _ => .ok (some text)
    else value rest wanted

def Follows (arguments : List String) (option text : String) : Prop :=
  ∃ before after, arguments = before ++ option :: text :: after ∧ option ∉ before

def Ends (arguments : List String) (option : String) : Prop :=
  ∃ before, arguments = before ++ [option] ∧ option ∉ before

theorem value_absent (arguments : List String) (wanted : String) :
    value arguments wanted = .ok none ↔ wanted ∉ arguments := by
  induction arguments with
  | nil => simp [value]
  | cons name rest ih =>
    unfold value
    by_cases same : name = wanted
    · subst same
      cases rest <;> simp
    · have other : ¬ wanted = name := fun found => same found.symm
      simp [same, other, ih]

theorem value_follows (arguments : List String) (wanted text : String) :
    value arguments wanted = .ok (some text) ↔ Follows arguments wanted text := by
  induction arguments with
  | nil =>
    constructor
    · intro found
      cases found
    · rintro ⟨before, after, shape, -⟩
      cases before <;> cases shape
  | cons name rest ih =>
    unfold value
    by_cases same : name = wanted
    · subst same
      cases rest with
      | nil =>
        constructor
        · intro found
          simp at found
        · rintro ⟨before, after, shape, absent⟩
          cases before with
          | nil => cases shape
          | cons head tail =>
            have first : name = head := (List.cons.inj shape).1
            exact (absent (first ▸ List.mem_cons_self)).elim
      | cons next tail =>
        constructor
        · intro found
          simp only [beq_self_eq_true, ↓reduceIte, Except.ok.injEq, Option.some.injEq] at found
          exact ⟨[], tail, by rw [found]; rfl, List.not_mem_nil⟩
        · rintro ⟨before, after, shape, absent⟩
          cases before with
          | nil =>
            have texts : next = text := (List.cons.inj (List.cons.inj shape).2).1
            simp [texts]
          | cons head others =>
            have first : name = head := (List.cons.inj shape).1
            exact (absent (first ▸ List.mem_cons_self)).elim
    · simp only [beq_iff_eq, same, ↓reduceIte]
      rw [ih]
      constructor
      · rintro ⟨before, after, shape, absent⟩
        refine ⟨name :: before, after, by rw [shape]; rfl, ?_⟩
        intro found
        rcases List.mem_cons.mp found with first | later
        · exact same first.symm
        · exact absent later
      · rintro ⟨before, after, shape, absent⟩
        cases before with
        | nil => exact (same (List.cons.inj shape).1).elim
        | cons head others =>
          exact ⟨others, after, (List.cons.inj shape).2,
            fun found => absent (List.mem_cons_of_mem _ found)⟩

theorem value_missing (arguments : List String) (wanted : String) (error : Error) :
    value arguments wanted = .error error ↔ Ends arguments wanted ∧ error = .missing wanted := by
  induction arguments with
  | nil =>
    constructor
    · intro found
      cases found
    · rintro ⟨⟨before, shape, -⟩, -⟩
      cases before <;> cases shape
  | cons name rest ih =>
    unfold value
    by_cases same : name = wanted
    · subst same
      cases rest with
      | nil =>
        constructor
        · intro found
          simp only [beq_self_eq_true, ↓reduceIte, Except.error.injEq] at found
          exact ⟨⟨[], rfl, List.not_mem_nil⟩, found.symm⟩
        · rintro ⟨-, named⟩
          simp [named]
      | cons next tail =>
        constructor
        · intro found
          simp at found
        · rintro ⟨⟨before, shape, absent⟩, -⟩
          cases before with
          | nil => cases shape
          | cons head others =>
            have first : name = head := (List.cons.inj shape).1
            exact (absent (first ▸ List.mem_cons_self)).elim
    · simp only [beq_iff_eq, same, ↓reduceIte]
      rw [ih]
      constructor
      · rintro ⟨⟨before, shape, absent⟩, named⟩
        refine ⟨⟨name :: before, by rw [shape]; rfl, ?_⟩, named⟩
        intro found
        rcases List.mem_cons.mp found with first | later
        · exact same first.symm
        · exact absent later
      · rintro ⟨⟨before, shape, absent⟩, named⟩
        cases before with
        | nil => exact (same (List.cons.inj shape).1).elim
        | cons head others =>
          exact ⟨⟨others, (List.cons.inj shape).2,
            fun found => absent (List.mem_cons_of_mem _ found)⟩, named⟩

def required (arguments : List String) (name : String) : Except Error String := do
  let some text ← value arguments name | .error (.missing name)
  if (trimControlLine text).isEmpty || text.startsWith "--" then .error (.invalid name text)
  else return text

def unsigned (arguments : List String) (name : String) (width fallback : Nat) : Except Error Nat := do
  match ← value arguments name with
  | none => return fallback
  | some text =>
    let some number := Digits.natural text | .error (.invalid name text)
    if number < 2 ^ width then return number else .error (.invalid name text)

def side (arguments : List String) : Except Error Coordinate := do
  match ← value arguments "--side" with
  | none => return ⟨1024, by decide⟩
  | some text =>
    let some number := Digits.natural text | .error (.invalid "--side" text)
    let some coordinate := Coordinate.checked number | .error (.invalid "--side" text)
    return coordinate

def profile (text : String) : Except Error ResearchProfile :=
  match text with
  | "ranked" => .ok .ranked | "primitive" => .ok .primitive
  | "boundary-credit" => .ok .boundaryCredit | "annealed" => .ok .annealed
  | "spatial" => .ok .spatial | _ => .error (.invalid "--research-profile" text)

def ProfileSpelled (text : String) (selected : ResearchProfile) : Prop :=
  (text = "ranked" ∧ selected = .ranked) ∨ (text = "primitive" ∧ selected = .primitive) ∨
    (text = "boundary-credit" ∧ selected = .boundaryCredit) ∨
    (text = "annealed" ∧ selected = .annealed) ∨ (text = "spatial" ∧ selected = .spatial)

theorem profile_spelled (text : String) (selected : ResearchProfile) :
    profile text = .ok selected ↔ ProfileSpelled text selected := by
  unfold profile ProfileSpelled
  split <;> cases selected <;> simp_all

theorem profile_refused (text : String) (error : Error) :
    profile text = .error error ↔
      (∀ selected, ¬ ProfileSpelled text selected) ∧
        error = .invalid "--research-profile" text := by
  unfold profile ProfileSpelled
  split <;> simp_all [eq_comm]

def criterion (arguments : List String) : Except Error (Option Features.Criterion) := do
  match ← value arguments "--criterion" with
  | none => return none
  | some "discounted" => return some .discounted
  | some "average-reward" => return some .differential
  | some text => .error (.invalid "--criterion" text)

def planningValue (text : String) : Except Error Features.PlanningSelection :=
  match Features.PlanningSelection.parse text with
  | some selection => .ok selection
  | Option.none => .error (.invalid "--planning" text)

def planningSelection (arguments : List String) : Except Error Features.PlanningSelection := do
  match ← value arguments "--planning" with
  | none => return .expectation
  | some text => planningValue text

theorem planningSelection_absent (arguments : List String)
    (absent : value arguments "--planning" = .ok none) :
    planningSelection arguments = .ok .expectation := by
  simp [planningSelection, absent]
  rfl

theorem planningSelection_provided (arguments : List String) (text : String)
    (provided : value arguments "--planning" = .ok (some text)) :
    planningSelection arguments = planningValue text := by
  simp [planningSelection, provided]
  rfl

def stepOrderValue (text : String) : Except Error StepOrder :=
  match StepOrder.parse text with
  | some order => .ok order
  | Option.none => .error (.invalid "--step-order" text)

def stepOrder (arguments : List String) : Except Error StepOrder := do
  match ← value arguments "--step-order" with
  | none => return .learnThenAct
  | some text => stepOrderValue text

theorem stepOrderValue_iff (text : String) (order : StepOrder) :
    stepOrderValue text = .ok order ↔ StepOrder.Spelled text order := by
  rw [← StepOrder.parse_spelled]
  unfold stepOrderValue
  cases StepOrder.parse text with
  | none => simp
  | some found => simp

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

theorem stepOrder_iff (arguments : List String) (order : StepOrder) :
    stepOrder arguments = .ok order ↔
      ("--step-order" ∉ arguments ∧ order = .learnThenAct) ∨
        ∃ text, Follows arguments "--step-order" text ∧ StepOrder.Spelled text order := by
  simp only [← value_absent, ← value_follows]
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

theorem stepOrder_refused (arguments : List String) (error : Error) :
    stepOrder arguments = .error error ↔
      (Ends arguments "--step-order" ∧ error = .missing "--step-order") ∨
        ∃ text, Follows arguments "--step-order" text ∧
          (∀ order, ¬ StepOrder.Spelled text order) ∧ error = .invalid "--step-order" text := by
  simp only [← value_missing, ← value_follows]
  unfold stepOrder
  cases read : value arguments "--step-order" with
  | error refusal => simp [bind, Except.bind]
  | ok found =>
    cases found with
    | none => simp [bind, Except.bind, pure, Except.pure]
    | some text =>
      simp only [bind, Except.bind, reduceCtorEq, false_or, Except.ok.injEq, Option.some.injEq,
        exists_eq_left']
      exact stepOrderValue_refused text error

theorem stepOrder_absent (arguments : List String)
    (absent : value arguments "--step-order" = .ok none) :
    stepOrder arguments = .ok .learnThenAct := by
  simp [stepOrder, absent]
  rfl

theorem stepOrder_provided (arguments : List String) (text : String)
    (provided : value arguments "--step-order" = .ok (some text)) :
    stepOrder arguments = stepOrderValue text := by
  simp [stepOrder, provided]
  rfl

structure Common where
  profile : ResearchProfile
  world : WorldConfig
  steps : UInt64
  goals : UInt64
  cycles : UInt64
  planning : Features.PlanningSelection

structure Streaming where
  common : Common
  attempts : UInt64
  criterion : Option Features.Criterion
  checkpoint : Option String
  checkpointEvery : UInt32
  baseline : Bool
  telemetry : Bool
  csv : Option String
  controlStdin : Bool
  runId : UInt64
  agentEpoch : UInt64
  newAgentEpoch : UInt64
  cleared : Bool
  order : StepOrder

inductive Demo where
  | streaming (options : Streaming)
  | ansi (common : Common) (period : Word.Count)

def defaultSeed : UInt64 := 42

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

def visitsFlags : List (String × Bool) :=
  [("--seed", true), ("--side", true), ("--steps", true), ("--visits", true),
    ("--target-x", true), ("--target-y", true), ("--research-profile", true),
    ("--planning", true), ("--step-order", true), ("--checkpoint", true),
    ("--checkpoint-every", true), ("--comparator", false)]

structure Visits where
  profile : ResearchProfile
  world : WorldConfig
  cap : UInt64
  visits : Nat
  target : Position
  planning : Features.PlanningSelection
  order : StepOrder
  checkpoint : Option String
  checkpointEvery : UInt32
  comparator : Bool

def requiredCoordinate (arguments : List String) (name : String) : Except Error Coordinate := do
  let text ← required arguments name
  let some number := Digits.integer text | .error (.invalid name text)
  let some coordinate := Coordinate.checked number | .error (.invalid name text)
  return coordinate

def visits (arguments : List String) : Except Error Visits := do
  scan visitsFlags arguments []
  if arguments.contains "--checkpoint-every" && !(arguments.contains "--checkpoint") then
    .error (.missing "--checkpoint")
  let comparator := arguments.contains "--comparator"
  if comparator then
    for name in ["--planning", "--step-order", "--checkpoint", "--checkpoint-every"] do
      if arguments.contains name then
        .error (.invalid name "unsupported with --comparator")
  let selected ← profile (← required arguments "--research-profile")
  if !selected.resumable && arguments.contains "--checkpoint" then
    .error (.invalid "--checkpoint" "selected research profile has no checkpoint encoding")
  let planning ← planningSelection arguments
  let order ← stepOrder arguments
  let visitsText ← required arguments "--visits"
  let some count := Digits.natural visitsText | .error (.invalid "--visits" visitsText)
  if count == 0 || 2 ^ 64 ≤ count then .error (.invalid "--visits" visitsText)
  let x ← requiredCoordinate arguments "--target-x"
  let y ← requiredCoordinate arguments "--target-y"
  let seed := (← unsigned arguments "--seed" 64 defaultSeed.toNat).toUInt64
  let coordinate ← side arguments
  let steps := (← unsigned arguments "--steps" 64 3000).toUInt64
  let checkpointEvery := (← unsigned arguments "--checkpoint-every" 32 4).toUInt32
  let checkpoint ← value arguments "--checkpoint"
  let world ← (WorldConfig.standard seed coordinate).mapError Error.world
  return ⟨selected, world, steps, count, ⟨x, y⟩, planning, order, checkpoint, checkpointEvery,
    comparator⟩

def Streaming.campaign (options : Streaming) : CampaignSpec :=
  ⟨options.common.steps, options.attempts, options.common.goals, options.common.cycles⟩

inductive Dispatch where
  | demo (options : Demo)
  | external (command : { selected : Command // selected ≠ .demo }) (arguments : List String)

def dispatch (arguments : List String) : Except Error Dispatch := do
  let selected ← command arguments
  if h : selected = .demo then return .demo (← demo arguments)
  else return .external ⟨selected, h⟩ arguments

end Acorn.Host.Cli
