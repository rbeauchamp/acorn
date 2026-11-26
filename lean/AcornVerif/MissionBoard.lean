import Lean.Data.Json
import AcornVerif.Landings

namespace AcornVerif.MissionBoard

open Lean (Json toJson)

private def pullFields : String :=
  "number merged baseRefName mergedAt author { __typename login } mergedBy { login } " ++
  "mergeCommit { oid message }"

def query : String :=
  "query($endCursor: String) { repository(owner: \"rbeauchamp\", name: \"acorn\") { " ++
  "owner { login } defaultBranchRef { name } " ++
  "issues(labels: [\"mission\"], states: [OPEN, CLOSED], first: 100, after: $endCursor, " ++
  "orderBy: {field: CREATED_AT, direction: ASC}) { totalCount " ++
  "pageInfo { hasNextPage endCursor } " ++
  "nodes { number title state stateReason updatedAt lastEditedAt body author { login } " ++
  "editor { login } labels(first: 100) { totalCount nodes { name } } " ++
  "timelineItems(itemTypes: [CLOSED_EVENT], last: 1) { nodes { ... on ClosedEvent { closer { " ++
  "__typename ... on PullRequest { " ++ pullFields ++ " } " ++
  "... on Commit { oid associatedPullRequests(first: 100) { totalCount " ++
  "nodes { " ++ pullFields ++ " } } } } } } } } } } }"

structure Account where
  kind : String
  login : String
  deriving DecidableEq

structure MergeCommit where
  oid : String
  message : String
  deriving DecidableEq

structure Closer where
  number : Nat
  merged : Bool
  base : String
  mergedAt : Option String
  author : Option Account
  mergedBy : Option String
  commit : Option MergeCommit
  deriving DecidableEq

def Closer.squashes (p : Closer) (oid : String) : Bool :=
  p.merged && p.commit.any (·.oid == oid)

def squashedBy (oid : String) (pulls : List Closer) : Option Closer :=
  match pulls.find? (·.squashes oid) with
  | none => none
  | some p => if pulls.all (fun q => !q.squashes oid || decide (q = p)) then some p else none

theorem squashedBy_iff {oid : String} {pulls : List Closer} {p : Closer} :
    squashedBy oid pulls = some p ↔
      p ∈ pulls ∧ p.squashes oid = true ∧ ∀ q ∈ pulls, q.squashes oid = true → q = p := by
  have squashing {first : Closer} (found : pulls.find? (·.squashes oid) = some first) :
      first ∈ pulls ∧ first.squashes oid = true :=
    ⟨List.mem_of_find?_eq_some found,
      List.find?_some (p := fun q : Closer => q.squashes oid) found⟩
  unfold squashedBy
  constructor
  · intro named
    split at named
    · simp at named
    · rename_i first found
      split at named
      · rename_i only
        simp only [Option.some.injEq] at named
        subst named
        refine ⟨(squashing found).1, (squashing found).2, fun q member squash => ?_⟩
        have checked := List.all_eq_true.mp only q member
        simpa [squash] using checked
      · simp at named
  · rintro ⟨member, squash, only⟩
    cases found : pulls.find? (·.squashes oid) with
    | none => exact absurd squash (by simpa using List.find?_eq_none.mp found p member)
    | some first =>
      have same : first = p := only first (squashing found).1 (squashing found).2
      subst same
      have every : pulls.all (fun q => !q.squashes oid || decide (q = first)) = true :=
        List.all_eq_true.mpr fun q inside => by
          cases held : q.squashes oid with
          | false => simp
          | true => simp [only q inside held]
      simp [every]

structure Mission where
  number : Nat
  title : String
  isOpen : Bool
  completed : Bool
  updatedAt : String
  lastEditedAt : Option String
  body : String
  author : Option String
  editor : Option String
  labels : List String
  closer : Option Closer
  deriving DecidableEq

structure Page where
  total : Nat
  more : Bool
  owner : String
  branch : String
  missions : List Mission
  deriving DecidableEq

structure Snapshot where
  owner : String
  branch : String
  missions : List Mission
  deriving DecidableEq

private def text (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

private def optional {α : Type} (j : Json) (key : String) (read : Json → Except String α) :
    Except String (Option α) := do
  match ← j.getObjVal? key with
  | .null => return none
  | value => return some (← read value)

private def login (j : Json) : Except String String := text j "login"

private def account (j : Json) : Except String Account :=
  return { kind := ← text j "__typename", login := ← login j }

private def mergeCommit (j : Json) : Except String MergeCommit :=
  return { oid := ← text j "oid", message := ← text j "message" }

private def pullRequest (value : Json) : Except String Closer :=
  return {
    number := ← (← value.getObjVal? "number").getNat?
    merged := ← (← value.getObjVal? "merged").getBool?
    base := ← text value "baseRefName"
    mergedAt := ← optional value "mergedAt" Json.getStr?
    author := ← optional value "author" account
    mergedBy := ← optional value "mergedBy" login
    commit := ← optional value "mergeCommit" mergeCommit }

private def closer (number : Nat) (j : Json) : Except String (Option Closer) := do
  match ← optional j "closer" pure with
  | none => return none
  | some value =>
    let kind ← text value "__typename"
    if kind == "PullRequest" then return some (← pullRequest value)
    else if kind == "Commit" then
      let associated ← value.getObjVal? "associatedPullRequests"
      let nodes ← (← associated.getObjVal? "nodes").getArr?
      unless (← (← associated.getObjVal? "totalCount").getNat?) == nodes.size do
        throw s!"issue {number}: the pull requests of its closing commit did not fit one read"
      return squashedBy (← text value "oid") (← nodes.toList.mapM pullRequest)
    else return none

private def mission (j : Json) : Except String Mission := do
  let labels ← j.getObjVal? "labels"
  let labelNodes ← (← labels.getObjVal? "nodes").getArr?
  let number ← (← j.getObjVal? "number").getNat?
  unless (← (← labels.getObjVal? "totalCount").getNat?) == labelNodes.size do
    throw s!"issue {number}: its labels did not fit one read"
  let closings ← (← (← j.getObjVal? "timelineItems").getObjVal? "nodes").getArr?
  let closing ← match closings.toList with
    | [] => pure none
    | [event] => closer number event
    | _ => throw s!"issue {number}: more than the one closing event asked for"
  return {
    number
    title := ← text j "title"
    isOpen := (← text j "state") == "OPEN"
    completed := (← optional j "stateReason" Json.getStr?) == some "COMPLETED"
    updatedAt := ← text j "updatedAt"
    lastEditedAt := ← optional j "lastEditedAt" Json.getStr?
    body := ← text j "body"
    author := ← optional j "author" login
    editor := ← optional j "editor" login
    labels := ← labelNodes.toList.mapM (fun node => text node "name")
    closer := closing }

private def page (j : Json) : Except String Page := do
  if let .ok errors := j.getObjVal? "errors" then
    throw s!"GitHub reported errors: {errors.compress}"
  let repository ← (← j.getObjVal? "data").getObjVal? "repository"
  let issues ← repository.getObjVal? "issues"
  let nodes ← (← issues.getObjVal? "nodes").getArr?
  return {
    total := ← (← issues.getObjVal? "totalCount").getNat?
    more := ← (← (← issues.getObjVal? "pageInfo").getObjVal? "hasNextPage").getBool?
    owner := ← login (← repository.getObjVal? "owner")
    branch := ← text (← repository.getObjVal? "defaultBranchRef") "name"
    missions := ← nodes.toList.mapM mission }

def Complete (pages : List Page) (total : Nat) (owner branch : String) : Prop :=
  0 < total ∧
  (∀ p ∈ pages, p.total = total ∧ p.owner = owner ∧ p.branch = branch) ∧
  pages.map (·.more) = List.replicate (pages.length - 1) true ++ [false] ∧
  ((pages.flatMap (·.missions)).map (·.number)).Nodup ∧
  (pages.flatMap (·.missions)).length = total

instance (pages : List Page) (total : Nat) (owner branch : String) :
    Decidable (Complete pages total owner branch) := by
  unfold Complete; exact inferInstance

def assemble (pages : List Page) : Except String Snapshot :=
  match pages with
  | [] => .error "GitHub returned no pages"
  | first :: rest =>
    if Complete (first :: rest) first.total first.owner first.branch then
      .ok { owner := first.owner, branch := first.branch
            missions := (first :: rest).flatMap (·.missions) }
    else .error "the read of GitHub's pages is partial or inconsistent"

theorem assemble_complete {pages : List Page} {s : Snapshot} (read : assemble pages = .ok s) :
    ∃ total, Complete pages total s.owner s.branch ∧ s.missions = pages.flatMap (·.missions) := by
  unfold assemble at read
  split at read
  · simp at read
  · rename_i first rest
    split at read
    · rename_i complete
      simp only [Except.ok.injEq] at read
      subst read
      exact ⟨first.total, complete, rfl⟩
    · simp at read

def agree (first second : List Page) : Except String Snapshot := do
  let a ← assemble first
  let b ← assemble second
  if a = b then return a else throw "GitHub's missions changed between the two reads; read again"

theorem agree_both {first second : List Page} {s : Snapshot} (read : agree first second = .ok s) :
    assemble first = .ok s ∧ assemble second = .ok s := by
  unfold agree at read
  cases a : assemble first with
  | error e => simp [a, bind, Except.bind] at read
  | ok x =>
    cases b : assemble second with
    | error e => simp [a, b, bind, Except.bind] at read
    | ok y =>
      simp only [a, b, bind, Except.bind] at read
      split at read
      · rename_i same
        simp only [pure, Except.pure, Except.ok.injEq] at read
        subst read
        subst same
        exact ⟨rfl, rfl⟩
      · simp [throw, throwThe, MonadExcept.throw] at read

def kindLabels : List String :=
  ["mission:proof", "mission:contract", "mission:world", "mission:prior-art"]

def Mission.kinds (m : Mission) : List String := kindLabels.filter m.labels.contains

def contractOf (body : String) : Option String :=
  let lines := (body.splitOn "\n").map fun line => (line.dropEndWhile (· == '\r')).toString
  match lines.dropWhile (fun line => line.trimAscii.toString != "## Mission contract") with
  | [] => none
  | _ :: rest =>
    let contract := "\n".intercalate (rest.takeWhile (fun line => !line.startsWith "## "))
    let trimmed := contract.trimAscii.toString
    if trimmed.isEmpty then none else some trimmed

inductive ContractState
  | frozen
  | proposed
  | edited
  deriving DecidableEq

def Mission.issueState (m : Mission) (owner : String) : ContractState :=
  if m.kinds.isEmpty || (contractOf m.body).isNone then .proposed
  else match m.editor with
    | some editor => if editor = owner then .frozen else .edited
    | none => .frozen

structure TargetRow where
  mission : Nat
  name : Lean.Name
  provedBy : Option Lean.Name

def targetRowsOf (record : List Targets.Landing) : List TargetRow :=
  Targets.registry.map fun target => {
    mission := target.mission, name := target.name
    provedBy := (record.find? (·.target == target.name)).map (·.provedBy) }

theorem targetRowsOf_proved {record : List Targets.Landing} {row : TargetRow} {proof : Lean.Name}
    (member : row ∈ targetRowsOf record) (proved : row.provedBy = some proof) :
    (∃ landing ∈ record, landing.target = row.name ∧ landing.provedBy = proof) ∧
      ∃ target ∈ Targets.registry,
        target.mission = row.mission ∧ target.name = row.name ∧ target.statement := by
  simp only [targetRowsOf, List.mem_map] at member
  obtain ⟨target, registered, rfl⟩ := member
  simp only [Option.map_eq_some_iff] at proved
  obtain ⟨landing, found, rfl⟩ := proved
  have named : landing.target = target.name :=
    eq_of_beq (List.find?_some (p := fun entry : Targets.Landing => entry.target == target.name)
      found)
  have holds : Targets.statementOf target.name := named ▸ landing.proof
  exact ⟨⟨landing, List.mem_of_find?_eq_some found, named, rfl⟩, target, registered, rfl, rfl,
    (Targets.statementOf_name target registered).mp holds⟩

theorem targetRowsOf_shown {record : List Targets.Landing} {landing : Targets.Landing}
    (member : landing ∈ record) :
    ∃ row ∈ targetRowsOf record, row.name = landing.target ∧ row.provedBy.isSome = true := by
  obtain ⟨target, registered, named, _⟩ := landing.proves
  refine ⟨_, List.mem_map.mpr ⟨target, registered, rfl⟩, named, ?_⟩
  simp only [Option.isSome_map, List.find?_isSome]
  exact ⟨landing, member, by simp [named]⟩

def Mission.contractState (m : Mission) (owner : String) : ContractState :=
  if Targets.registry.any (·.mission == m.number) then .frozen else m.issueState owner

theorem Mission.contractState_targets {m : Mission} {owner : String}
    (held : ∃ target ∈ Targets.registry, target.mission = m.number) :
    m.contractState owner = .frozen := by
  obtain ⟨target, member, same⟩ := held
  have found : Targets.registry.any (·.mission == m.number) = true :=
    List.any_eq_true.mpr ⟨target, member, by simp [same]⟩
  simp only [Mission.contractState, found, ite_true]

theorem Mission.contractState_issue {m : Mission} {owner : String}
    (none : ∀ target ∈ Targets.registry, target.mission ≠ m.number) :
    m.contractState owner = m.issueState owner := by
  have absent : Targets.registry.any (·.mission == m.number) = false := by
    simp only [List.any_eq_false, beq_iff_eq]
    exact none
  simp only [Mission.contractState, absent, Bool.false_eq_true, ite_false]

def agentChar (c : Char) : Bool :=
  c.isAlphanum || [' ', '.', '_', '+', '-', '(', ')', '/'].contains c

def admitName (name : String) : Option String :=
  if !name.isEmpty && name.length ≤ 64 && name.toList.all agentChar then some name else none

def bareLine (line : String) : String :=
  let trimmed := line.trimAscii.toString
  if trimmed.startsWith "- " then (trimmed.drop 2).toString else trimmed

def agentName (line : String) : Option String :=
  if (bareLine line).startsWith "Agent: " then admitName ((bareLine line).drop 7).toString else none

theorem agentName_closed {line name : String} (named : agentName line = some name) :
    ∀ c ∈ name.toList, agentChar c = true := by
  unfold agentName at named
  split at named
  · unfold admitName at named
    split at named
    · rename_i admitted
      simp only [Option.some.injEq] at named
      subst named
      simp only [Bool.and_eq_true, List.all_eq_true] at admitted
      exact admitted.2
    · simp at named
  · simp at named

def gateLine : String := "gate: every merge check passed"

structure Landed where
  mission : Nat
  title : String
  pullRequest : Nat
  account : Option Account
  agents : List String
  mergedAt : Option String
  commit : String

inductive Withheld
  | notCompleted
  | noMerge
  | otherBranch
  | otherMerger
  | noGateResult

def Accepted (m : Mission) (owner branch : String) : Prop :=
  m.completed = true ∧ ∃ c, m.closer = some c ∧ c.merged = true ∧ c.base = branch ∧
    c.mergedBy = some owner ∧ ∃ commit, c.commit = some commit ∧ commit.message.contains gateLine

def Mission.landing (m : Mission) (owner branch : String) : Except Withheld Landed :=
  if !m.completed then .error .notCompleted else
  match m.closer with
  | none => .error .noMerge
  | some c =>
    if !c.merged then .error .noMerge
    else if c.base != branch then .error .otherBranch
    else if c.mergedBy != some owner then .error .otherMerger
    else match c.commit with
      | none => .error .noGateResult
      | some commit =>
        if !commit.message.contains gateLine then .error .noGateResult
        else .ok {
          mission := m.number, title := m.title, pullRequest := c.number, account := c.author
          agents := ((commit.message.splitOn "\n").filterMap agentName).eraseDups
          mergedAt := c.mergedAt, commit := commit.oid }

theorem Mission.landing_accepted {m : Mission} {owner branch : String} {l : Landed}
    (landed : m.landing owner branch = .ok l) : Accepted m owner branch ∧ l.mission = m.number := by
  unfold Mission.landing at landed
  split at landed
  · simp at landed
  · rename_i completed
    split at landed
    · simp at landed
    · rename_i c closing
      split at landed
      · simp at landed
      · rename_i merged
        split at landed
        · simp at landed
        · rename_i base
          split at landed
          · simp at landed
          · rename_i mergedBy
            split at landed
            · simp at landed
            · rename_i commit found
              split at landed
              · simp at landed
              · rename_i contains
                simp only [Except.ok.injEq] at landed
                subst landed
                simp only [Bool.not_eq_true', Bool.not_eq_false] at completed merged contains
                simp only [bne_iff_ne, ne_eq, Decidable.not_not] at base mergedBy
                exact ⟨⟨completed, c, closing, merged, base, mergedBy, commit, found, contains⟩,
                  rfl⟩

theorem Mission.landing_complete {m : Mission} {owner branch : String}
    (accepted : Accepted m owner branch) :
    ∃ l, m.landing owner branch = .ok l ∧ l.mission = m.number := by
  obtain ⟨completed, c, closing, merged, base, mergedBy, commit, found, contains⟩ := accepted
  subst base
  simp [Mission.landing, completed, closing, merged, mergedBy, found, contains]

def landedOf (s : Snapshot) : List Landed :=
  (s.missions.filter (!·.isOpen)).filterMap fun m =>
    match m.landing s.owner s.branch with
    | .ok l => some l
    | .error _ => none

theorem landedOf_accepted {s : Snapshot} {l : Landed} (landed : l ∈ landedOf s) :
    ∃ m ∈ s.missions, m.number = l.mission ∧ Accepted m s.owner s.branch := by
  simp only [landedOf, List.mem_filterMap, List.mem_filter] at landed
  obtain ⟨m, ⟨member, _⟩, record⟩ := landed
  split at record
  · rename_i r result
    simp only [Option.some.injEq] at record
    subst record
    obtain ⟨accepted, same⟩ := Mission.landing_accepted result
    exact ⟨m, member, same.symm, accepted⟩
  · simp at record

theorem landedOf_complete {s : Snapshot} {m : Mission} (member : m ∈ s.missions)
    (closed : m.isOpen = false) (accepted : Accepted m s.owner s.branch) :
    ∃ l ∈ landedOf s, l.mission = m.number := by
  obtain ⟨l, landed, number⟩ := Mission.landing_complete accepted
  refine ⟨l, ?_, number⟩
  simp only [landedOf, List.mem_filterMap, List.mem_filter]
  exact ⟨m, ⟨member, by simp [closed]⟩, by simp [landed]⟩

structure Credit (α : Type) where
  holder : α
  missions : List Nat

def credits {α : Type} [DecidableEq α] (names : Landed → List α) (landed : List Landed) :
    List (Credit α) :=
  let rows := ((landed.flatMap names).eraseDups).map fun holder =>
    ({ holder, missions := (landed.filter (fun l => decide (holder ∈ names l))).map (·.mission) } :
      Credit α)
  rows.mergeSort fun a b => decide (b.missions.length ≤ a.missions.length)

theorem credited_landed {α : Type} [DecidableEq α] {names : Landed → List α}
    {landed : List Landed} {c : Credit α} {mission : Nat} (row : c ∈ credits names landed)
    (counted : mission ∈ c.missions) :
    ∃ l ∈ landed, l.mission = mission ∧ c.holder ∈ names l := by
  simp only [credits, List.mem_mergeSort, List.mem_map] at row
  obtain ⟨holder, _, same⟩ := row
  subst same
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at counted
  obtain ⟨l, ⟨member, name⟩, number⟩ := counted
  exact ⟨l, member, number, name⟩

theorem landed_credited {α : Type} [DecidableEq α] {names : Landed → List α}
    {landed : List Landed} {l : Landed} {holder : α} (member : l ∈ landed)
    (name : holder ∈ names l) :
    ∃ c ∈ credits names landed, c.holder = holder ∧ l.mission ∈ c.missions := by
  refine ⟨{ holder
            missions := (landed.filter (fun l => decide (holder ∈ names l))).map (·.mission) },
    ?_, rfl, ?_⟩
  · simp only [credits, List.mem_mergeSort, List.mem_map]
    refine ⟨holder, ?_, rfl⟩
    rw [List.mem_eraseDups]
    exact List.mem_flatMap.mpr ⟨l, member, name⟩
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨l, ⟨member, name⟩, rfl⟩

theorem credited_accepted {α : Type} [DecidableEq α] {names : Landed → List α} {s : Snapshot}
    {c : Credit α} {mission : Nat} (row : c ∈ credits names (landedOf s))
    (counted : mission ∈ c.missions) :
    ∃ m ∈ s.missions, m.number = mission ∧ Accepted m s.owner s.branch := by
  obtain ⟨l, member, same, _⟩ := credited_landed row counted
  obtain ⟨m, found, number, accepted⟩ := landedOf_accepted member
  exact ⟨m, found, number.trans same, accepted⟩

theorem accepted_credited {α : Type} [DecidableEq α] {names : Landed → List α} {s : Snapshot}
    {m : Mission} (member : m ∈ s.missions) (closed : m.isOpen = false)
    (accepted : Accepted m s.owner s.branch) :
    ∃ l ∈ landedOf s, l.mission = m.number ∧ ∀ holder ∈ names l,
      ∃ c ∈ credits names (landedOf s), c.holder = holder ∧ m.number ∈ c.missions := by
  obtain ⟨l, landed, number⟩ := landedOf_complete member closed accepted
  refine ⟨l, landed, number, fun holder name => ?_⟩
  rw [← number]
  exact landed_credited landed name

def inert (c : Char) : Bool :=
  c.isAlphanum || [' ', '.', ',', ':', '(', ')', '\'', '"', '-', '?', '/', '=', '+', '%'].contains c

def escape (s : String) : String :=
  String.ofList <| s.toList.flatMap fun c =>
    if inert c then [c] else '&' :: '#' :: (Nat.toDigits 10 c.toNat ++ [';'])

def escaped (c : Char) : Bool := inert c || c == '&' || c == '#' || c == ';' || c.isDigit

theorem escape_chars (s : String) : ∀ c ∈ (escape s).toList, escaped c = true := by
  intro c member
  simp only [escape, String.toList_ofList, List.mem_flatMap] at member
  obtain ⟨d, _, output⟩ := member
  split at output
  · rename_i kept
    simp only [List.mem_singleton] at output
    subst output
    simp [escaped, kept]
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at output
    rcases output with rfl | rfl | digit | rfl
    · decide
    · decide
    · simp [escaped, Nat.isDigit_of_mem_toDigits (by decide) (by decide) digit]
    · decide

def active : List Char := ['`', '|', '[', ']', '<', '>', '*', '_', '~', '\\', '!', '\n', '\r']

theorem escape_inert (s : String) : ∀ c ∈ (escape s).toList, c ∉ active := by
  intro c member known
  have allowed := escape_chars s c member
  simp only [active, List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd allowed (by decide)

private def repository : String := "https://github.com/rbeauchamp/acorn"

private def issueUrl (n : Nat) : String := s!"{repository}/issues/{n}"

private def pullUrl (n : Nat) : String := s!"{repository}/pull/{n}"

private def stateName : ContractState → String
  | .frozen => "frozen"
  | .proposed => "proposed"
  | .edited => "edited"

private def withheldName : Withheld → String
  | .notCompleted => "closed without being completed"
  | .noMerge => "no merged pull request closed it"
  | .otherBranch => "the pull request merged into another branch"
  | .otherMerger => "someone other than the owner merged the pull request"
  | .noGateResult => "the squash commit holds no passing gate result"

private def accountNames (l : Landed) : List (Option Account) := [l.account]

private def openOf (s : Snapshot) : List Mission := s.missions.filter (·.isOpen)

private def withheldOf (s : Snapshot) : List (Mission × Withheld) :=
  (s.missions.filter (!·.isOpen)).filterMap fun m =>
    match m.landing s.owner s.branch with
    | .ok _ => none
    | .error reason => some (m, reason)

private def optionJson (value : Option String) : Json :=
  match value with
  | some text => .str text
  | none => .null

private def missionsJson (missions : List Nat) : Json := toJson missions.toArray

private def accountJson (value : Option Account) : Json :=
  match value with
  | some a => Json.mkObj [("kind", .str a.kind), ("login", .str a.login)]
  | none => .null

def targetFile (name : Lean.Name) : String :=
  "lean/" ++ (name.getPrefix.toString (escape := false)).replace "." "/" ++ ".lean"

private def nameJson (value : Option Lean.Name) : Json :=
  optionJson (value.map (·.toString))

def boardJson (stamp : String) (record : List Targets.Landing) (s : Snapshot) : Json :=
  let landed := landedOf s
  Json.mkObj [
    ("authority", .str s!"GitHub ({repository}) is the record. This is a copy derived at \
      derived_at; it may lag GitHub and never overrides it."),
    ("derived_at", .str stamp),
    ("regenerate", .str s!"{repository}/blob/main/docs/missions.md#regenerating-the-board"),
    ("untrusted_fields", toJson #["title", "contract"]),
    ("open", toJson <| (openOf s).toArray.map fun m => Json.mkObj [
      ("number", toJson m.number), ("title", .str m.title), ("url", .str (issueUrl m.number)),
      ("kinds", toJson m.kinds.toArray),
      ("contract_state", .str (stateName (m.contractState s.owner))),
      ("issue_state", .str (stateName (m.issueState s.owner))),
      ("contract", optionJson (contractOf m.body)), ("filed_by", optionJson m.author),
      ("last_edited_by", optionJson m.editor), ("last_edited_at", optionJson m.lastEditedAt)]),
    ("targets", toJson <| (targetRowsOf record).toArray.map fun row => Json.mkObj [
      ("mission", toJson row.mission), ("name", .str row.name.toString),
      ("file", .str (targetFile row.name)), ("proved_by", nameJson row.provedBy)]),
    ("landed", toJson <| landed.toArray.map fun l => Json.mkObj [
      ("mission", toJson l.mission), ("title", .str l.title), ("url", .str (issueUrl l.mission)),
      ("pull_request", .str (pullUrl l.pullRequest)), ("account", accountJson l.account),
      ("agents", toJson l.agents.toArray), ("merged_at", optionJson l.mergedAt),
      ("commit", .str l.commit)]),
    ("closed_without_landing", toJson <| (withheldOf s).toArray.map fun (m, reason) => Json.mkObj [
      ("mission", toJson m.number), ("title", .str m.title), ("url", .str (issueUrl m.number)),
      ("reason", .str (withheldName reason))]),
    ("credit", Json.mkObj [
      ("accounts", toJson <| (credits accountNames landed).toArray.map fun c => Json.mkObj [
        ("account", accountJson c.holder), ("missions", missionsJson c.missions)]),
      ("agents", toJson <| (credits (·.agents) landed).toArray.map fun c => Json.mkObj [
        ("agent", .str c.holder), ("missions", missionsJson c.missions)])])]

private def count (n : Nat) (one many : String) : String :=
  if n = 1 then s!"1 {one}" else s!"{n} {many}"

private def issueLink (n : Nat) : String := s!"[#{n}]({issueUrl n})"

private def pullLink (n : Nat) : String := s!"[#{n}]({pullUrl n})"

private def loginChar (c : Char) : Bool := c.isAlphanum || c == '-'

private def accountText (owner : String) (value : Option Account) : String :=
  match value with
  | none => "a deleted account"
  | some a =>
    let name := if a.kind == "User" && a.login.toList.all loginChar then
        s!"[{a.login}](https://github.com/{a.login})"
      else s!"{escape a.login} ({escape a.kind})"
    if a.login == owner then s!"{name} (owner)" else name

private def kindText (m : Mission) : String :=
  match m.kinds.map (fun kind => (kind.drop 8).toString) with
  | [] => "not yet given"
  | kinds => ", ".intercalate (kinds.map escape)

private def rows (lines : List String) : String := "\n".intercalate lines

private def stateText (m : Mission) (owner : String) : String :=
  let state := m.contractState owner
  let issue := m.issueState owner
  if state = issue then stateName state else s!"{stateName state} (issue {stateName issue})"

private def openSection (s : Snapshot) : String :=
  match openOf s with
  | [] => "No mission is open at this time."
  | missions =>
    let table := missions.map fun m =>
      s!"| {issueLink m.number} | {escape m.title} | {kindText m} | {stateText m s.owner} |"
    rows ([s!"{count missions.length "mission is" "missions are"} open.", "",
      "| Mission | What it asks | Kind | Contract |", "|---|---|---|---|"] ++ table ++ ["",
      "A *frozen* contract is accepted and may not be weakened. A *proposed* one has not been \
      accepted yet, so do not start on it. An *edited* one was last changed by someone other than \
      the owner, so its text may not be what was accepted; do not rely on it until the owner has \
      edited it again. A mission with [targets](#targets) is frozen whatever its issue says, \
      because its statements are in the repository, where only the owner merges a change to \
      them. Where its issue alone would read otherwise the table adds that in brackets: what \
      such a mission keeps in its issue, such as the files a pull request may change, is only \
      as reliable as the issue."])

private def pathChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '/' || c == '.'

private def fileText (name : Lean.Name) : String :=
  let file := targetFile name
  if file.toList.all pathChar then s!"[{escape file}](../{file})" else escape file

private def targetSection (record : List Targets.Landing) : String :=
  match targetRowsOf record with
  | [] => "No target is registered."
  | targets =>
    let table := targets.map fun row =>
      s!"| {issueLink row.mission} | {escape row.name.toString} | {fileText row.name} | \
        {(row.provedBy.map fun proof => escape proof.toString).getD "not yet"} |"
    rows ([s!"{count targets.length "target is" "targets are"} registered.", "",
      "| Mission | Target | File | Proved by |", "|---|---|---|---|"] ++ table)

private def landedSection (s : Snapshot) : String :=
  match landedOf s with
  | [] => "No mission has landed yet."
  | landed =>
    let table := landed.map fun l =>
      s!"| {issueLink l.mission} | {escape l.title} | {pullLink l.pullRequest} | \
        {accountText s.owner l.account} | {", ".intercalate (l.agents.map escape)} | \
        {escape ((l.mergedAt.getD "").take 10).toString} |"
    rows (["| Mission | What it asked | Pull request | Account | Agent | Merged |",
      "|---|---|---|---|---|---|"] ++ table)

private def withheldSection (s : Snapshot) : String :=
  match withheldOf s with
  | [] => ""
  | withheld =>
    let lines := withheld.map fun (m, reason) =>
      s!"- {issueLink m.number} {escape m.title}: {withheldName reason}."
    rows (["", "", "Closed without a landed result, so these earn no credit:", ""] ++ lines)

private def missionList (missions : List Nat) : String :=
  ", ".intercalate (missions.map issueLink)

private def creditSection (s : Snapshot) : String :=
  let landed := landedOf s
  match credits accountNames landed with
  | [] => "Nobody holds credit yet, because no mission has landed."
  | accounts =>
    let accountRows := accounts.map fun c =>
      s!"| {accountText s.owner c.holder} | {c.missions.length} | {missionList c.missions} |"
    let agentRows := (credits (·.agents) landed).map fun c =>
      s!"| {escape c.holder} | {c.missions.length} | {missionList c.missions} |"
    let agentTable := if agentRows.isEmpty then
        ["", "No landed pull request has named an agent yet."]
      else ["", "| Agent | Landed missions | Which |", "|---|---|---|"] ++ agentRows
    rows (["| Account | Landed missions | Which |", "|---|---|---|"] ++ accountRows ++ agentTable)

def boardMarkdown (stamp : String) (record : List Targets.Landing) (s : Snapshot) : String :=
  rows [
    "# Mission board", "",
    s!"This page is a copy of what GitHub records about Acorn's missions, derived at {stamp}. \
      GitHub is the record: this copy may lag it and never overrides it. For the current state, \
      see the [open missions on GitHub]({repository}/issues?q=is%3Aopen+label%3Amission). \
      [Regenerating the board](missions.md#regenerating-the-board) says how this page is made. \
      New to missions? [Start here](missions.md).", "",
    "## Open missions", "", openSection s, "",
    "## Targets", "",
    "A *target* is a statement that a mission is to prove, held in the repository as a Lean \
    definition. Every build has Lean read it against the current code, so it cannot stop making \
    sense unnoticed, and only the owner merges a change to it. A mission establishes its \
    statements by proving each of its targets, and a target is marked as proved once the \
    repository records the theorem that proves it. \
    [Missions](missions.md#step-3-read-the-contract) says how to find one and \
    [how to prove it](missions.md#step-5-do-the-work).", "",
    targetSection record, "",
    "## Landed missions", "",
    "A mission has landed when the pull request that closed it was merged into the default branch \
    by the repository's owner, with the passing result of the proof gate in its commit message.",
    "", landedSection s ++ withheldSection s, "",
    "## Credit", "",
    "Credit counts landed missions and nothing else: not claims, comments, opened pull requests, \
    runs or scores. The account is the GitHub account that opened the pull request; the agent is \
    what the merged commit's message names. Credit grants no repository privilege.", "",
    creditSection s, ""]

private def stampShape : List Char := "0000-00-00T00:00:00Z".toList

def validStamp (stamp : String) : Bool :=
  stamp.length == stampShape.length &&
    (stamp.toList.zip stampShape).all fun (c, shape) =>
      if shape == '0' then c.isDigit else c == shape

private def readPages (path : String) : IO (List Page) := do
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept ((← IO.ofExcept parsed.getArr?).toList.mapM page)

private def publish (path content : String) : IO Unit := do
  let staged := path ++ ".tmp"
  IO.FS.writeFile staged content
  IO.FS.rename staged path

def render (stamp first second base : String) : IO Unit := do
  unless validStamp stamp do
    throw (IO.userError s!"not a UTC time of the form {String.ofList stampShape}: {stamp}")
  unless first != second do throw (IO.userError "the two reads must be two separate files")
  let snapshot ← IO.ofExcept (agree (← readPages first) (← readPages second))
  publish (base ++ ".json") ((boardJson stamp landings snapshot).pretty ++ "\n")
  publish (base ++ ".md") (boardMarkdown stamp landings snapshot)

def run (args : List String) : IO UInt32 := do
  match args with
  | ["query"] =>
    IO.println query
    return 0
  | ["render", stamp, first, second, base] =>
    render stamp first second base
    return 0
  | _ =>
    IO.eprintln "usage: query | render <time> <first read> <second read> <path without extension>"
    return 2

end AcornVerif.MissionBoard
