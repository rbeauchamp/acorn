/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean.Data.Json

/-! # The mission board

GitHub is the record of Acorn's missions: an issue labelled `mission` is a mission, and a mission
has landed when a merged pull request closed it. This module derives the repository's copy of that
record, `docs/mission-board.md` and `docs/mission-board.json`, from pages of GitHub's GraphQL
interface. `docs/missions.md` gives the commands that run it.

The module imports only the toolchain and spawns no process: `gh api graphql --paginate --slurp`
fetches the pages, and the commands fetch them twice. It defines no root `main`, since the ownership
audit imports every non-executable module together; the commands run `run` from a one-line script.

What the proofs below establish about the executed definitions:

* A read is complete or refused (`assemble_complete`): every page reports one total, only the last
  page ends the pagination, and the missions read are that many distinct issues. Two reads must
  agree before anything is written (`agree_both`), which refuses most changes GitHub makes between
  pages; a label removed and restored between the two reads goes unseen.
* Credit follows acceptance (`credited_accepted`): every mission counted for an account or an agent
  is a mission of the read whose closing pull request was merged into the default branch by the
  repository's owner with the gate's final line on record. A claim, a comment, an open pull request
  and a run have no field here, so they earn nothing.
* Acceptance earns credit (`accepted_credited`): a closed mission of the read that meets `Accepted`
  is recorded as landed (`landedOf_complete`) and counted for each holder its record names. So an
  empty board cannot come from a `landing` that refuses what the condition accepts.
* Text that `escape` outputs holds no character of `active` (`escape_inert`), and `boardMarkdown`
  passes titles through it. An agent's name uses only a closed character set (`agentName_closed`).

What they do not establish: that GitHub answers truly; that a merge by the owner followed a passing
gate run (`CONTRIBUTING.md` makes that the rule and nothing on GitHub enforces it; the gate's final
line in the commit message is what the author pasted); or that the written files are not edited
afterwards.
-/

namespace AcornVerif.MissionBoard

open Lean (Json toJson)

/-- The one GraphQL query of a read. Its one `pageInfo` makes `gh api graphql --paginate` page the
issues, and ordering by creation keeps the pages stable while issues change. -/
def query : String :=
  "query($endCursor: String) { repository(owner: \"rbeauchamp\", name: \"acorn\") { " ++
  "owner { login } defaultBranchRef { name } " ++
  "issues(labels: [\"mission\"], states: [OPEN, CLOSED], first: 100, after: $endCursor, " ++
  "orderBy: {field: CREATED_AT, direction: ASC}) { totalCount pageInfo { hasNextPage endCursor } " ++
  "nodes { number title state stateReason updatedAt lastEditedAt body author { login } " ++
  "editor { login } labels(first: 100) { totalCount nodes { name } } " ++
  "timelineItems(itemTypes: [CLOSED_EVENT], last: 1) { nodes { ... on ClosedEvent { closer { " ++
  "__typename ... on PullRequest { number merged baseRefName mergedAt " ++
  "author { __typename login } mergedBy { login } mergeCommit { oid message } } } } } } } } } }"

/-- A GitHub account: its login, unique among accounts of its kind at one time, and that kind. -/
structure Account where
  /-- GitHub's type name for the account, such as `User` or `Bot`. -/
  kind : String
  /-- The account's current login. -/
  login : String
  deriving DecidableEq

/-- The squash commit a merge put on the base branch. -/
structure MergeCommit where
  /-- The commit's object id. -/
  oid : String
  /-- The commit's whole message, which later edits of the pull request cannot change. -/
  message : String
  deriving DecidableEq

/-- The pull request GitHub records as having closed an issue. -/
structure Closer where
  /-- The pull request's number. -/
  number : Nat
  /-- Whether it merged. -/
  merged : Bool
  /-- The branch it targets. -/
  base : String
  /-- When it merged, as GitHub gives the time. -/
  mergedAt : Option String
  /-- The account that opened it; none when that account was deleted. -/
  author : Option Account
  /-- The login of the account that merged it. -/
  mergedBy : Option String
  /-- The squash commit, once there is one. -/
  commit : Option MergeCommit
  deriving DecidableEq

/-- One issue labelled `mission`. There is no field for a claim, a comment or a run. -/
structure Mission where
  /-- The issue's number. -/
  number : Nat
  /-- The title, written by whoever filed or last edited it. -/
  title : String
  /-- Whether the issue is open. -/
  isOpen : Bool
  /-- Whether GitHub records it as closed because it was completed. -/
  completed : Bool
  /-- When GitHub last changed anything about it, which lets two reads differ when a label moved. -/
  updatedAt : String
  /-- When its text was last edited, if ever. -/
  lastEditedAt : Option String
  /-- The issue's text, written by whoever filed or last edited it. -/
  body : String
  /-- The login of the account that filed it. -/
  author : Option String
  /-- The login of the account that last edited its text, if any. -/
  editor : Option String
  /-- Its labels. -/
  labels : List String
  /-- The pull request GitHub records as having closed it, if one did. -/
  closer : Option Closer
  deriving DecidableEq

/-- One page of a read. -/
structure Page where
  /-- The number of missions GitHub reports in all. -/
  total : Nat
  /-- Whether GitHub reports another page. -/
  more : Bool
  /-- The login of the repository's owner. -/
  owner : String
  /-- The name of the default branch. -/
  branch : String
  /-- The missions on this page. -/
  missions : List Mission
  deriving DecidableEq

/-- A complete read of the repository's missions. -/
structure Snapshot where
  /-- The login of the repository's owner. -/
  owner : String
  /-- The name of the default branch. -/
  branch : String
  /-- Every mission, in order of creation. -/
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

private def closer (j : Json) : Except String (Option Closer) := do
  match ← optional j "closer" pure with
  | none => return none
  | some value =>
    unless (← text value "__typename") == "PullRequest" do return none
    return some {
      number := ← (← value.getObjVal? "number").getNat?
      merged := ← (← value.getObjVal? "merged").getBool?
      base := ← text value "baseRefName"
      mergedAt := ← optional value "mergedAt" Json.getStr?
      author := ← optional value "author" account
      mergedBy := ← optional value "mergedBy" login
      commit := ← optional value "mergeCommit" mergeCommit }

private def mission (j : Json) : Except String Mission := do
  let labels ← j.getObjVal? "labels"
  let labelNodes ← (← labels.getObjVal? "nodes").getArr?
  let number ← (← j.getObjVal? "number").getNat?
  unless (← (← labels.getObjVal? "totalCount").getNat?) == labelNodes.size do
    throw s!"issue {number}: its labels did not fit one read"
  let closings ← (← (← j.getObjVal? "timelineItems").getObjVal? "nodes").getArr?
  let closing ← match closings.toList with
    | [] => pure none
    | [event] => closer event
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

/-- A read is complete when GitHub reports at least one mission (no mission at all means the label
was renamed or removed, never that the record is empty), its pages agree on one total and one
repository, only the last page
ends the pagination, and the issues read are exactly that many distinct numbers. -/
def Complete (pages : List Page) (total : Nat) (owner branch : String) : Prop :=
  0 < total ∧
  (∀ p ∈ pages, p.total = total ∧ p.owner = owner ∧ p.branch = branch) ∧
  pages.map (·.more) = List.replicate (pages.length - 1) true ++ [false] ∧
  ((pages.flatMap (·.missions)).map (·.number)).Nodup ∧
  (pages.flatMap (·.missions)).length = total

instance (pages : List Page) (total : Nat) (owner branch : String) :
    Decidable (Complete pages total owner branch) := by
  unfold Complete; exact inferInstance

/-- Assemble the pages of one read, refusing a read that is not complete. -/
def assemble (pages : List Page) : Except String Snapshot :=
  match pages with
  | [] => .error "GitHub returned no pages"
  | first :: rest =>
    if Complete (first :: rest) first.total first.owner first.branch then
      .ok { owner := first.owner, branch := first.branch
            missions := (first :: rest).flatMap (·.missions) }
    else .error "the read of GitHub's pages is partial or inconsistent"

/-- An assembled read holds exactly the total GitHub reported, distinct, from a pagination that
ended. -/
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

/-- Two reads, taken one after the other, must assemble to one snapshot. -/
def agree (first second : List Page) : Except String Snapshot := do
  let a ← assemble first
  let b ← assemble second
  if a = b then return a else throw "GitHub's missions changed between the two reads; read again"

/-- What `agree` returns both reads assembled to. -/
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

/-- The labels that say what kind of work a mission is. Labels on a repository are applied only by
accounts with triage access, or by the issue template, which applies `mission` alone. -/
def kindLabels : List String :=
  ["mission:proof", "mission:contract", "mission:world", "mission:prior-art"]

/-- The kinds a mission carries, in the order of `kindLabels`. -/
def Mission.kinds (m : Mission) : List String := kindLabels.filter m.labels.contains

/-- The text under the issue template's `## Mission contract` heading, when it has any. CRLF line
ends, which GitHub stores for text typed in its web forms, are removed. -/
def contractOf (body : String) : Option String :=
  let lines := (body.splitOn "\n").map fun line => (line.dropEndWhile (· == '\r')).toString
  match lines.dropWhile (fun line => line.trimAscii.toString != "## Mission contract") with
  | [] => none
  | _ :: rest =>
    let contract := "\n".intercalate (rest.takeWhile (fun line => !line.startsWith "## "))
    let trimmed := contract.trimAscii.toString
    if trimmed.isEmpty then none else some trimmed

/-- Whether a mission's contract can be relied on as frozen. -/
inductive ContractState
  /-- It carries a kind label and a contract, and nobody but the owner has edited it last. -/
  | frozen
  /-- It has no kind label or no contract section, so nobody has accepted a contract yet. -/
  | proposed
  /-- Someone other than the owner edited it last, so its text may not be what was accepted. -/
  | edited
  deriving DecidableEq

/-- The state of a mission's contract, where `owner` is the repository's owner. An outsider's edit
after the owner's acceptance shows as `edited`; the owner's own later edit accepts it again. -/
def Mission.contractState (m : Mission) (owner : String) : ContractState :=
  if m.kinds.isEmpty || (contractOf m.body).isNone then .proposed
  else match m.editor with
    | some editor => if editor = owner then .frozen else .edited
    | none => .frozen

/-- Whether a character may stand in an agent's name. -/
def agentChar (c : Char) : Bool :=
  c.isAlphanum || [' ', '.', '_', '+', '-', '(', ')', '/'].contains c

/-- A name of at most 64 characters from `agentChar`, and nothing else. -/
def admitName (name : String) : Option String :=
  if !name.isEmpty && name.length ≤ 64 && name.toList.all agentChar then some name else none

/-- A line with its surrounding space and any list marker removed. -/
def bareLine (line : String) : String :=
  let trimmed := line.trimAscii.toString
  if trimmed.startsWith "- " then (trimmed.drop 2).toString else trimmed

/-- An agent named by a line of the squash commit's message: `Agent: <name>` or `- Agent: <name>`,
with a name `admitName` admits. Any other line names nobody. -/
def agentName (line : String) : Option String :=
  if (bareLine line).startsWith "Agent: " then admitName ((bareLine line).drop 7).toString else none

/-- A name `agentName` admits uses only the closed character set. -/
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

/-- The last line of a passing `./scripts/gate.sh`, which the pull request template asks for. -/
def gateLine : String := "gate: every merge check passed"

/-- A mission that landed. -/
structure Landed where
  /-- The mission's issue number. -/
  mission : Nat
  /-- The mission's title. -/
  title : String
  /-- The number of the pull request that closed it. -/
  pullRequest : Nat
  /-- The account that opened that pull request. -/
  account : Option Account
  /-- The agents the squash commit's message names. -/
  agents : List String
  /-- When the pull request merged. -/
  mergedAt : Option String
  /-- The squash commit's object id. -/
  commit : String

/-- Why a closed mission is not on the record as landed. -/
inductive Withheld
  /-- It was closed as not planned or as a duplicate. -/
  | notCompleted
  /-- No merged pull request closed it. -/
  | noMerge
  /-- The pull request that closed it merged into another branch. -/
  | otherBranch
  /-- Someone other than the repository's owner merged it. -/
  | otherMerger
  /-- The squash commit's message holds no passing gate result. -/
  | noGateResult

/-- What a closed mission must have to have landed: it was completed, the pull request GitHub
records as having closed it merged into the default branch at the owner's hand, and the squash
commit, which later edits of the pull request cannot change, holds the gate's final line. -/
def Accepted (m : Mission) (owner branch : String) : Prop :=
  m.completed = true ∧ ∃ c, m.closer = some c ∧ c.merged = true ∧ c.base = branch ∧
    c.mergedBy = some owner ∧ ∃ commit, c.commit = some commit ∧ commit.message.contains gateLine

/-- Decide whether a closed mission landed, and give the reason when it did not. -/
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

/-- A mission that `landing` admits meets `Accepted`, and the record names that mission. -/
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
                exact ⟨⟨completed, c, closing, merged, base, mergedBy, commit, found, contains⟩, rfl⟩

/-- A mission that meets `Accepted` is one that `landing` admits, so `landing` refuses nothing the
condition accepts. -/
theorem Mission.landing_complete {m : Mission} {owner branch : String}
    (accepted : Accepted m owner branch) :
    ∃ l, m.landing owner branch = .ok l ∧ l.mission = m.number := by
  obtain ⟨completed, c, closing, merged, base, mergedBy, commit, found, contains⟩ := accepted
  subst base
  simp [Mission.landing, completed, closing, merged, mergedBy, found, contains]

/-- The missions of a read that landed. -/
def landedOf (s : Snapshot) : List Landed :=
  (s.missions.filter (!·.isOpen)).filterMap fun m =>
    match m.landing s.owner s.branch with
    | .ok l => some l
    | .error _ => none

/-- Every landed record comes from a mission of the read that meets `Accepted`. -/
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

/-- A closed mission of the read that meets `Accepted` has a landed record. A mission that is open,
reopened ones included, is outside the statement and earns nothing. -/
theorem landedOf_complete {s : Snapshot} {m : Mission} (member : m ∈ s.missions)
    (closed : m.isOpen = false) (accepted : Accepted m s.owner s.branch) :
    ∃ l ∈ landedOf s, l.mission = m.number := by
  obtain ⟨l, landed, number⟩ := Mission.landing_complete accepted
  refine ⟨l, ?_, number⟩
  simp only [landedOf, List.mem_filterMap, List.mem_filter]
  exact ⟨m, ⟨member, by simp [closed]⟩, by simp [landed]⟩

/-- What a holder is credited with: the missions that landed in their name. -/
structure Credit (α : Type) where
  /-- Who is credited. -/
  holder : α
  /-- The issue numbers of the missions that landed in their name. -/
  missions : List Nat

/-- Credit each holder `names` gives a landed mission, most missions first, with ties in the order
of landing. -/
def credits {α : Type} [DecidableEq α] (names : Landed → List α) (landed : List Landed) :
    List (Credit α) :=
  let rows := ((landed.flatMap names).eraseDups).map fun holder =>
    ({ holder, missions := (landed.filter (fun l => decide (holder ∈ names l))).map (·.mission) } :
      Credit α)
  rows.mergeSort fun a b => decide (b.missions.length ≤ a.missions.length)

/-- A mission counted for a holder is one that landed, and it names that holder. -/
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

/-- Every landed mission is counted for every holder it names. -/
theorem landed_credited {α : Type} [DecidableEq α] {names : Landed → List α}
    {landed : List Landed} {l : Landed} {holder : α} (member : l ∈ landed)
    (name : holder ∈ names l) :
    ∃ c ∈ credits names landed, c.holder = holder ∧ l.mission ∈ c.missions := by
  refine ⟨{ holder, missions := (landed.filter (fun l => decide (holder ∈ names l))).map (·.mission) },
    ?_, rfl, ?_⟩
  · simp only [credits, List.mem_mergeSort, List.mem_map]
    refine ⟨holder, ?_, rfl⟩
    rw [List.mem_eraseDups]
    exact List.mem_flatMap.mpr ⟨l, member, name⟩
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨l, ⟨member, name⟩, rfl⟩

/-- Credit follows acceptance: every mission counted for an account or an agent on the board is a
mission of the read whose closing pull request meets `Accepted`. -/
theorem credited_accepted {α : Type} [DecidableEq α] {names : Landed → List α} {s : Snapshot}
    {c : Credit α} {mission : Nat} (row : c ∈ credits names (landedOf s))
    (counted : mission ∈ c.missions) :
    ∃ m ∈ s.missions, m.number = mission ∧ Accepted m s.owner s.branch := by
  obtain ⟨l, member, same, _⟩ := credited_landed row counted
  obtain ⟨m, found, number, accepted⟩ := landedOf_accepted member
  exact ⟨m, found, number.trans same, accepted⟩

/-- Acceptance earns credit: a closed mission of the read that meets `Accepted` has a landed record,
and is counted for every holder that record names. -/
theorem accepted_credited {α : Type} [DecidableEq α] {names : Landed → List α} {s : Snapshot}
    {m : Mission} (member : m ∈ s.missions) (closed : m.isOpen = false)
    (accepted : Accepted m s.owner s.branch) :
    ∃ l ∈ landedOf s, l.mission = m.number ∧ ∀ holder ∈ names l,
      ∃ c ∈ credits names (landedOf s), c.holder = holder ∧ m.number ∈ c.missions := by
  obtain ⟨l, landed, number⟩ := landedOf_complete member closed accepted
  refine ⟨l, landed, number, fun holder name => ?_⟩
  rw [← number]
  exact landed_credited landed name

/-- Characters that act as nothing in a Markdown table cell or in HTML. -/
def inert (c : Char) : Bool :=
  c.isAlphanum || [' ', '.', ',', ':', '(', ')', '\'', '"', '-', '?', '/', '=', '+', '%'].contains c

/-- Replace every character that is not `inert` by its numeric character reference, which renders
as that character and acts as nothing. -/
def escape (s : String) : String :=
  String.ofList <| s.toList.flatMap fun c =>
    if inert c then [c] else '&' :: '#' :: (Nat.toDigits 10 c.toNat ++ [';'])

/-- The characters `escape` may output. -/
def escaped (c : Char) : Bool := inert c || c == '&' || c == '#' || c == ';' || c.isDigit

/-- Everything `escape` outputs is `inert` or belongs to a numeric character reference. -/
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

/-- The characters by which text would act as Markdown or HTML: table cells, code spans, links,
tags, emphasis, escapes and new lines. -/
def active : List Char := ['`', '|', '[', ']', '<', '>', '*', '_', '~', '\\', '!', '\n', '\r']

/-- Text that has been through `escape` holds no character of `active`. -/
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

/-- The machine-readable copy. Titles and contracts are as GitHub returned them, and JSON encoding
is what keeps them data. -/
def boardJson (stamp : String) (s : Snapshot) : Json :=
  let landed := landedOf s
  Json.mkObj [
    ("authority", .str s!"GitHub ({repository}) is the record. This is a copy derived at derived_at; \
      it may lag GitHub and never overrides it."),
    ("derived_at", .str stamp),
    ("regenerate", .str s!"{repository}/blob/main/docs/missions.md#regenerating-the-board"),
    ("untrusted_fields", toJson #["title", "contract"]),
    ("open", toJson <| (openOf s).toArray.map fun m => Json.mkObj [
      ("number", toJson m.number), ("title", .str m.title), ("url", .str (issueUrl m.number)),
      ("kinds", toJson m.kinds.toArray), ("contract_state", .str (stateName (m.contractState s.owner))),
      ("contract", optionJson (contractOf m.body)), ("filed_by", optionJson m.author),
      ("last_edited_by", optionJson m.editor), ("last_edited_at", optionJson m.lastEditedAt)]),
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

private def openSection (s : Snapshot) : String :=
  match openOf s with
  | [] => "No mission is open at this time."
  | missions =>
    let table := missions.map fun m =>
      s!"| {issueLink m.number} | {escape m.title} | {kindText m} | \
        {stateName (m.contractState s.owner)} |"
    rows ([s!"{count missions.length "mission is" "missions are"} open.", "",
      "| Mission | What it asks | Kind | Contract |", "|---|---|---|---|"] ++ table ++ ["",
      "A *frozen* contract is accepted and may not be weakened. A *proposed* one has not been \
      accepted yet, so do not start on it. An *edited* one was last changed by someone other than \
      the owner, so its text may not be what was accepted; do not rely on it until the owner has \
      edited it again."])

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

/-- The page for people. Everything an outsider wrote goes through `escape`; links are built from
issue and pull request numbers and from logins that pass `loginChar`, never from outside text. -/
def boardMarkdown (stamp : String) (s : Snapshot) : String :=
  rows [
    "# Mission board", "",
    s!"This page is a copy of what GitHub records about Acorn's missions, derived at {stamp}. \
      GitHub is the record: this copy may lag it and never overrides it. For the current state, \
      see the [open missions on GitHub]({repository}/issues?q=is%3Aopen+label%3Amission). \
      [Regenerating the board](missions.md#regenerating-the-board) says how this page is made. \
      New to missions? [Start here](missions.md).", "",
    "## Open missions", "", openSection s, "",
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

/-- Whether a time has the form `date -u +%FT%TZ` prints. -/
def validStamp (stamp : String) : Bool :=
  stamp.length == stampShape.length &&
    (stamp.toList.zip stampShape).all fun (c, shape) => if shape == '0' then c.isDigit else c == shape

private def readPages (path : String) : IO (List Page) := do
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept ((← IO.ofExcept parsed.getArr?).toList.mapM page)

private def publish (path content : String) : IO Unit := do
  let staged := path ++ ".tmp"
  IO.FS.writeFile staged content
  IO.FS.rename staged path

/-- Derive both files, then write them; a refused read writes nothing. -/
def render (stamp first second base : String) : IO Unit := do
  unless validStamp stamp do throw (IO.userError s!"not a UTC time of the form {String.ofList stampShape}: {stamp}")
  unless first != second do throw (IO.userError "the two reads must be two separate files")
  let snapshot ← IO.ofExcept (agree (← readPages first) (← readPages second))
  publish (base ++ ".json") ((boardJson stamp snapshot).pretty ++ "\n")
  publish (base ++ ".md") (boardMarkdown stamp snapshot)

/-- `query` prints the GraphQL query; `render <time> <read> <read> <path without extension>` writes
the board. -/
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
