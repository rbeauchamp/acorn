/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.OwnershipSource
import AcornTools.Theorems
import AcornTools.Corpus.Audit
import AcornTools.SealedControl
import Acorn.Host.Checkpoint.Snapshot

/-! # Compiler-linked ownership admission

Source discovery, Lake's evaluated executable configuration, and compiled
declaration ownership must agree. Required proof anchors name statements about
the actual executing definitions; their types must still refer to those owners.
This is coverage/routing admission, not an inference that names prove semantics.
Types, proof terms, the runtime boundary and review supply the semantic evidence.

## Sealed constants

A private constructor stops the constructor notation outside its module. It does not stop
a tactic: `by constructor` applies it anywhere. Lean also generates a public alias of a
public constructor. So the audit reads the compiled declarations, and it finds the
constants that make a sealed value by what they are, with no test of a name.

The sealed constants of an environment, each with the modules that may reference it:

1. every private constructor of a type of a maintained project module, with its declaring
   module;
2. the rows of `AcornOwnership.sealedConstants`;
3. every alias of a sealed constructor, found by its body: a definition whose body is the
   constructor applied to a rearrangement of the definition's own parameters;
4. every maker of a type of `AcornOwnership.sealedTypes`, found by its type (`gives`), in
   the modules that may reference a sealed constant of those types. It gets the modules
   of the constructors of the type it makes, unless it has a row or is an open maker
   (`AcornOwnership.openMakers`, each with the theorem that justifies it).

The rule: no declaration of a project module outside the permitted modules, other than a
theorem, references a sealed constant. A definition of another module then gets a sealed
value only from an open maker, or from a function that takes a sealed value with the same
arguments, so part 4 reads the owning modules only.

`gives` is a test of position, not of mention. A value of a sealed type gives one, unless
a binder before it has a sealed type with equal arguments (the snapshot of a state does
not make an image; a function from a state of one construction to a state of another
does). A structure gives what a field gives: an `Option`, an `Except`, a product or an
`Inhabited` instance of a sealed type gives one, and a `SizeOf` instance or a record of
functions that take the value first does not. A constructor of a type that is not sealed
is no maker: it holds what its caller gave it. A field projection is no maker.

Limits. The rule classifies a function of an owning module by its type and does not read
its body: the owning modules stay the reviewed makers. A theorem is exempt: compiled code
gets no value from a proof, and the equations that Lean derives for a definition are
theorems of the module that first uses them. A `noncomputable` definition could take a
sealed value out of a proof by choice; it is not executed. The rule is about this
project's modules. It does not stop a definition in another project, and it says nothing
about bytes in a file.

Five control declarations below make a sealed value outside its module. The audit runs
the rule on this module two times and requires that the complete rule reports exactly the
five and that parts 1 and 2 alone report exactly the first two. So each of the other
three is reported by part 3 or part 4 and by nothing else.
-/
namespace AcornOwnershipAudit
open Lean

/-- Compiler module indices, rather than declaration namespaces, establish ownership. -/
def ownerOf (env : Environment) (name : Name) : IO Name := do
  let some index := env.getModuleIdxFor? name
    | throw (IO.userError s!"{name}: no compiled declaration owner")
  let some imported := env.header.modules[index.toNat]?
    | throw (IO.userError s!"{name}: invalid compiled owner index")
  return imported.module

/-- Follow actual compiler IR calls and closures, excluding erased proof/type references.
External compiler/library primitives end traversal and remain trusted. -/
def executionClosure (env : Environment) (imports : NameSet) : IO NameSet := do
  let mut pending := #[`main]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let some name := pending.back? | throw (IO.userError "lost IR work item")
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let owner ← ownerOf env name
    require (imports.contains owner) s!"{name}: IR reference outside entry import closure: {owner}"
    unless AcornOwnership.modules.contains owner do continue
    let some declaration := IR.findEnvDecl env name
      | throw (IO.userError s!"{owner}: missing compiler IR for {name}")
    require (!declaration.isExtern) s!"{owner}: external replacement for {name}"
    require declaration.getInfo.sorryDep?.isNone s!"{owner}: admitted hole in compiled {name}"
    pending := pending ++ IR.collectUsedDecls env [declaration]
  return seen

/-- Every declared entry must reach its own reviewed executing owners. -/
def entryContract (env : Environment) (owner : Name) (imports : NameSet) : IO Unit := do
  let contracts := AcornOwnership.entryUses.filter (·.1 == owner)
  require (contracts.size == 1) s!"{owner}: missing or duplicate entry contract"
  let some (_, required) := contracts[0]? | throw (IO.userError "entry contract disappeared")
  require (!required.isEmpty) s!"{owner}: empty execution contract"
  let reachable ← executionClosure env imports
  let missing := required.filter (!reachable.contains ·)
  require missing.isEmpty s!"{owner}: native main no longer reaches {missing}"

/-- The required theorem's checked statement must still name its executable definition. -/
def anchor (env : Environment) (proofOwner theoremName implementation : Name) : IO Unit := do
  let some (.thmInfo theoremInfo) := env.find? theoremName
    | throw (IO.userError s!"missing required theorem {theoremName}")
  require ((← ownerOf env theoremName) == proofOwner) s!"{theoremName}: wrong proof owner"
  let some implementationInfo := env.find? implementation
    | throw (IO.userError s!"{theoremName}: missing execution owner {implementation}")
  require (!implementationInfo.isUnsafe && !implementationInfo.isPartial)
    s!"{implementation}: unreviewed execution replacement"
  require (AcornOwnership.modules.contains (← ownerOf env implementation))
    s!"{implementation}: execution owner is not maintained"
  require (theoremInfo.type.getUsedConstantsAsSet.contains implementation)
    s!"{theoremName}: statement no longer refers to {implementation}"

/-- Control of part 1: a state of a construction from a learner state of no declared
history, made outside the module of the type with the `constructor` tactic. Nothing calls
it; the audit requires that the rule reports it. -/
def sealedControl (construction : Acorn.Handcrafted.AgentConstruction)
    (agent : Acorn.Handcrafted.Agent Acorn.Handcrafted.Grid.interface construction.profile
      construction.config construction.criterion construction.dimension construction.planning) :
    construction.State := by
  constructor
  exact agent

/-- Control of part 2: the callback record of one step order copied under the index of
the other with the constructor. Nothing calls it; the audit requires that the rule
reports it. -/
def tableControl {α β : Type} (callbacks : Acorn.Host.AgentCallbacks .planAfterAct α β) :
    Acorn.Host.AgentCallbacks .learnThenAct α β :=
  { Chosen := callbacks.Chosen, choose := callbacks.choose, learn := callbacks.learn,
    recordEnvironment := callbacks.recordEnvironment, recordAttempt := callbacks.recordAttempt,
    capture := callbacks.capture, metrics := callbacks.metrics }

/-- Control of part 3, the image route: the snapshot of a state of one construction is
made into an image of a construction of the other step order with the generated alias of
the image's constructor, and the payload writer of that construction stamps it. It
references no constructor, so parts 1 and 2 do not report it. The compiler has no code
for the alias, so the definition is not compiled. -/
noncomputable def aliasImageControl (profile : Acorn.Handcrafted.FeatureProfile)
    (criterion : Acorn.Features.Criterion) (planning : Acorn.Features.PlanningSelection)
    (config : Acorn.Features.Config) (dimension : Acorn.Dimension)
    (state : (Acorn.Handcrafted.AgentConstruction.mk profile criterion planning .learnThenAct
      config dimension).State) : Acorn.Checkpoint.Payload dimension :=
  Acorn.Checkpoint.imagePayload ⟨profile, criterion, planning, .planAfterAct, config, dimension⟩
    (@Acorn.Handcrafted.AgentConstruction.Image.mk._flat_ctor
      ⟨profile, criterion, planning, .planAfterAct, config, dimension⟩
      (Acorn.Checkpoint.snapshotImage ⟨profile, criterion, planning, .learnThenAct, config,
        dimension⟩ state).image)

/-- Control of part 3, the callback route: the callback record of one step order is
copied under the index of the other with the generated alias of its constructor and
given to the generic attempt runner. It references no constructor, so parts 1 and 2 do
not report it. -/
noncomputable def aliasCallbackControl {config : Acorn.Host.WorldConfig} {goal : Acorn.Host.Goal}
    {cap : UInt64} {α β : Type} (callbacks : Acorn.Host.AgentCallbacks .planAfterAct α β)
    (observer : Acorn.Host.StreamObserver β) (context : Acorn.Host.GoalContext)
    (initial : Acorn.Host.Attempt config α goal cap) (resources : Acorn.Host.RunnerResources) :
    IO (Except (Acorn.Host.Refusal config α goal cap)
      (Acorn.Host.RunState config α × Acorn.Host.GoalOutcome × Acorn.Host.RunnerResources)) :=
  Acorn.Host.runAttempt
    (@Acorn.Host.AgentCallbacks.mk._flat_ctor .learnThenAct α β callbacks.Chosen
      callbacks.choose callbacks.learn callbacks.recordEnvironment callbacks.recordAttempt
      callbacks.capture callbacks.metrics)
    observer context initial resources

/-- Control of part 4: a value of the sealed control type from the `Inhabited` instance of
its owning module. It references no constructor and no constructor alias, and the
instance has no constructor in its name: the rule finds the instance by its type. -/
def instanceControl : AcornSealedControl.Token true := default

/-- The applications of the given types in an expression: the type and its arguments. -/
partial def sealedMentions (types : Array Name) (e : Expr) : Array (Name × Array Expr) :=
  match e with
  | .const name _ => if types.contains name then #[(name, #[])] else #[]
  | .app .. =>
    let args := e.getAppArgs
    let inner := args.foldl (fun found arg => found ++ sealedMentions types arg) #[]
    match e.getAppFn with
    | .const name _ => if types.contains name then #[(name, args)] ++ inner else inner
    | head => sealedMentions types head ++ inner
  | .lam _ domain body _ | .forallE _ domain body _ =>
    sealedMentions types domain ++ sealedMentions types body
  | .letE _ type value body _ =>
    sealedMentions types type ++ sealedMentions types value ++ sealedMentions types body
  | .mdata _ body | .proj _ _ body => sealedMentions types body
  | _ => #[]

/-- The declared type ends in `Prop`: its values are proofs. -/
def typeInProp (type : Expr) : Bool := Id.run do
  let mut current := type
  while current.isForall do current := current.bindingBody!
  return current.isProp

/-- The types of `types` that a holder of a value of `type` gets a value of, when no
binder before it supplied a value of a sealed type with the same arguments. `guards` are
the argument lists of the sealed binders passed so far, and `visited` the applied
inductive types on the path. A type that a recursor computes gives what the type of one
of its branches gives. Another type that this function cannot reduce counts as giving
each type it mentions. -/
partial def gives (env : Environment) (types : Array Name) (guards : Array (Array Expr))
    (visited : Array Expr) (depth : Nat) (type : Expr) : Array Name :=
  let unguarded (found : Array (Name × Array Expr)) : Array Name :=
    found.foldl (fun made (name, args) =>
      if guards.any (· == args) || made.contains name then made else made.push name) #[]
  if depth > 96 then unguarded (sealedMentions types type) else
  let type := type.headBeta
  match type with
  | .mdata _ body => gives env types guards visited depth body
  | .sort _ => #[]
  | .forallE _ domain body _ =>
    let guards := match domain.getAppFn with
      | .const name _ => if types.contains name then guards.push domain.getAppArgs else guards
      | _ => guards
    gives env types guards visited (depth + 1)
      (body.instantiate1 (.fvar ⟨Name.mkNum `binder depth⟩))
  | _ =>
    match type.getAppFn with
    | .const name levels =>
      let args := type.getAppArgs
      if types.contains name then unguarded #[(name, args)]
      else match env.find? name with
        | some (.defnInfo info) =>
          gives env types guards visited (depth + 1)
            ((info.value.instantiateLevelParams info.levelParams levels).beta args)
        | some (.inductInfo info) =>
          if typeInProp info.type || visited.contains type then #[] else Id.run do
            let visited := visited.push type
            let mut made : Array Name := #[]
            let mut used := false
            for constructor in info.ctors do
              let some (.ctorInfo constructorInfo) := env.find? constructor | continue
              let mut current :=
                constructorInfo.type.instantiateLevelParams constructorInfo.levelParams levels
              for index in [:info.numParams] do
                if current.isForall then
                  current := current.bindingBody!.instantiate1 (args.getD index (.sort .zero))
              let mut counter := 0
              while current.isForall do
                let field := current.bindingDomain!
                let proof := match field.getAppFn with
                  | .const head _ => match env.find? head with
                    | some (.inductInfo fieldInfo) => typeInProp fieldInfo.type
                    | _ => false
                  | _ => false
                unless proof || (sealedMentions types field).isEmpty do used := true
                for name in gives env types guards visited (depth + 1) field do
                  unless made.contains name do made := made.push name
                current := current.bindingBody!.instantiate1
                  (.fvar ⟨Name.mkNum (Name.mkNum `field depth) counter⟩)
                counter := counter + 1
            -- A parameter that no data field uses is the mark of an opaque container.
            unless used do
              for name in unguarded (sealedMentions types type) do
                unless made.contains name do made := made.push name
            return made
        | some (.recInfo info) =>
          -- A type that a recursor computes from a value that is not known is one of the
          -- types of its branches.
          let minors := args.extract (info.numParams + info.numMotives)
            (info.numParams + info.numMotives + info.numMinors)
          minors.foldl (fun made minor => Id.run do
            let mut body := minor
            let mut counter := 0
            while body.isLambda do
              body := body.bindingBody!.instantiate1
                (.fvar ⟨Name.mkNum (Name.mkNum `branch depth) (made.size * 64 + counter)⟩)
              counter := counter + 1
            let mut made := made
            for name in gives env types guards visited (depth + 1) body do
              unless made.contains name do made := made.push name
            return made) #[]
        | _ => unguarded (sealedMentions types type)
    | _ => unguarded (sealedMentions types type)

/-- A field projection: `fun parameters self => self.i`. It returns a part of a value
that exists. -/
def isProjection (info : ConstantInfo) : Bool :=
  match info with
  | .defnInfo definition => Id.run do
    let mut body := definition.value
    while body.isLambda do body := body.bindingBody!
    return match body with
      | .proj _ _ (.bvar 0) => true
      | _ => false
  | _ => false

/-- Built from bound variables by constructors only, with a bound variable in each leaf. -/
partial def rearranged (env : Environment) (e : Expr) : Bool :=
  match e with
  | .bvar _ => true
  | .mdata _ body => rearranged env body
  | .app .. =>
    match e.getAppFn with
    | .const name _ =>
      match env.find? name with
      | some (.ctorInfo info) =>
        let fields := e.getAppArgs.extract info.numParams e.getAppNumArgs
        !fields.isEmpty && fields.all (rearranged env)
      | _ => false
    | _ => false
  | _ => false

/-- The constructor that a definition is an alias of: its body is that constructor
applied to a rearrangement of the definition's own parameters, and to nothing else. -/
def aliasOf (env : Environment) (info : ConstantInfo) : Option Name :=
  match info with
  | .defnInfo definition => Id.run do
    let mut body := definition.value
    while body.isLambda do body := body.bindingBody!
    let .const head _ := body.getAppFn | return none
    let some (.ctorInfo constructor) := env.find? head | return none
    let fields := body.getAppArgs.extract constructor.numParams body.getAppNumArgs
    if body.getAppNumArgs == constructor.numParams + constructor.numFields &&
        !fields.isEmpty && fields.all (rearranged env) then return some head else return none
  | _ => none

/-- The sealed constants of one compiled environment. -/
structure Sealing where
  /-- Each sealed constant with the modules that may reference it in a definition. -/
  permitted : NameMap (Array Name) := {}
  /-- Each sealed constant with the part of the rule that found it and those modules. -/
  found : Array (Name × String × Array Name) := #[]

/-- Add one sealed constant. -/
def Sealing.add (sealing : Sealing) (name : Name) (part : String) (owners : Array Name) :
    Sealing :=
  { permitted := sealing.permitted.insert name owners,
    found := sealing.found.push (name, part, owners) }

/-- The number of sealed constants that one part found. -/
def Sealing.count (sealing : Sealing) (part : String) : Nat :=
  (sealing.found.filter (·.2.1 == part)).size

/-- The modules that may reference a constructor of a type. -/
def typeOwners (env : Environment) (sealing : Sealing) (type : Name) : Array Name :=
  match env.find? type with
  | some (.inductInfo info) =>
    info.ctors.foldl (fun owners constructor =>
      (sealing.permitted.find? constructor |>.getD #[]).foldl
        (fun owners owner => if owners.contains owner then owners else owners.push owner) owners)
      #[]
  | _ => #[]

/-- The sealed constants of one compiled environment with the modules that may reference
each. Parts 1 and 2 are the direct part; `derived` adds the constructor aliases found by
body and the makers of `types` found by type. -/
def sealedIn (env : Environment) (projects : Array Name)
    (types : Array Name := AcornOwnership.sealedTypes) (derived : Bool := true) :
    IO Sealing := do
  let mut sealing : Sealing := {}
  for (name, info) in env.constants do
    if let .ctorInfo constructor := info then
      if isPrivateName name then
        let owner ← ownerOf env constructor.induct
        if projects.contains owner then sealing := sealing.add name "private constructor" #[owner]
  for (name, owners) in AcornOwnership.sealedConstants do
    if (env.find? name).isSome then sealing := sealing.add name "table row" owners
  unless derived do return sealing
  for (name, info) in env.constants do
    let some constructor := aliasOf env info | continue
    let some owners := sealing.permitted.find? constructor | continue
    if sealing.permitted.contains name then continue
    unless projects.contains (← ownerOf env name) do continue
    sealing := sealing.add name "constructor alias" owners
  let mut owning : Array Name := #[]
  for type in types do
    for owner in typeOwners env sealing type do
      unless owning.contains owner do owning := owning.push owner
  for (name, owners) in AcornOwnership.sealedConstants do
    if (env.find? name).isSome then
      for owner in owners do
        unless owning.contains owner do owning := owning.push owner
  for (name, info) in env.constants do
    match info with
    | .defnInfo _ | .opaqueInfo _ => pure ()
    | _ => continue
    let some index := env.getModuleIdxFor? name | continue
    let some imported := env.header.modules[index.toNat]? | continue
    unless owning.contains imported.module do continue
    if sealing.permitted.contains name || AcornOwnership.openMakers.any (·.1 == name) then continue
    if isProjection info then continue
    let made := gives env types #[] #[] 0 info.type
    let some first := made[0]? | continue
    let owners := (made.extract 1 made.size).foldl
      (fun owners other => owners.filter (typeOwners env sealing other).contains)
      (typeOwners env sealing first)
    sealing := sealing.add name "maker" owners
  return sealing

/-- Each declaration of the selected modules, other than a theorem, that references a
sealed constant outside its permitted modules: the owner, the declaration, the constant. -/
def sealedViolations (env : Environment) (permitted : NameMap (Array Name))
    (selected : Array Name) : IO (Array (Name × Name × Name)) := do
  let mut found := #[]
  for (name, info) in env.constants do
    if let .thmInfo _ := info then continue
    let some index := env.getModuleIdxFor? name | continue
    let some imported := env.header.modules[index.toNat]?
      | throw (IO.userError s!"{name}: invalid compiled owner index")
    let owner := imported.module
    unless selected.contains owner do continue
    for used in info.getUsedConstantsAsSet do
      if let some owners := permitted.find? used then
        unless owners.contains owner do found := found.push (owner, name, used)
  return found

/-- No selected project module makes a sealed value outside the permitted modules. -/
def sealedAdmission (env : Environment) (sealing : Sealing) (selected : Array Name) :
    IO Unit := do
  for (owner, name, used) in ← sealedViolations env sealing.permitted selected do
    throw (IO.userError s!"{owner}: {name} references the sealed constant {privateToUserName used}; only {sealing.permitted.find? used |>.getD #[]} may")

/-- The tables agree with the environment. Each type of `AcornOwnership.sealedTypes`
exists and each of its constructors is sealed. Each table row names a compiled constant
and maintained modules. Each sealed constant is owned by one of its own permitted
modules, so a computed maker in a module that has only a row fails closed. Each open
maker is a maker by its type, and its theorem exists and names it. -/
def sealedRequired (env : Environment) (sealing : Sealing) (modules : Array Name) :
    IO Unit := do
  for type in AcornOwnership.sealedTypes do
    let some (.inductInfo info) := env.find? type
      | throw (IO.userError s!"missing sealed type {type}")
    for constructor in info.ctors do
      require (sealing.permitted.contains constructor)
        s!"{type}: the constructor {constructor} is neither private nor a sealed table row"
  for (name, owners) in AcornOwnership.sealedConstants do
    require ((env.find? name).isSome) s!"stale sealed constant {name}"
    for owner in owners do
      require (modules.contains owner) s!"{name}: stale permitted module {owner}"
  for (name, part, owners) in sealing.found do
    require (owners.contains (← ownerOf env name))
      s!"{privateToUserName name}: this {part} is not owned by a module that may reference it ({owners}); give it a row or make it an open maker"
  for (maker, justification) in AcornOwnership.openMakers do
    let some info := env.find? maker | throw (IO.userError s!"stale open maker {maker}")
    require (!(gives env AcornOwnership.sealedTypes #[] #[] 0 info.type).isEmpty)
      s!"{maker}: an open maker that makes no sealed type by its type"
    let some (.thmInfo theoremInfo) := env.find? justification
      | throw (IO.userError s!"{maker}: missing theorem {justification}")
    require (theoremInfo.type.getUsedConstantsAsSet.contains maker)
      s!"{justification}: its statement does not name the open maker {maker}"

/-- The complete rule must report the five controls of this module and nothing else in
it, and the direct part alone must report the first two and nothing else. The control
type and its owning module are inputs of this run only. -/
def sealedControls (env : Environment) (projects : Array Name) : IO Unit := do
  let controls := projects.push `AcornTools.SealedControl
  let types := AcornOwnership.sealedTypes.push ``AcornSealedControl.Token
  let reported (sealing : Sealing) : IO (Array Name) := do
    let found ← sealedViolations env sealing.permitted #[`AcornTools.OwnershipAudit]
    return found.foldl (fun names row =>
      if names.contains row.2.1 then names else names.push row.2.1) #[]
  let complete ← reported (← sealedIn env controls types)
  let direct ← reported (← sealedIn env controls types (derived := false))
  let expected := #[``sealedControl, ``tableControl, ``aliasImageControl,
    ``aliasCallbackControl, ``instanceControl]
  require (expected.all complete.contains && complete.all expected.contains)
    s!"the sealed-constant rule must report exactly its 5 controls; it reported {complete}"
  require (direct.size == 2 && direct.contains ``sealedControl && direct.contains ``tableControl)
    s!"the direct part of the sealed-constant rule must report exactly the 2 direct controls; it reported {direct}"

/-- One line for each part of the rule, from the computed set. -/
def Sealing.report (sealing : Sealing) : String :=
  s!"ownership: {sealing.found.size} sealed constants ({sealing.count "private constructor"} private constructors, {sealing.count "table row"} table rows, {sealing.count "constructor alias"} constructor aliases found by body, {sealing.count "maker"} makers found by type) and {AcornOwnership.openMakers.size} open makers; no definition outside their modules references a sealed constant"

/-- Follow the entry's actual serialized import edges. Shared dependency data
must never make a declaration outside this closure available to its IR check. -/
def importClosure (env : Environment) (root : Name) : IO NameSet := do
  let mut seen : NameSet := {}
  let mut pending := #[root]
  while !pending.isEmpty do
    let some owner := pending.back? | throw (IO.userError "lost import work item")
    pending := pending.pop
    if seen.contains owner then continue
    seen := seen.insert owner
    let some index := env.getModuleIdx? owner
      | throw (IO.userError s!"{owner}: missing compiled import owner")
    let some data := env.header.moduleData[index.toNat]?
      | throw (IO.userError s!"{owner}: missing compiled import data")
    pending := pending ++ data.imports.map (·.module)
  return seen

/-- Reuse compiler-loaded dependency regions, keeping each executable's `main`
isolated. Lean itself constructs every environment and rejects conflicting
constants. Regions remain alive until this bounded audit process exits;
no sibling environment may free shared regions. Ordinary sibling maps are
released, while the common environment also serves axiom/document admission.
Complete mode initializes the same reviewed non-entry scope used by corpus
admission, after source admission; standalone ownership needs no extensions. -/
unsafe def compiled (complete : Bool := false) (listSealed : Bool := false) : IO Unit := do
  let modules ← sources
  let entries ← targets
  initSearchPath (← findSysroot)
  for owner in modules do
    let path : System.FilePath := ".lake/build/lib/lean" / (owner.toString.replace "." "/" ++ ".olean")
    require ((← IO.FS.realPath (← findOLean owner)) == (← IO.FS.realPath path))
      s!"{owner}: compiled artifact resolves outside the current build"
  let mut dependencies : Array Import := #[]
  for (_, owner) in entries do
    let (data, _) ← readModuleData (← findOLean owner)
    dependencies := dependencies ++ data.imports.map fun imp =>
      { imp with importAll := true, isMeta := true }
  withImporting do
    let (_, base) ← (importModulesCore dependencies).run
    let shared := modules.filter fun owner => !entries.any (·.2 == owner)
    let commonImports := shared.map fun owner => { module := owner : Import }
    let (_, commonState) ← (importModulesCore commonImports).run base
    if complete then enableInitializersExecution
    let common ← finalizeImport commonState commonImports {} (leakEnv := true) (loadExts := complete)
    let projects := modules.filter (!AcornModuleInventory.toolingModules.contains ·)
    let included := projects.filter fun owner => (common.getModuleIdx? owner).isSome
    let sealing ← sealedIn common projects
    if listSealed then
      for (name, part, owners) in sealing.found.qsort (fun a b => a.2.1 < b.2.1 ||
          (a.2.1 == b.2.1 && (privateToUserName a.1).toString < (privateToUserName b.1).toString)) do
        IO.println s!"sealed {part}: {privateToUserName name} <- {owners}"
      for (maker, justification) in AcornOwnership.openMakers do
        IO.println s!"open maker: {maker} ({justification})"
    sealedRequired common sealing modules
    sealedAdmission common sealing included
    let mut counts : AcornTheoremCount.Counts := {}
    if complete then counts ← AcornTheoremCount.countEnvironment common included
    let mut counted := included
    for owner in modules do
      let isEntry := entries.any (·.2 == owner)
      let inspect (env : Environment) : IO Unit := do
        require ((env.getModuleIdx? owner).isSome) s!"{owner}: module absent from compiled environment"
        let ownsMain ← match env.find? `main with
          | some _ => do pure ((← ownerOf env `main) == owner)
          | none => pure false
        require (ownsMain == (isEntry || owner == `Bootstrap))
          s!"{owner}: compiled main and executable inventory disagree"
        if isEntry then
          require ((getModuleDoc? env owner).any (·.any (·.doc.any (!·.isWhitespace : Char → Bool))))
            s!"{owner}: executable root lacks a module docstring"
          entryContract env owner (← importClosure env owner)
        for (proofOwner, theoremName, implementation) in AcornOwnership.anchors do
          if proofOwner == owner then anchor env proofOwner theoremName implementation
      if isEntry then
        let imports := #[{ module := owner, importAll := true, isMeta := true : Import }]
        let (_, state) ← (importModulesCore imports).run base
        let env ← finalizeImport state imports {} (leakEnv := false) (loadExts := false)
        inspect env
        if projects.contains owner then sealedAdmission env (← sealedIn env projects) #[owner]
        if owner == `AcornTools.OwnershipAudit then sealedControls env projects
        if complete && projects.contains owner && !counted.contains owner then
          let extra ← AcornTheoremCount.countEnvironment env #[owner]
          counts := counts.add extra
          counted := counted.push owner
      else
        inspect common
    for (proofOwner, _, _) in AcornOwnership.anchors do
      require (modules.contains proofOwner) s!"stale proof owner {proofOwner}"
    for (owner, _) in AcornOwnership.entryUses do
      require (entries.any (·.2 == owner)) s!"stale entry contract {owner}"
    IO.println s!"ownership: {modules.size} maintained modules, {entries.size} native entries, {AcornOwnership.anchors.size} required execution/proof links"
    IO.println sealing.report
    IO.println "ownership: 5 controls of the sealed-constant rule reported, 2 of them by the direct part alone"
    if complete then
      require (projects.all counted.contains && counted.size == projects.size)
        "incomplete or duplicate theorem-owner admission"
      counts.report
      let cwd ← IO.Process.getCurrentDir
      try
        IO.Process.setCurrentDir ".."
        AcornCorpus.check (env? := some common)
      finally IO.Process.setCurrentDir cwd

end AcornOwnershipAudit

/-- Source/target admission can run before project modules are compiled. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["source"] =>
      discard AcornOwnershipAudit.sources
      discard AcornOwnershipAudit.targets
      IO.println "ownership: source modules and Lake entries admitted"
    | ["compiled"] => AcornOwnershipAudit.compiled
    | ["complete"] => AcornOwnershipAudit.compiled true
    | ["sealed"] => AcornOwnershipAudit.compiled false true
    | _ => throw (IO.userError "usage: ownership-audit (source|compiled|complete|sealed)")
    return 0
  catch error =>
    IO.eprintln s!"ownership-audit: {error}"
    return 1
