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
public constructor. So the audit reads the compiled declarations.

The sealed constants of an environment, each with the modules that may reference it:

1. every private constructor of a type of a maintained project module, with its declaring
   module;
2. the rows of `AcornOwnership.sealedConstants`;
3. every alias of a sealed constructor, found by its body: a definition whose body is the
   constructor applied to a rearrangement of the definition's own parameters;
4. every site that is not an entry of the interface.

**The tracked set** is the one definition behind part 4. The designated constants are
the constructors of the types of `AcornOwnership.sealedTypes` and the table rows. An
owning module is a module that may reference a designated constant. The tracked set is
the least set that holds the designated constants and each declaration of an owning
module, other than a theorem, that references a member of the set. A site is a tracked
declaration that is not designated. There is no exception: a declaration that is sealed
for another reason (an alias of any constructor, a private constructor of another type),
a table row and an interface entry each propagate to the declarations that reference
them, and every kind of declaration is read (for an inductive type, its type; its list of
constructors is not a reference).

The rule: no declaration of a project module outside the permitted modules, other than a
theorem, references a sealed constant. The entries of `AcornOwnership.interface` are the
sites that every module may use. A declaration of an owning module that references an
entry is tracked, so it is sealed unless it is an entry too: the rule does not rely on an
argument about what a caller of an entry can do.

The audit reads no type and infers nothing: it does not decide that a definition makes a
value, carries one, or is harmless. A type can hide a sealed type from any reader of
types (a type variable with an equality, a recursor, an abbreviation, a projection of an
opaque constant, a value packed with its own type), and a reference cannot be hidden. So
a site that other modules use is in the interface, with a theorem or with a line that
says why no statement exists, and every other site is sealed.

The trusted base of the invariant is the owning modules, the interface list and this
tool. The rule does not read the body of a definition of an owning module to decide if
it keeps the claim of a sealed type: a change of an owning module or of the interface
list is a change of the invariant and is reviewed as one. A theorem is exempt: compiled
code gets no value from a proof, and the equations that Lean derives for a definition are
theorems of the module that first uses them. A `noncomputable` definition could take a
sealed value out of a proof by choice; it is not executed. The rule is about this
project's modules. It does not stop a definition in another project, and it says nothing
about bytes in a file.

Eleven control declarations below make a sealed value outside its module. The audit runs
the rule on this module two times. The complete rule must report each control for its
intended constant and nothing else, and parts 1 and 2 alone must report exactly the first
two. So each of the other nine is reported by part 3 or part 4 and by nothing else.
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

/-- Control of part 3, the image route: the durable data of an image of one construction
is made into an image of a construction of the other step order with the generated alias
of the image's constructor, and the payload writer of that construction stamps it. It
references no constructor and no other sealed constant, so parts 1 and 2 do not report
it. The compiler has no code for the alias, so the definition is not compiled. -/
noncomputable def aliasImageControl (profile : Acorn.Handcrafted.FeatureProfile)
    (criterion : Acorn.Features.Criterion) (planning : Acorn.Features.PlanningSelection)
    (config : Acorn.Features.Config) (dimension : Acorn.Dimension)
    (image : (Acorn.Handcrafted.AgentConstruction.mk profile criterion planning .learnThenAct
      config dimension).Image) : Acorn.Checkpoint.Payload dimension :=
  Acorn.Checkpoint.imagePayload ⟨profile, criterion, planning, .planAfterAct, config, dimension⟩
    (@Acorn.Handcrafted.AgentConstruction.Image.mk._flat_ctor
      ⟨profile, criterion, planning, .planAfterAct, config, dimension⟩ image.image)

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
instance has no constructor in its name: the instance is a site. -/
def instanceControl : AcornSealedControl.Token true := default

/-- Control of part 4, a site whose result is a type variable that an equality identifies
with the sealed type. -/
def castControl : AcornSealedControl.Token true :=
  AcornSealedControl.tokenByCast true (AcornSealedControl.Token true) rfl

/-- Control of part 4, a site whose result type a recursor computes. -/
def recursorControl : AcornSealedControl.Token true := AcornSealedControl.tokenByRecursor true

/-- Control of part 4, a site whose result type is behind abbreviations. -/
def abbreviationControl : AcornSealedControl.Token true :=
  AcornSealedControl.tokenByAbbreviation true

/-- Control of part 4, a site whose result type is a projection of an opaque constant: the
caller gets the value with a cast along the proof that the constant holds. -/
def opaqueControl : AcornSealedControl.Token true :=
  cast (AcornSealedControl.box true).property (AcornSealedControl.tokenByOpaque true)

/-- Control of part 4, a site whose result packs the value with its own type: the caller
takes the value out. -/
def packControl : AcornSealedControl.Token true := (AcornSealedControl.tokenByPack true).2

/-- Control of part 4, a site behind a definition that is sealed for another reason: the
caller reads the token out of a wrapper whose maker calls an alias of the wrapper's
constructor. -/
def wrapControl : AcornSealedControl.Token true := (AcornSealedControl.exposed true 0).token

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
  /-- Each sealed constant with the part of the rule that found it. -/
  found : Array (Name × String) := #[]
  /-- The tracked set of the module documentation. -/
  tracked : NameSet := {}

/-- Add one sealed constant. -/
def Sealing.add (sealing : Sealing) (name : Name) (part : String) (owners : Array Name) :
    Sealing :=
  { sealing with permitted := sealing.permitted.insert name owners,
                 found := sealing.found.push (name, part) }

/-- The number of sealed constants that one part found. -/
def Sealing.count (sealing : Sealing) (part : String) : Nat :=
  (sealing.found.filter (·.2 == part)).size

/-- What a declaration references. For an inductive type this is its type: the list of
its constructors is not a reference, so a mention of a sealed type is no reference to its
constructor. -/
def referencesOf (info : ConstantInfo) : NameSet :=
  match info with
  | .inductInfo induct => induct.type.getUsedConstantsAsSet
  | _ => info.getUsedConstantsAsSet

/-- The sealed constants of one compiled environment with the modules that may reference
each. Parts 1 and 2 are the direct part; `derived` adds the constructor aliases found by
body and the tracked set of `types`. No type is read. -/
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
  -- The designated constants and the owning modules.
  let mut tracked : NameSet := {}
  for type in types do
    if let some (.inductInfo info) := env.find? type then
      for constructor in info.ctors do tracked := tracked.insert constructor
  for (name, _) in AcornOwnership.sealedConstants do
    if (env.find? name).isSome then tracked := tracked.insert name
  let mut owning : Array Name := #[]
  for name in tracked do
    for owner in sealing.permitted.find? name |>.getD #[] do
      unless owning.contains owner do owning := owning.push owner
  let designated := tracked
  -- Every declaration of an owning module, other than a theorem, with what it references.
  let mut candidates : Array (Name × NameSet) := #[]
  for (name, info) in env.constants do
    if let .thmInfo _ := info then continue
    let some index := env.getModuleIdxFor? name | continue
    let some imported := env.header.modules[index.toNat]? | continue
    if owning.contains imported.module then candidates := candidates.push (name, referencesOf info)
  -- The least set: add each candidate that references a member, until none is added.
  let mut changed := true
  while changed do
    changed := false
    for (name, references) in candidates do
      if tracked.contains name then continue
      if references.toList.any tracked.contains then
        tracked := tracked.insert name
        changed := true
  -- A tracked declaration that is not an interface entry is sealed. A designated constant
  -- keeps the modules of its declaration or of its row. The modules of each other one
  -- are those that may reference every sealed member that it references, to a fixed
  -- point.
  let entry (name : Name) : Bool := AcornOwnership.interface.any (·.1 == name)
  let mut modules : NameMap (Array Name) := {}
  for (name, _) in candidates do
    if tracked.contains name && !entry name && !designated.contains name then
      modules := modules.insert name (sealing.permitted.find? name |>.getD owning)
  changed := true
  while changed do
    changed := false
    for (name, references) in candidates do
      let some current := modules.find? name | continue
      let mut narrowed := current
      for used in references do
        if used == name || entry used || !tracked.contains used then continue
        let allowed := (modules.find? used).getD (sealing.permitted.find? used |>.getD owning)
        narrowed := narrowed.filter allowed.contains
      if narrowed.size != current.size then
        modules := modules.insert name narrowed
        changed := true
  for (name, _) in candidates do
    let some owners := modules.find? name | continue
    if sealing.permitted.contains name then
      sealing := { sealing with permitted := sealing.permitted.insert name owners }
    else sealing := sealing.add name "site" owners
  return { sealing with tracked := tracked }

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

/-- No selected project module references a sealed constant outside its permitted modules. -/
def sealedAdmission (env : Environment) (sealing : Sealing) (selected : Array Name) :
    IO Unit := do
  for (owner, name, used) in ← sealedViolations env sealing.permitted selected do
    throw (IO.userError s!"{owner}: {name} references the sealed constant {privateToUserName used}; only {sealing.permitted.find? used |>.getD #[]} may. If every module may use it, it needs an entry in AcornOwnership.interface with its theorem")

/-- The tables agree with the environment. Each type of `AcornOwnership.sealedTypes`
exists and each of its constructors is sealed. Each table row names a compiled constant
and maintained modules. Each interface entry is in the tracked set, so the list holds no
entry that the rule does not need; it has its line; and a theorem that it names
exists and names the entry in its statement. -/
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
  for (entry, justification, line) in AcornOwnership.interface do
    let some info := env.find? entry | throw (IO.userError s!"stale interface entry {entry}")
    require (sealing.tracked.contains entry && !(referencesOf info).isEmpty)
      s!"{entry}: an interface entry that is not in the tracked set; remove it"
    require (!line.trimAscii.isEmpty) s!"{entry}: an interface entry with no line"
    match justification with
    | none => pure ()
    | some name =>
      let some (.thmInfo theoremInfo) := env.find? name
        | throw (IO.userError s!"{entry}: missing theorem {name}")
      require (theoremInfo.type.getUsedConstantsAsSet.contains entry)
        s!"{name}: its statement does not name the interface entry {entry}"

/-- The controls of this module, each with the sealed constant that it must be reported
for. The first two reference a constructor; the others do not. -/
def controls : Array (Name × Name) := #[
  (``sealedControl, `Acorn.Handcrafted.AgentConstruction.State.mk),
  (``tableControl, `Acorn.Host.AgentCallbacks.mk),
  (``aliasImageControl, `Acorn.Handcrafted.AgentConstruction.Image.mk._flat_ctor),
  (``aliasCallbackControl, `Acorn.Host.AgentCallbacks.mk._flat_ctor),
  (``instanceControl, ``AcornSealedControl.defaultToken),
  (``castControl, ``AcornSealedControl.tokenByCast),
  (``recursorControl, ``AcornSealedControl.tokenByRecursor),
  (``abbreviationControl, ``AcornSealedControl.tokenByAbbreviation),
  (``opaqueControl, ``AcornSealedControl.tokenByOpaque),
  (``packControl, ``AcornSealedControl.tokenByPack),
  (``wrapControl, ``AcornSealedControl.exposed)]

/-- The complete rule must report each control of this module for its intended constant
and nothing else in the module, and the direct part alone must report the first two for
their constructors and nothing else. The control type and its owning module are inputs
of this run only. -/
def sealedControls (env : Environment) (projects : Array Name) : IO Unit := do
  let scanned := projects.push `AcornTools.SealedControl
  let types := AcornOwnership.sealedTypes.push ``AcornSealedControl.Token
  let reported (sealing : Sealing) : IO (Array (Name × Name)) := do
    let found ← sealedViolations env sealing.permitted #[`AcornTools.OwnershipAudit]
    return found.map fun row => (row.2.1, privateToUserName row.2.2)
  let complete ← reported (← sealedIn env scanned types)
  let direct ← reported (← sealedIn env scanned types (derived := false))
  for (control, constant) in controls do
    require (complete.contains (control, constant))
      s!"the sealed-constant rule did not report {control} for {constant}; it reported {complete}"
  for (control, constant) in complete do
    require (controls.contains (control, constant))
      s!"the sealed-constant rule reported {control} for {constant}, which is no control"
  require (direct.size == 2 && (controls.extract 0 2).all direct.contains)
    s!"the direct part of the sealed-constant rule must report exactly the 2 direct controls for their constructors; it reported {direct}"

/-- One line for each part of the rule, from the computed set. -/
def Sealing.report (sealing : Sealing) : String :=
  let proved := (AcornOwnership.interface.filter (·.2.1.isSome)).size
  s!"ownership: {sealing.found.size} sealed constants ({sealing.count "private constructor"} private constructors, {sealing.count "table row"} table rows, {sealing.count "constructor alias"} constructor aliases found by body, {sealing.count "site"} sites) and {AcornOwnership.interface.size} interface entries ({proved} with a theorem, {AcornOwnership.interface.size - proved} with a line only); no definition outside their modules references a sealed constant"

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
      for (name, part) in sealing.found.qsort (fun a b => a.2 < b.2 ||
          (a.2 == b.2 && (privateToUserName a.1).toString < (privateToUserName b.1).toString)) do
        IO.println s!"sealed {part}: {privateToUserName name} <- {sealing.permitted.find? name |>.getD #[]}"
      for (entry, justification, line) in AcornOwnership.interface do
        IO.println s!"interface entry: {entry} ({justification.getD .anonymous}) {line}"
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
    IO.println s!"ownership: {controls.size} controls of the sealed-constant rule reported, each for its intended constant, 2 of them by the direct part alone"
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
