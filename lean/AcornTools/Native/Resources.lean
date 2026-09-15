/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean
import AcornVerif.Resource.WordKernel

/-!
# Admission of actual numerical compiler IR

The extractor admits finite scalar execution and a checked u32 halving loop.
It constructs the
formal resource tree from the compiler's own declarations. It is a trusted
build-time extraction boundary, not a verified compiler. Native lowering and
the pinned scalar primitives remain trusted. No source-name blacklist or
separately authored numerical evaluator stands in for the extracted body.
-/

namespace AcornNativeResourceAudit
open Lean Lean.IR AcornVerif.Resource

/-- Only unboxed fixed-width words, booleans and native floats enter this resource boundary. -/
def wordType : IRType → Bool
  | .uint8 | .uint32 | .uint64 | .float | .float32 => true
  | _ => false

/-- Closed pinned-runtime primitive domain. Declaration signatures are checked
as well; all other external operations fail admission. -/
def primitive (name : Name) : Bool :=
  #[`UInt64.land, `UInt64.lor, `UInt64.xor, `UInt64.add, `UInt64.sub,
    `UInt64.div, `UInt64.mod, `UInt64.log2, `UInt32.toUInt64,
    `UInt32.xor, `UInt32.land, `UInt32.shiftRight, `Float32.ofBits, `Float32.toFloat, `UInt64.neg, `UInt64.toFloat, `Float.toBits, `Float.ofBits, `Float.add, `Float.sub, `Float.mul, `Float.div,
    `Float.toFloat32, `Float32.toBits, `Float32.add, `Float32.sub, `Float32.mul, `Float32.div, `UInt64.toFloat32, `UInt32.shiftLeft, `UInt32.lor, `UInt32.sub,
    `UInt32.add, `UInt32.mod, `UInt64.mul, `UInt32.decEq, `UInt32.decLt, `UInt32.decLe,
    `UInt64.shiftLeft, `UInt64.shiftRight, `UInt64.decLt, `UInt64.decLe,
    `UInt64.decEq, `UInt64.toUInt32, `Int32.neg, `Int64.toInt, `Int64.ofInt, `UInt32.toNat, `Int64.neg, `Int32.sub, `Int32.toInt64].contains name

/-- These interval consumers borrow the compiler's two-u32 endpoint record.
Allocation and ownership transfer remain outside the numerical kernel. -/
def intervalReader (name : Name) : Bool :=
  #[`Acorn.Interval32.instDecidableContains, `Acorn.Interval32.saturate].contains name

/-- Only these fixed-width conversions may produce an integer object.
Their allocation-capable native costs stay explicit in the primitive model. -/
def integerEgress (name : Name) : Bool :=
  #[`Int64.toInt, `Int64.ofInt, `UInt32.toNat, `Acorn.Conversion.toI64,
    `Acorn.Host.coordinateCast, `Acorn.Features.durationRemaining].contains name

/-- Bounded coordinate values cross one native signed conversion at ingress.
The source Coordinate refinement and coordinateIngress_exact own its domain. -/
def integerIngress (name : Name) : Bool :=
  #[`Int64.ofInt, `Acorn.Host.coordinateFloat, `Acorn.Host.coordinateWord].contains name

/-- The admitted borrowed-record signature is exact, not a general object exemption. -/
def admittedSignature (declaration : Decl) : Bool :=
  if integerIngress declaration.name then
    declaration.params.size == 1 && declaration.params[0]!.ty == .tobject &&
      declaration.params[0]!.borrow && wordType declaration.resultType
  else if intervalReader declaration.name then
    declaration.params.size == 2 && declaration.params[0]!.ty == .object &&
      declaration.params[0]!.borrow && declaration.params[1]!.ty == .uint32 &&
      wordType declaration.resultType
  else declaration.params.all (fun p => wordType p.ty) &&
    (wordType declaration.resultType ||
      (integerEgress declaration.name && declaration.resultType == .tobject))

/-- Lexically visible join bodies; jumps are expanded with cycle detection. -/
abbrev Joins := List (JoinPointId × Array Param × FnBody)

/-- Extraction requests share one decreasing admission budget. The budget
bounds the checker, never serves as a claimed program execution bound. -/
inductive Request where
  /-- Expand a direct declaration with its current call ancestry. -/
  | decl (name : Name) (calls : List Name)
  /-- Expand a body with its lexical joins and current jump ancestry. -/
  | body (owner : Name) (body : FnBody) (calls : List Name)
      (joins : Joins) (jumps : List JoinPointId)

/-- Fail-closed extraction from typed native compiler IR. Every accepted
instruction contributes to the formal tree; join declarations themselves do
not execute, while their reachable bodies are accounted at each jump. -/
def extract (env : Environment) (onceSymbols globalSymbols : List String) (startup : Bool) (cutTail : Option Name) (power : Option WordTree) : Nat → Request → Except String WordTree
  | 0, _ => .error "resource extraction depth exceeded"
  | fuel + 1, request => do
    match request with
    | .decl name calls =>
      if calls.contains name then throw s!"recursive resource path: {name}"
      let some declaration := Lean.IR.findEnvDecl env name
        | throw s!"missing compiler IR: {name}"
      unless admittedSignature declaration || (startup && declaration.params.isEmpty &&
          (declaration.resultType == .object || declaration.resultType == .tobject)) do
        throw s!"non-word signature: {name}"
      if name == `Acorn.Portable.powLoopWord then
        if let some body := power then return body.repeatBody 33
      match declaration with
      | .extern .. =>
        unless primitive name do throw s!"unadmitted native primitive: {name}"
        return .step (.primitive name.toString) .done
      | .fdecl _ _ _ body _ => extract env onceSymbols globalSymbols startup cutTail power fuel (.body name body (name :: calls) [] [])
    | .body owner body calls joins jumps =>
      let next (b : FnBody) := extract env onceSymbols globalSymbols startup cutTail power fuel (.body owner b calls joins jumps)
      match body with
      | .vdecl _ ty expression rest =>
        let egress := match expression with
          | .fap name _ => integerEgress owner && integerEgress name && ty == .tobject
          | _ => false
        unless wordType ty || egress || (startup && (ty == .object || ty == .tobject || ty == .tagged)) do throw s!"non-word local in {owner}"
        let instruction ← match expression with
          | .lit (.num _) => pure (.step .literal .done)
          | .ctor info args => do
            unless startup && #[`List.cons, `List.nil, `Option.some, `Option.none].contains info.name &&
                args.size == info.size && info.usize == 0 && info.ssize == 0 do
              throw "unadmitted startup constructor"
            pure (.step (.allocate info.size info.ssize) .done)
          | .box scalar _ => do
            unless startup && wordType scalar do throw "unadmitted scalar boxing"
            pure (.step (.box (toString (repr scalar))) .done)
          | .sproj 0 offset record => do
            let some declaration := Lean.IR.findEnvDecl env owner
              | throw "missing interval reader"
            unless intervalReader owner && admittedSignature declaration &&
                declaration.params[0]!.x == record && ty == .uint32 &&
                (offset == 0 || offset == 4) do throw "unadmitted record projection"
            pure (.step .scalarRead .done)
          | .fap name arguments => do
            if onceSymbols.contains (Lean.getSymbolStem env name) ||
                globalSymbols.contains (Lean.getSymbolStem env name) then
              unless arguments.isEmpty do throw s!"once-cell arguments: {name}"
              let some declaration := Lean.IR.findEnvDecl env name
                | throw s!"missing once-cell IR: {name}"
              unless declaration.params.isEmpty &&
                  (wordType declaration.resultType || (startup &&
                    (declaration.resultType == .object || declaration.resultType == .tobject))) do
                throw s!"non-scalar once-cell: {name}"
              pure (.step (.cacheRead name.toString (onceSymbols.contains (Lean.getSymbolStem env name))) .done)
            else
              let called ← if cutTail == some owner && name == owner then
                  match rest with
                  | .ret (.var _) => pure WordTree.done
                  | _ => throw s!"non-tail cut in {owner}"
                else extract env onceSymbols globalSymbols startup cutTail power fuel (.decl name calls)
              pure (.step (.call name.toString) called)
          | _ => throw s!"unadmitted scalar expression in {owner}"
        return .seq instruction (← next rest)
      | .jdecl id parameters target rest =>
        unless parameters.all (fun p => wordType p.ty) do
          throw s!"non-word join in {owner}"
        if joins.any (fun entry => entry.1 == id) then throw s!"duplicate join in {owner}"
        extract env onceSymbols globalSymbols startup cutTail power fuel (.body owner rest calls ((id, parameters, target) :: joins) jumps)
      | .jmp id arguments =>
        if jumps.contains id then throw s!"cyclic join in {owner}"
        let some (_, parameters, target) := joins.find? (fun entry => entry.1 == id)
          | throw s!"missing join in {owner}"
        unless arguments.size == parameters.size do throw s!"join arity in {owner}"
        return .step .transfer (← extract env onceSymbols globalSymbols startup cutTail power fuel (.body owner target calls joins (id :: jumps)))
      | .case tid _ ty alternatives =>
        unless (tid == `Bool || tid == `UInt8) && ty == .uint8 && alternatives.size == 2 do
          throw s!"unadmitted branch domain in {owner}: {tid}, {repr ty}, {alternatives.size}"
        let mut branches := #[]
        for alternative in alternatives do
          match alternative with
          | .ctor info b =>
            unless (info.name == `Bool.false || info.name == `Bool.true) && !info.isRef do
              throw s!"unadmitted branch constructor in {owner}: {repr info}"
            branches := branches.push (← next b)
          | .default b => branches := branches.push (← next b)
        let some left := branches[0]? | throw s!"missing left branch in {owner}"
        let some right := branches[1]? | throw s!"missing right branch in {owner}"
        return .branch left right
      | .inc _ count _ _ rest =>
        unless startup && count == 1 do throw "unadmitted reference-count operation"
        return .step .retain (← next rest)
      | .ret (.var _) => return .step .transfer .done
      | _ => throw s!"unadmitted control or heap operation in {owner}: {Lean.IR.formatFnBodyHead body}"

/-- Dataflow facts admitted for the one fixed-width halving recurrence. -/
inductive CounterOrigin where
  /-- The original u32 counter argument. -/
  | counter
  /-- A scalar literal, retaining its value. -/
  | literal (value : Nat)
  /-- Exactly the original counter shifted right by one. -/
  | half
  /-- Exactly the original counter compared equal to zero. -/
  | zeroGuard
  /-- No useful counter fact. -/
  | other
  deriving BEq

/-- Lexically available scalar dataflow facts. -/
abbrev Origins := List (VarId × CounterOrigin)

/-- Read a fact only from the compiler variable actually supplied as an argument. -/
def origin (facts : Origins) : Arg → CounterOrigin
  | .var id => (facts.find? (fun entry => entry.1 == id)).map Prod.snd |>.getD .other
  | _ => .other

/-- Recognize the exact fixed-width recurrence and its zero predicate. -/
def expressionOrigin (facts : Origins) : IR.Expr → CounterOrigin
  | .lit (.num value) => .literal value
  | .fap name args =>
    if args.size != 2 then .other
    else if name == `UInt32.shiftRight && origin facts args[0]! == .counter &&
        origin facts args[1]! == .literal 1 then .half
    else if name == `UInt32.decEq && origin facts args[0]! == .counter &&
        origin facts args[1]! == .literal 0 then .zeroGuard
    else .other
  | _ => .other

/-- Validate every return and back edge against the dominating counter guard.
Join arguments propagate facts; unrecognized control fails closed. -/
def checkHalving (owner : Name) : Nat → FnBody → Origins → Joins →
    List JoinPointId → Option Bool → Except String Nat
  | 0, _, _, _, _, _ => .error "halving extraction depth exceeded"
  | fuel + 1, body, facts, joins, jumps, nonzero => do
    match body with
    | .vdecl id ty expression rest =>
      match expression with
      | .fap name args =>
        if name == owner then
          unless nonzero == some true && args.size == 3 &&
              origin facts args[2]! == .half && ty == .uint64 do
            throw "unproved halving back edge"
          match rest with
          | .ret (.var result) =>
            unless result == id do throw "halving call result is not returned"
            return 1
          | _ => throw "halving call is not in tail position"
      | _ => pure ()
      checkHalving owner fuel rest ((id, expressionOrigin facts expression) :: facts)
        joins jumps nonzero
    | .jdecl id parameters target rest =>
      if joins.any (fun entry => entry.1 == id) then throw "duplicate halving join"
      checkHalving owner fuel rest facts ((id, parameters, target) :: joins) jumps nonzero
    | .jmp id arguments =>
      if jumps.contains id then throw "cyclic halving join"
      let some (_, parameters, target) := joins.find? (fun entry => entry.1 == id)
        | throw "missing halving join"
      unless arguments.size == parameters.size do throw "halving join arity"
      let assigned := (parameters.zip arguments).toList.map fun (parameter, argument) =>
        (parameter.x, origin facts argument)
      checkHalving owner fuel target (assigned ++ facts) joins (id :: jumps) nonzero
    | .case _ id _ alternatives =>
      let guard := origin facts (.var id) == .zeroGuard
      let mut edges := 0
      for alternative in alternatives do
        match alternative with
        | .ctor info branch =>
          let state ← if guard then
              if info.name == `Bool.false then pure (some true)
              else if info.name == `Bool.true then pure (some false)
              else throw "unknown halving guard constructor"
            else pure nonzero
          edges := edges + (← checkHalving owner fuel branch facts joins jumps state)
        | .default branch =>
          if guard then throw "ambiguous halving guard default"
          edges := edges + (← checkHalving owner fuel branch facts joins jumps nonzero)
      return edges
    | .ret (.var _) =>
      unless nonzero == some false do throw "halving return without zero guard"
      return 0
    | _ => throw "unadmitted halving control"

/-- Extract the admitted loop body only after proving its counter dataflow at
the trusted compiler boundary. The mathematical owner supplies 33 body visits. -/
def extractHalving (env : Environment) (onceSymbols globalSymbols : List String) (owner : Name) : Except String WordTree := do
  let some (.fdecl _ parameters result body _) := Lean.IR.findEnvDecl env owner
    | throw "missing halving compiler declaration"
  unless parameters.size == 3 && parameters[0]!.ty == .uint64 &&
      parameters[1]!.ty == .uint64 && parameters[2]!.ty == .uint32 && result == .uint64 do
    throw "unexpected halving signature"
  let edges ← checkHalving owner 4096 body [(parameters[2]!.x, .counter)] [] [] none
  unless 0 < edges do throw "halving declaration has no recurrence"
  extract env onceSymbols globalSymbols false (some owner) none 4096 (.decl owner [])

/-- Once-cell dependencies are collected from the extracted execution tree. -/
def onceNames : WordTree → List String
  | .done => []
  | .step (.cacheRead name _) next => name :: onceNames next
  | .step _ next => onceNames next
  | .seq first next | .branch first next => onceNames first ++ onceNames next

/-- Close and deduplicate first-use dependencies by their compiler identities.
All initializer bodies pass the same scalar admission as recurring execution. -/
def initializerClosure (env : Environment) (onceSymbols globalSymbols : List String) : Nat → List (String × List String) → List InitCell →
    Except String (List InitCell)
  | 0, _, _ => .error "initializer closure depth exceeded"
  | fuel + 1, pending, admitted => do
    match pending with
    | [] => return admitted
    | (name, ancestors) :: rest =>
      if ancestors.contains name then throw s!"cyclic initializer: {name}"
      if admitted.any (fun cell => cell.name == name) then
        initializerClosure env onceSymbols globalSymbols fuel rest admitted
      else
        let tree ← extract env onceSymbols globalSymbols true none none 4096 (.decl name.toName [])
        initializerClosure env onceSymbols globalSymbols fuel
          ((onceNames tree).map (fun child => (child, name :: ancestors)) ++ rest)
          (⟨name, tree⟩ :: admitted)

/-- Concrete roots correspond to the actual numerical implementations consumed
by the exponential path; native routing is checked separately. -/
def roots : Array (Name × Nat) :=
  #[(`Acorn.Binary32.add, 9), (`Acorn.Binary32.sub, 9),
    (`Acorn.Binary32.mul, 9), (`Acorn.Binary32.div, 9), (`Acorn.Binary32.ofUInt64, 5),
    (`Acorn.Binary64.add, 9), (`Acorn.Binary64.sub, 9), (`Acorn.Binary64.mul, 9),
    (`Acorn.Binary64.div, 9), (`Acorn.Binary64.ofUInt64, 5),
    (`Acorn.Word.multiplyHigh, 69), (`Acorn.Word.below, 71),
    (`Acorn.Host.coordinateFloatWord, 18), (`Acorn.Host.coordinateFloat, 22),
    (`Acorn.Host.coordinateWord, 3), (`Acorn.Binary64.less, 48), (`Acorn.Conversion.toI32Word, 59), (`Acorn.Portable.powerOfTwoWord, 9),
    (`Acorn.Rounding.nearestEvenWord, 24), (`Acorn.Rounding.wordShift64, 35),
    (`Acorn.Conversion.roundedNormal, 46), (`Acorn.Conversion.subnormalFractionWord, 70),
    (`Acorn.Conversion.normalMagnitude, 78),
    (`Acorn.Conversion.ofI64Word, 15), (`Acorn.Conversion.ofI32Word, 19),
    (`Acorn.Conversion.narrow, 105), (`Acorn.Portable.expSeries, 254),
    (`Acorn.Portable.lnSeries, 186), (`Acorn.Conversion.widen, 65), (`Acorn.Binary32.less, 48),
    (`Acorn.Binary32.numericallyEqual, 54), (`Acorn.Binary32.lessOrEqual, 70),
    (`Acorn.Binary32.isZero, 7), (`Acorn.Conversion.toI64Word, 60),
    (`Acorn.Host.floor32, 69), (`Acorn.Portable.exp, 762), (`Acorn.Portable.ln, 658), (`Acorn.Portable.pow, 1396), (`Acorn.Conversion.cappedTrunc128, 45),
    (`Acorn.Features.durationWord, 128), (`Acorn.Binary32.positiveDecidable, 22),
    (`Acorn.Binary32.instDecidableFinite, 9), (`Acorn.Binary64.instDecidableFinite, 9),
    (`Acorn.Interval32.orderedDecidable, 70),
    (`Acorn.Interval32.instDecidableContains, 112), (`Acorn.Interval32.saturate, 115), (`Acorn.Conversion.toI64, 64),
    (`Acorn.Host.coordinateCast, 132), (`Acorn.Features.durationRemaining, 132)]

/-- Read actual compiler-owned once declarations. The closed-term cache is
not persistent across imports, so the standalone audit uses emitted C and the
pinned compiler's symbol mangling. Scalar types are checked again against IR. -/
def readOnceSymbols : Nat → System.FilePath → IO (List String)
  | 0, _ => throw (IO.userError "compiler directory depth exceeded")
  | fuel + 1, directory => do
    let mut result := []
    for entry in ← directory.readDir do
      let kind := (← entry.path.symlinkMetadata).type
      if kind == .dir then result := result ++ (← readOnceSymbols fuel entry.path)
      else if entry.path.extension == some "c" then
        unless kind == .file do throw (IO.userError s!"non-regular compiler source: {entry.path}")
        let source ← IO.FS.readFile entry.path
        for line in source.splitOn "\n" do
          let declarationStart := "static lean_once_cell_t "
          let suffix := "_once = LEAN_ONCE_CELL_INITIALIZER;"
          if line.startsWith declarationStart && line.endsWith suffix then
            let symbol := ((line.drop declarationStart.length).toString.dropEnd suffix.length).toString
            unless ["uint8_t", "uint32_t", "uint64_t", "float", "double", "lean_object*"].any
                (fun ty => (source.splitOn s!"static {ty} {symbol};").length > 1) do
              continue
            result := symbol :: result
    return result


/-- Compiler-emitted eager numerical initializers are startup roots. Match
both the assigned symbol and the actual initializer call, then require its IR. -/
def eagerInitializers (env : Environment) : IO (List Name × List String) := do
  let mut names := []
  let mut symbols := []
  for owner in ["Encoding", "Admission", "Arithmetic", "Rounding", "Conversion", "Portable",
      "Word", "Host/Terrain", "Exploration"] do
    let path : System.FilePath := s!".lake/build/ir/Acorn/{owner}.c"
    unless (← path.symlinkMetadata).type == .file do throw (IO.userError s!"invalid artifact {path}")
    let source ← IO.FS.readFile path
    for line in source.splitOn "\n" do
      let parts := line.splitOn " = _init_"
      if parts.length == 2 then
        let symbol := parts[0]!
        unless parts[1]! == symbol ++ "();" do
          throw (IO.userError s!"ambiguous numerical initializer: {line}")
        unless symbol.startsWith "lp_acorn_" do
          throw (IO.userError s!"unrecognized numerical symbol: {symbol}")
        let name := Name.demangle (symbol.drop "lp_acorn_".length).toString
        unless Lean.getSymbolStem env name == symbol && (Lean.IR.findEnvDecl env name).isSome do
          throw (IO.userError s!"initializer without matching IR: {symbol}")
        names := name :: names
        symbols := symbol :: symbols
  return (names, symbols)

/-- Load current compiler declarations and reject any root leaving the admitted
fragment. Lake freshness and module-origin gates run in the enclosing suite. -/
unsafe def audit : IO Unit := do
  initSearchPath (← findSysroot)
  -- IR and symbol queries read imported metadata; no project initializer runs.
  withImportModules #[{ module := `Acorn }] {} fun env => do
    let (eagerNames, globalSymbols) ← eagerInitializers env
    let onceSymbols ← readOnceSymbols 16 ".lake/build/ir/Acorn"
    let loop ← match extractHalving env onceSymbols globalSymbols `Acorn.Portable.powLoopWord with
      | .ok tree => pure tree
      | .error reason => throw (IO.userError s!"native resource: {reason}")
    IO.println s!"native resource: powLoopWord: ≤ 33 × {loop.bound} abstract units; checked u32 halving"
    let mut initializers := eagerNames.map Name.toString ++ onceNames loop
    for (root, limit) in roots do
      match extract env onceSymbols globalSymbols false none (some loop) 4096 (.decl root []) with
      | .error reason => throw (IO.userError s!"native resource: {reason}")
      | .ok tree =>
        initializers := initializers ++ onceNames tree
        let some admitted := tree.admit limit
          | throw (IO.userError s!"native resource: {root}: bound {tree.bound} exceeds budget {limit}")
        IO.println s!"native resource: {root}: ≤ {admitted.tree.bound}/{limit} abstract units; only admitted scalar operations and bounded integer adapters"

    let cells ← match initializerClosure env onceSymbols globalSymbols 4096 (initializers.map (·, [])) [] with
      | .ok cells => pure cells
      | .error reason => throw (IO.userError s!"native resource: {reason}")
    unless cells.length ≤ 68 && initCredit (fun _ => 1) cells ≤ 575 do
      throw (IO.userError "numerical initializer count or startup budget exceeded")
    IO.println s!"native resource: {cells.length} distinct numerical cached initializers; startup/first-use bound {initCredit (fun _ => 1) cells} abstract units"

end AcornNativeResourceAudit
