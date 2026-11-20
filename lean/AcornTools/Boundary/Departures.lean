/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean

/-! # Closed departure ownership

The closed departure type and complete compiled quarantine-module/type inventory
are bound to the maintained register. Composite state types declare all consumed
origins here; signal producers additionally carry their executable Provenance
contracts. Review checks each declared origin against the producing code.

This module imports no project module, as every gate tool must
(`AcornBoundaryAudit.toolImports`): the boundary audit is the first program a run builds, before
any source has been admitted. It keeps its own copy of the departures, `Departure`, and `check`
requires the compiled `Acorn.Departure` to have exactly those constructors, by name: the same
ones, each once, in any order. The compiled type must take no parameter or index and its
constructors must take no fields. Its sort must be above `Prop` at every universe
instantiation, so proof irrelevance cannot identify constructors with different register keys.
-/
namespace AcornDepartureAudit
open Lean

/-- The departures, as this audit lists them: one constructor for each constructor of the
compiled `Acorn.Departure`, with the same name. -/
inductive Departure where
  /-- `Acorn.Departure.featureChannels`. -/
  | featureChannels
  /-- `Acorn.Departure.spatialPotentials`. -/
  | spatialPotentials
  /-- `Acorn.Departure.explorationDuration`. -/
  | explorationDuration
  /-- `Acorn.Departure.learnerParameters`. -/
  | learnerParameters
  /-- `Acorn.Departure.cumulants`. -/
  | cumulants
  /-- `Acorn.Departure.explorationRate`. -/
  | explorationRate
  /-- `Acorn.Departure.featureTester`. -/
  | featureTester
  /-- `Acorn.Departure.achievementEvent`. -/
  | achievementEvent

/-- The constructor of the compiled `Acorn.Departure` that a departure stands for. -/
def Departure.compiled : Departure → Name
  | .featureChannels => `Acorn.Departure.featureChannels
  | .spatialPotentials => `Acorn.Departure.spatialPotentials
  | .explorationDuration => `Acorn.Departure.explorationDuration
  | .learnerParameters => `Acorn.Departure.learnerParameters
  | .cumulants => `Acorn.Departure.cumulants
  | .explorationRate => `Acorn.Departure.explorationRate
  | .featureTester => `Acorn.Departure.featureTester
  | .achievementEvent => `Acorn.Departure.achievementEvent

/-- Every constructor has a register key; adding a departure requires this total match. -/
def key : Departure → String
  | .featureChannels => "D1"
  | .spatialPotentials => "D2"
  | .explorationDuration => "D3"
  | .learnerParameters => "D4"
  | .cumulants => "D5"
  | .explorationRate => "D6"
  | .featureTester => "D7"
  | .achievementEvent => "D8"

/-- Maintained loci include compositions; adding a quarantined module requires admission. -/
def modules : List (Name × List Departure) :=
  [(`Acorn.Handcrafted.Signals, [.featureChannels, .cumulants]),
   (`Acorn.Handcrafted.Observation, [.featureChannels, .spatialPotentials, .cumulants]),
   (`Acorn.Handcrafted.Cumulants, [.cumulants]),
   (`Acorn.Handcrafted.GridWorld, [.featureChannels, .spatialPotentials, .cumulants,
     .achievementEvent]),
   (`Acorn.Handcrafted.Microduck, [.featureChannels, .cumulants, .achievementEvent]),
   (`Acorn.Handcrafted.FeatureProfile, [.featureChannels, .spatialPotentials, .explorationRate,
     .featureTester]),
   (`Acorn.Handcrafted.TemporalProfile, [.spatialPotentials, .explorationRate]),
   (`Acorn.Handcrafted.PredictionControl, [.featureChannels, .cumulants, .learnerParameters]),
   (`Acorn.Handcrafted.TemporalControl, [.spatialPotentials, .explorationDuration,
     .learnerParameters, .cumulants, .explorationRate, .achievementEvent]),
   (`Acorn.Handcrafted.AgentAlignment, [.spatialPotentials, .achievementEvent]),
   (`Acorn.Handcrafted.AgentEpisodes, [.spatialPotentials, .achievementEvent]),
   (`Acorn.Handcrafted.DrawFirst, [.spatialPotentials, .explorationDuration,
     .learnerParameters, .explorationRate, .achievementEvent]),
   (`Acorn.Handcrafted.Agent, [.featureChannels, .spatialPotentials, .explorationDuration,
     .learnerParameters, .cumulants, .explorationRate, .featureTester, .achievementEvent]),
   (`Acorn.Handcrafted.StepParts, [.featureChannels, .spatialPotentials, .explorationDuration,
     .learnerParameters, .cumulants, .explorationRate, .featureTester, .achievementEvent])]

/-- Every quarantine data type is a declared producer, immutable profile or
composite state/proof relation. Newly elaborated inductive types fail closed. -/
def types : List Name :=
  [`Acorn.Handcrafted.TaskFeatureMode, `Acorn.Handcrafted.Predictions,
   `Acorn.Handcrafted.SpatialInterest, `Acorn.Handcrafted.EvaluationMode,
   `Acorn.Handcrafted.ControlCredit, `Acorn.Handcrafted.RatePolicy,
   `Acorn.Handcrafted.SubtaskPolicy, `Acorn.Handcrafted.FeatureProfile,
   `Acorn.Handcrafted.PredictionControl, `Acorn.Handcrafted.RateState,
   `Acorn.Handcrafted.TemporalControl, `Acorn.Handcrafted.EpisodeTrace,
   `Acorn.Handcrafted.Agent, `Acorn.Handcrafted.AgentImage, `Acorn.Handcrafted.Chosen,
   `Acorn.Handcrafted.StartDraw, `Acorn.Handcrafted.Owed]

private def require (legal : Bool) (message : String) : IO Unit :=
  unless legal do throw (IO.userError s!"departure ownership: {message}")

/-- Compiler metadata supplies the complete constructor and public/private type
inventory. Documents must name every module in every declared departure it uses.
`maintained` are the governed discovered sources, which hold every quarantine module. -/
def check (env : Environment) (maintained : Array Name) : IO Unit := do
  let departures : List Departure := [.featureChannels, .spatialPotentials,
    .explorationDuration, .learnerParameters, .cumulants, .explorationRate, .featureTester,
    .achievementEvent]
  let some (.inductInfo declaration) := env.find? `Acorn.Departure
    | throw (IO.userError "departure type is not a compiled inductive")
  let .sort level := declaration.type
    | throw (IO.userError "departure type must be a data sort")
  require level.isNeverZero "departure type must be above Prop at every universe instantiation"
  let compiled := departures.map Departure.compiled
  let fieldless := declaration.ctors.all fun constructor =>
    match env.find? constructor with
    | some (.ctorInfo info) => info.numFields == 0
    | _ => false
  require (declaration.numParams == 0 && declaration.numIndices == 0 && fieldless &&
    declaration.ctors.length == compiled.length &&
    compiled.eraseDups.length == compiled.length && compiled.all declaration.ctors.contains &&
    (departures.map key).eraseDups.length == departures.length) "closed departure domain differs"
  let owners := maintained.toList.filter (`Acorn.Handcrafted).isPrefixOf
  require (owners.length == modules.length && owners.all (modules.map Prod.fst).contains &&
    (modules.map Prod.fst).eraseDups.length == modules.length) "quarantine module inventory differs"
  let mut actual := []
  for (name, info) in env.constants do
    if let .inductInfo _ := info then
      if let some index := env.getModuleIdxFor? name then
        if let some owner := (env.header.modules[index.toNat]?).map (·.module) then
          if owners.contains owner then actual := name :: actual
  require (actual.length == types.length && actual.all types.contains)
    s!"quarantine data-type inventory differs: {actual}"
  let text ← IO.FS.readFile "../docs/learned-only-binding.md"
  let entries := ((text.splitOn "### D").drop 1).map fun entry =>
    ("D" ++ (entry.takeWhile Char.isDigit).toString, entry)
  require (entries.length == departures.length &&
    (entries.map Prod.fst).eraseDups.length == entries.length) "register entry inventory differs"
  for departure in departures do
    let some (_, entry) := entries.find? (fun row => row.1 == key departure)
      | throw (IO.userError s!"missing register {key departure}")
    require (entry.contains "*Replacement:*") s!"{key departure} omits replacement search"
    for (owner, origins) in modules do
      if origins.any (fun origin => key origin == key departure) then
        require (entry.contains s!"`{owner}`") s!"{key departure} omits locus {owner}"
  IO.println "departures: compiled domain, quarantine modules/types and register loci admitted"

end AcornDepartureAudit
