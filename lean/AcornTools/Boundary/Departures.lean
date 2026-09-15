/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Provenance
import AcornTools.Ownership

/-! # Closed departure ownership

The closed departure type and complete compiled quarantine-module/type inventory
are bound to the maintained register. Composite state types declare all consumed
origins here; signal producers additionally carry their executable Provenance
contracts. Neither mechanism establishes that a declaration is scientifically true.
-/
namespace AcornDepartureAudit
open Lean Acorn

/-- Every constructor has a register key; adding a departure requires this total match. -/
def key : Departure → String
  | .featureChannels => "D1"
  | .spatialPotentials => "D2"
  | .explorationDuration => "D3"
  | .learnerParameters => "D4"
  | .cumulants => "D5"

/-- Maintained loci include compositions; adding a quarantined module requires admission. -/
def modules : List (Name × List Departure) :=
  [(`Acorn.Handcrafted.Observation, [.featureChannels, .spatialPotentials, .cumulants]),
   (`Acorn.Handcrafted.Cumulants, [.cumulants]),
   (`Acorn.Handcrafted.FeatureProfile, [.featureChannels, .spatialPotentials, .explorationDuration]),
   (`Acorn.Handcrafted.TemporalProfile, [.spatialPotentials, .explorationDuration]),
   (`Acorn.Handcrafted.PredictionControl, [.featureChannels, .cumulants, .learnerParameters]),
   (`Acorn.Handcrafted.TemporalControl, [.spatialPotentials, .explorationDuration, .learnerParameters]),
   (`Acorn.Handcrafted.AgentAlignment, [.spatialPotentials]),
   (`Acorn.Handcrafted.AgentEpisodes, [.spatialPotentials]),
   (`Acorn.Handcrafted.Agent, [.featureChannels, .spatialPotentials, .explorationDuration, .learnerParameters, .cumulants])]

/-- Every quarantine data type is a declared producer, immutable profile or
composite state/proof relation. Newly elaborated inductive types fail closed. -/
def types : List Name :=
  [`Acorn.Handcrafted.TaskFeatureMode, `Acorn.Handcrafted.Predictions,
   `Acorn.Handcrafted.SpatialInterest, `Acorn.Handcrafted.EvaluationMode,
   `Acorn.Handcrafted.ControlCredit, `Acorn.Handcrafted.RatePolicy,
   `Acorn.Handcrafted.SubtaskPolicy, `Acorn.Handcrafted.FeatureProfile,
   `Acorn.Handcrafted.PredictionControl, `Acorn.Handcrafted.RateState,
   `Acorn.Handcrafted.TemporalControl, `Acorn.Handcrafted.EpisodeTrace,
   `Acorn.Handcrafted.Agent, `Acorn.Handcrafted.AgentImage]

private def require (legal : Bool) (message : String) : IO Unit :=
  unless legal do throw (IO.userError s!"departure ownership: {message}")

/-- Compiler metadata supplies the complete constructor and public/private type
inventory. Documents must name every module in every declared departure it uses. -/
def check (env : Environment) : IO Unit := do
  let departures : List Departure := [.featureChannels, .spatialPotentials,
    .explorationDuration, .learnerParameters, .cumulants]
  let some (.inductInfo declaration) := env.find? `Acorn.Departure
    | throw (IO.userError "departure type is not a compiled inductive")
  require (declaration.ctors.length == departures.length &&
    (departures.map key).eraseDups.length == departures.length) "closed departure domain differs"
  let owners := AcornOwnership.modules.toList.filter (`Acorn.Handcrafted).isPrefixOf
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
