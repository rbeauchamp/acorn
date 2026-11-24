import Lean
import Acorn.Provenance
import AcornTools.TrackedFiles

namespace AcornDepartureAudit
open Lean Acorn

def key : Departure → String
  | .featureChannels => "D1"
  | .spatialPotentials => "D2"
  | .explorationDuration => "D3"
  | .learnerParameters => "D4"
  | .cumulants => "D5"
  | .explorationRate => "D6"
  | .featureTester => "D7"
  | .achievementEvent => "D8"

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

def check (env : Environment) (maintained : Array Name) : IO Unit := do
  let departures : List Departure := [.featureChannels, .spatialPotentials,
    .explorationDuration, .learnerParameters, .cumulants, .explorationRate, .featureTester,
    .achievementEvent]
  let some (.inductInfo declaration) := env.find? `Acorn.Departure
    | throw (IO.userError "departure type is not a compiled inductive")
  require (declaration.ctors.length == departures.length &&
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
  AcornTrackedFiles.ensureTrackedRegular ".." "" "docs/learned-only-binding.md"
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
