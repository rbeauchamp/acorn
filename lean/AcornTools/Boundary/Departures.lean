/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean
import Acorn.Provenance

/-! # Closed departure ownership

The closed departure type and complete compiled quarantine-module/type inventory
are bound to the maintained register. Composite state types declare all consumed
origins here; signal producers additionally carry their executable Provenance
contracts. Review checks each declared origin against the producing code.

Declaring a departure is required. Admitting one is the owner's and is its own change: the
closed type `Acorn.Departure`, which this audit requires to be declared in `Acorn.Provenance`,
the register `docs/learned-only-binding.md` and this module are each named by
`.github/CODEOWNERS`, and the merge gate refuses a change to one that carries no admission
(`scripts/admission.sh`). A declared departure is no evidence of learning. What this audit
accepts is where a mechanism is declared, never what it is: a mechanism added inside a module
that an admitted departure already covers passes it.
-/
namespace AcornDepartureAudit
open Lean Acorn

/-- Every constructor has a register key; adding a departure requires this total match, a change
to this module, which is the owner's to admit. -/
def key : Departure → String
  | .featureChannels => "D1"
  | .spatialPotentials => "D2"
  | .explorationDuration => "D3"
  | .learnerParameters => "D4"
  | .cumulants => "D5"
  | .explorationRate => "D6"
  | .featureTester => "D7"
  | .achievementEvent => "D8"

/-- Maintained loci include compositions; adding a quarantined module requires a change to this
list, which is the owner's to admit. -/
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
  -- The register is declared in the module `.github/CODEOWNERS` names, so a change that moves
  -- it to a module outside the owner's paths fails here.
  let home := (env.getModuleIdxFor? `Acorn.Departure).bind fun index =>
    (env.header.modules[index.toNat]?).map (·.module)
  require (home == some `Acorn.Provenance) "the departure type is declared outside Acorn.Provenance"
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
