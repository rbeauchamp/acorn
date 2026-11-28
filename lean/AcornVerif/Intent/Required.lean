import AcornVerif.Intent.BeforeFixes
import AcornVerif.Intent.Decisions
import AcornVerif.Intent.OneStreamBlindCompare
import AcornVerif.Intent.WorldInterfaceBlindReading

namespace AcornVerif.Intent.Required

open LeanIntent
open AcornVerif.Intent.DayCycle
open AcornVerif.Intent.Decisions
open AcornVerif.Intent.Hash
open AcornVerif.Intent.WorldInterface
open AcornVerif.Intent.OneStream

theorem day_o2 : O2 dayCycle :=
  dayCycle_o2 (lo := 0) (hi := 1) (by decide) quarterSight

theorem day_o2Run : O2Run dayCycle :=
  dayCycle_o2Run (lo := 0) (hi := 1) (by decide) quarterSight_injective

theorem day_o3 : O3 dayCycle :=
  dayCycle_o3 () .wait (lo := 0) (hi := 1) (Nat.lt_irrefl 0) quarterSight

theorem day_o4 : O4 dayCycle :=
  dayCycle_o4

theorem day_o5 : O5 dayCycle .widest :=
  dayCycle_o5_widest

theorem day_not_o5_eq : ¬ O5 dayCycle .eq :=
  dayCycle_not_o5_eq (lo := 0) (hi := 1) (by decide) quarterSight_injective

theorem day_everyDayAlike :
    (everyDayAlike (Ctx := Unit) (Act := Acorn.Host.Action) (Obs := UInt8) (E := Nat)).HoldsOf
      dayCycle :=
  everyDayAlike_holds

theorem day_seesQuarter :
    (seesQuarterOfDay (Ctx := Unit) (Act := Acorn.Host.Action) (Obs := UInt8) (E := Nat)).HoldsOf
      dayCycle :=
  seesQuarterOfDay_holds

theorem day_refutes_dayOrNightOnly :
    ¬ dayCycle.Meets (dayOrNightOnly (lo := 0) (hi := 1) (0 : UInt8) (4 : UInt8)) :=
  dayCycle_refutes_dayOrNightOnly () (lo := 0) (hi := 1) 0 4

theorem day_nightCostVaries :
    (nightCostVaries (Ctx := Unit) (Act := Acorn.Host.Action) (Obs := UInt8) (E := Nat)).HoldsOf
      dayCycle :=
  nightCostVaries_holds () .wait (lo := 0) (hi := 1) (hi' := 2) (by decide) (by decide)
    (by decide) quarterSight_injective

def dayRequired : LeanIntent.Required dayDeliverable where
  o2 := day_o2
  o2Run := .proved day_o2Run
  o3 := day_o3
  o4 := day_o4
  freedom := .widest
  o5 := day_o5
  comparison := .cases
    [⟨day_everyDayAlike⟩, ⟨day_seesQuarter⟩, ⟨day_refutes_dayOrNightOnly⟩, ⟨day_nightCostVaries⟩]
    "pilot blind formalization (docs/spec-first-pilot.md) predates committed blind records; \
      divergence consequences proved on dayCycle"
  additional := [⟨day_not_o5_eq⟩]

def hashRequired : LeanIntent.Required hashDeliverable where
  o2 := hashes_o2
  o2Run := .deferred
    "rbeauchamp/acorn#184 tracks proving O2Run and the implementation for AcornVerif.Intent.Hash.hashes"
  o3 := hashes_o3
  o4 := hashes_o4
  freedom := .widest
  o5 := hashes_o5_widest
  comparison := .cases
    [⟨oneChangeMoves_holds⟩, ⟨noFixedRule_holds⟩, ⟨rulesOutPlainCombinations_holds⟩, ⟨replay_holds⟩]
    "pilot blind formalization (docs/spec-first-pilot.md) predates committed blind records; \
      divergence consequences proved on hashes"
  additional := [⟨BeforeFixes.hashes_refuses_before⟩]

theorem worldInterface_separates_blind :
    worldInterface.Meets WorldInterface.Compare.deferredStop ∧
      ¬ WorldInterface.OwnerIntent.worldInterfaceIntent.Meets WorldInterface.Compare.deferredStop :=
  ⟨WorldInterface.Compare.deferredStop_meets_mine, WorldInterface.Compare.deferredStop_fails_theirs⟩

def worldInterfaceRequired : LeanIntent.Required worldInterfaceDeliverable where
  o2 := worldInterface_o2
  o2Run := .proved worldInterface_o2Run
  o3 := worldInterface_o3
  o4 := worldInterface_o4
  freedom := .widest
  o5 := worldInterface_o5_widest
  comparison := .records WorldInterface.OwnerIntent.worldInterfaceIntent
    (.separates WorldInterface.Compare.deferredStop worldInterface_separates_blind)
    (.implies WorldInterface.Compare.theirs_mine)
  additional := [⟨worldInterface_not_o5_eq⟩, ⟨worldInterface_pairs⟩]

theorem oneStream_separates_blind :
    oneStream.Meets OneStream.Compare.resumesOtherUnstopped ∧
      ¬ OneStream.OwnerRecord.oneStreamIntent.Meets OneStream.Compare.resumesOtherUnstopped :=
  ⟨OneStream.Compare.resumesOtherUnstopped_mine, OneStream.Compare.resumesOtherUnstopped_not_theirs⟩

theorem blind_separates_oneStream :
    OneStream.OwnerRecord.oneStreamIntent.Meets OneStream.counting ∧
      ¬ oneStream.Meets OneStream.counting :=
  ⟨OneStream.Compare.counting_theirs, OneStream.Compare.counting_not_mine⟩

def oneStreamRequired : LeanIntent.Required oneStreamDeliverable where
  o2 := oneStream_o2
  o2Run := .proved oneStream_o2Run
  o3 := oneStream_o3
  o4 := oneStream_o4
  freedom := .widest
  o5 := oneStream_o5_widest
  comparison := .records OneStream.OwnerRecord.oneStreamIntent
    (.separates OneStream.Compare.resumesOtherUnstopped oneStream_separates_blind)
    (.separates OneStream.counting blind_separates_oneStream)
  additional := [⟨oneStream_not_o5_eq⟩, ⟨oneStream_pairs⟩]

end AcornVerif.Intent.Required
