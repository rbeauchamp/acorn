import NativeApp.MutationAudit
import AcornTools.ModuleInventory
import AcornTools.Ownership

namespace AcornSite

def executableNames : List String :=
  AcornOwnership.executables.toList.map (·.1)

def executable (name : String) (_listed : name ∈ executableNames := by decide) : String :=
  name

def applicationExecutables : List String :=
  (AcornOwnership.executables.toList.filter fun entry =>
    !AcornModuleInventory.toolingModules.contains entry.2).map (·.1)

def toolExecutables : List String :=
  (AcornOwnership.executables.toList.filter fun entry =>
    AcornModuleInventory.toolingModules.contains entry.2).map (·.1)

def auditArms : List NativeApp.AuditArm := NativeApp.AuditArm.all

def digest (arm : NativeApp.AuditArm) : String :=
  NativeApp.auditWord arm.receipt.digest

def checksum (arm : NativeApp.AuditArm) : String :=
  NativeApp.hexWord arm.receipt.checksum

def numberWord (count : Nat) : String :=
  (["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten",
    "eleven", "twelve"][count]?).getD (toString count)

def proseList : List String → String
  | [] => ""
  | [only] => only
  | [first, last] => first ++ " and " ++ last
  | first :: rest => first ++ ", " ++ proseList rest

end AcornSite
