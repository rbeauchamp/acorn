/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.MutationAudit
import AcornTools.ModuleInventory
import AcornTools.Ownership

/-! # Values the documents splice from Acorn's Lean owners

Each definition reads the declaration that owns a fact the documents state: the ownership
inventory and the audit arms and their pins. The documents splice
these values and hold no copy of them.
-/

namespace AcornSite

/-- The Lake executables of the ownership inventory, which the ownership gate compares with
Lake's evaluated configuration. -/
def executableNames : List String :=
  AcornOwnership.executables.toList.map (·.1)

/-- An executable name, accepted only with a proof that the ownership inventory lists it. -/
def executable (name : String) (_listed : name ∈ executableNames := by decide) : String :=
  name

/-- Executables whose root module is application code. -/
def applicationExecutables : List String :=
  (AcornOwnership.executables.toList.filter fun entry =>
    !AcornModuleInventory.toolingModules.contains entry.2).map (·.1)

/-- Executables whose root module is reviewed tooling. -/
def toolExecutables : List String :=
  (AcornOwnership.executables.toList.filter fun entry =>
    AcornModuleInventory.toolingModules.contains entry.2).map (·.1)

/-- Every fixed audit arm. -/
def auditArms : List NativeApp.AuditArm := [.declared, .annealed, .differential]

/-- `auditArms` omits no arm, so its length is the number of arms. -/
theorem mem_auditArms (arm : NativeApp.AuditArm) : arm ∈ auditArms := by
  cases arm <;> decide

/-- The pinned action digest of an audit arm, as the audit command prints and accepts it. -/
def digest (arm : NativeApp.AuditArm) : String :=
  NativeApp.hexWord arm.receipt.digest

/-- The pinned knowledge checksum paired with an audit arm's digest. -/
def checksum (arm : NativeApp.AuditArm) : String :=
  NativeApp.hexWord arm.receipt.checksum

/-- A small count as an English word; larger counts stay decimal. -/
def numberWord (count : Nat) : String :=
  (["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten",
    "eleven", "twelve"][count]?).getD (toString count)

/-- Items as an English list: `a`, `a and b`, `a, b and c`. -/
def proseList : List String → String
  | [] => ""
  | [only] => only
  | [first, last] => first ++ " and " ++ last
  | first :: rest => first ++ ", " ++ proseList rest

end AcornSite
