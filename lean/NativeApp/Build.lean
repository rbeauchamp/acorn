import Acorn.Host.Viewer.CoreTelemetry

namespace NativeApp
open Acorn.Host.Viewer

private def provenance : String := include_str "../.lake/build/native-provenance.txt"

def sourceInventory : String := include_str "../.lake/build/native-source-inventory.txt"

def buildRecord : String := include_str "../.lake/build/native-build-identity.txt"

private def hex (count : Nat) (value : String) : Option (HexText count) :=
  if valid : value.length = count ∧
      value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) = true then
    some ⟨value, valid⟩
  else none

def decodeBuildIdentity (bytes : String) : Option TelemetryBuild := do
  let [source, build, audit, ""] := bytes.splitOn "\n" | none
  return ⟨← hex 64 source, ← hex 64 build, ← hex 16 audit⟩

def buildIdentity : Option TelemetryBuild := decodeBuildIdentity provenance

end NativeApp
