/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.CoreTelemetry

/-!
# Native build identity

Lake's `nativeProvenance` dependency runs before this library is compiled and
contributes its trace to this module. The embedded bytes identify the complete
Lean/C source corpus, declared audit-pin owner, pinned manifests, compiler
versions and floating-operation flags. Compiler/build orchestration is trusted;
a digest supplies byte identity, never authenticity or correctness evidence.
-/
namespace NativeApp
open Acorn.Host.Viewer

private def provenance : String := include_str "../.lake/build/native-provenance.txt"

/-- Exact source framing embedded by the build, for explicitly requested scientific execution. -/
def sourceInventory : String := include_str "../.lake/build/native-source-inventory.txt"

/-- Actual compiler settings embedded alongside the source identity. -/
def buildRecord : String := include_str "../.lake/build/native-build-identity.txt"

private def hex (count : Nat) (value : String) : Option (HexText count) :=
  if valid : value.length = count ∧
      value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) = true then
    some ⟨value, valid⟩
  else none

/-- Admit complete build framing before any execution is attributed to it. -/
def decodeBuildIdentity (bytes : String) : Option TelemetryBuild := do
  let [source, build, audit, ""] := bytes.splitOn "\n" | none
  return ⟨← hex 64 source, ← hex 64 build, ← hex 16 audit⟩

/-- Shared telemetry uses the shared native build record. -/
def buildIdentity : Option TelemetryBuild := decodeBuildIdentity provenance

end NativeApp
