/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Cli
import Std.Sync.Mutex

/-! # Sampled native resident memory

The host `ps` reports KiB at each 256th lifetime decision. Sampling and parsing
failure are unavailable values, never zeros. Terminal frames reuse the latest
sample. This observer has no path to action selection or agent state.
-/
namespace Acorn.Host.Viewer

/-- Checked KiB conversion cannot wrap at the wire's word boundary. -/
def residentBytes (text : String) : Option UInt64 := do
  let kib ← Cli.natural (trimControlLine text)
  if kib * 1024 < 2 ^ 64 then some (kib * 1024).toUInt64 else none

/-- Process-local optional sample; an absent measurement stays absent. -/
structure NativeResources where
  private mk ::
  private latest : Std.Mutex (Option UInt64)

/-- No sampling or subprocess at construction. -/
def NativeResources.new : BaseIO NativeResources := do return ⟨← Std.Mutex.new none⟩

/-- Sample at the declared cadence before a regular observer frame. -/
def NativeResources.observe (resources : NativeResources) (clock : UInt64) (terminal : Bool) : IO (Option UInt64) := do
  if !terminal && clock % 256 == 0 then
    let value ← try
      let output ← IO.Process.output {
        cmd := "/bin/ps", args := #["-o", "rss=", "-p", toString (← IO.Process.getPID)] }
      pure (if output.exitCode == 0 then residentBytes output.stdout else none)
    catch _ => pure none
    resources.latest.atomically (set value)
  return ← resources.latest.atomically get

end Acorn.Host.Viewer
