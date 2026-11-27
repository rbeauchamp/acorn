import Acorn.Host.Cli
import Std.Sync.Mutex

namespace Acorn.Host.Viewer

def residentBytes (text : String) : Option UInt64 := do
  let kib ← Digits.read (trimControlLine text)
  if kib * 1024 < 2 ^ 64 then some (kib * 1024).toUInt64 else none

structure NativeResources where
  private mk ::
  private latest : Std.Mutex (Option UInt64)

def NativeResources.new : BaseIO NativeResources := do return ⟨← Std.Mutex.new none⟩

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
