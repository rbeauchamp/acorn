import NativeApp.Core

def _root_.NativeApp.Main.main (arguments : List String) : IO UInt32 := do
  try NativeApp.runCore arguments
  catch error =>
    try IO.eprintln s!"acorn-core: {error}" catch _ => pure ()
    return 1
