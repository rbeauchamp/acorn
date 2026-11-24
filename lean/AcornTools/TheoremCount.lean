import AcornTools.Theorems

unsafe def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: theorem-count"
    return 1
  let counts ← AcornTheoremCount.inventory
  counts.report
  return 0
