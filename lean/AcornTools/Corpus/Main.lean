import AcornTools.Corpus.Audit

unsafe def main (args : List String) : IO UInt32 := do
  try
    unless args.isEmpty || args == ["documents"] do
      throw (IO.userError "usage: corpus-audit [documents]")
    AcornCorpus.check (args == ["documents"])
    return 0
  catch error =>
    IO.eprintln s!"corpus-audit: {error}"
    return 1
