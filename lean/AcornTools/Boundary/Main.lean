import AcornTools.Boundary.Audit

unsafe def main (args : List String) : IO UInt32 :=
  AcornBoundaryAudit.command args
