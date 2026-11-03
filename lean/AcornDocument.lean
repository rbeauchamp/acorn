/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-! # External names of maintained prose

The names that maintained prose may cite from outside the project, which the corpus audit in
`AcornTools.Corpus.Documents` admits, and the theorem that states what an admitted name is. This
module imports nothing beyond Lean's prelude, so the proof claim covers it and its theorem.
-/

namespace AcornDocument

/-- External names used in maintained prose must be registered individually here when the
prose is added; dependency imports do not contribute maintained declaration names. -/
def externalSymbols : List String := [
  "libc",
  "Vec",
  "Some",
  "None",
  "u8",
  "u16",
  "u32",
  "usize",
  "f32",
  "f64",
  "i64",
  "i128",
  "u32",
  "u64",
  "NonZeroU32",
  "Result",
  "assert",
  "debug_assert",
  "include_str",
  "eprintln",
  "panic",
  "unwrap",
  "expect",
  "todo",
  "unimplemented",
  "unreachable",
  "exit",
  "is_finite",
  "is_power_of_two",
  "unwrap_or_else",
  "read_dir",
  "zip",
  "exp",
  "ln",
  "powf",
  "sqrt",
  "floor",
  "fma",
  "mul_add",
  "spawn",
  "exec",
  "rename",
  "assume",
  "Lean",
  "Std.TreeMap",
  "LeanIntent.Declared",
  "LeanIntent.Codes",
  "Float",
  "Float32",
  "Int",
  "Nat",
  "Bool",
  "Option",
  "Except",
  "Decidable",
  "Classical",
  "Quot",
  "propext",
  "IO",
  "decide",
  "native_decide",
  "sorry",
  "ring",
  "SwiftTD",
  "Horde",
  "learn_online_lsvi",
  "JSON",
  "localStorage",
  "requestAnimationFrame",
  "setTimeout",
  "RUSTFLAGS",
  "RUSTDOCFLAGS",
  "CARGO_TARGET_DIR",
  "cargo",
  "pdftotext",
  "ACORN_REGISTRATION_TRUST",
  "warningAsError",
  "autoImplicit",
  "lintDriverArgs",
  "missingDocs"]

/-- Whether a name is one of the external symbols. Admission is equality with a listed name,
so a listed name admits no other name of its namespace: every qualified external name a
document uses is listed in full. -/
def external (name : String) : Bool :=
  (externalSymbols.map (·.replace "::" ".")).contains name

/-- An admitted external name is one of the listed symbols. -/
theorem external_listed (name : String) (admitted : external name = true) :
    name ∈ externalSymbols.map (·.replace "::" ".") := by
  simpa [external] using admitted

end AcornDocument
