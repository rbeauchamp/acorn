/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Signed and unsigned word interpretations

Integer wrapping is shared by hashed curriculum coordinates and numerical
execution. These definitions do not depend on floating-point operations.
-/

namespace AcornSpec

/-- The two's-complement `u64` image of an integer — Rust's `x as u64` on an
`i64`. Total for every integer; on the `i64` domain it is exactly the
reinterpretation. -/
@[inline]
def i64bits (n : Int) : UInt64 :=
  if 0 ≤ n then n.toNat.toUInt64 else 0 - (-n).toNat.toUInt64

/-- Signed reading of a `u64` word — the inverse of `i64bits` on the `i64`
domain. -/
@[inline]
def u64AsI64 (u : UInt64) : Int :=
  if u < 0x8000000000000000 then (u.toNat : Int) else (u.toNat : Int) - 18446744073709551616

end AcornSpec
