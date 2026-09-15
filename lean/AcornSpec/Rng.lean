/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Executable specification: deterministic pseudo-randomness and hashing

Mirrors `src/rng.rs` function by function. Every definition is a total pure
function over fixed-width words; `UInt64` arithmetic in Lean is wrapping, the
same as the Rust source's `wrapping_*` operations. This module is part of
`AcornSpec`, the definitional owner of "the specified Acorn system" for the
agent-baseline performance claim. The Rust binary is an untrusted accelerator
bound to these definitions by the action-transcript fold gate.
-/

namespace AcornSpec

/-- Rotate a 64-bit word left by `n` bits (`u64::rotate_left`). Callers pass
constant `n` in `1..63`, but the definition is total for every `n`. -/
@[inline]
def rotl64 (x : UInt64) (n : UInt64) : UInt64 :=
  (x <<< (n &&& 63)) ||| (x >>> ((64 - n) &&& 63))

/-- `rng::mix64` — the SplitMix64 finalizer. -/
@[inline]
def mix64 (x : UInt64) : UInt64 :=
  let x := x + 0x9E3779B97F4A7C15
  let x := (x ^^^ (x >>> 30)) * 0xBF58476D1CE4E5B9
  let x := (x ^^^ (x >>> 27)) * 0x94D049BB133111EB
  x ^^^ (x >>> 31)

/-- `rng::SplitMix64` — the seeded source of stream keys. The state is the
single `u64` the Rust struct holds. -/
structure SplitMix64 where
  /-- Generator state. -/
  state : UInt64

/-- `SplitMix64::next_u64`: advance the state and mix. Returns the drawn word
and the advanced generator. -/
@[inline]
def SplitMix64.next (g : SplitMix64) : UInt64 × SplitMix64 :=
  let s := g.state + 0x9E3779B97F4A7C15
  (mix64 s, ⟨s⟩)

/-- `rng::Xoshiro256` — the workhorse generator (xoshiro256**). -/
structure Xoshiro256 where
  /-- State word 0. -/
  s0 : UInt64
  /-- State word 1. -/
  s1 : UInt64
  /-- State word 2. -/
  s2 : UInt64
  /-- State word 3. -/
  s3 : UInt64

/-- `Xoshiro256::new`: seed all four state words from `SplitMix64`, in order. -/
def Xoshiro256.new (seed : UInt64) : Xoshiro256 :=
  let g : SplitMix64 := ⟨seed⟩
  let (a, g) := g.next
  let (b, g) := g.next
  let (c, g) := g.next
  let (d, _) := g.next
  ⟨a, b, c, d⟩

/-- `Xoshiro256::stream_key`: derive an independent stream key from a parent
seed and a stream id. -/
@[inline]
def Xoshiro256.streamKey (seed id : UInt64) : UInt64 :=
  mix64 (seed ^^^ (mix64 id * 0x9E3779B97F4A7C15))

/-- `Xoshiro256::next_u64`: one xoshiro256** step. Returns the output word and
the advanced generator. -/
@[inline]
def Xoshiro256.next (g : Xoshiro256) : UInt64 × Xoshiro256 :=
  let result := rotl64 (g.s1 * 5) 7 * 9
  let t := g.s1 <<< 17
  let s2 := g.s2 ^^^ g.s0
  let s3 := g.s3 ^^^ g.s1
  let s1 := g.s1 ^^^ s2
  let s0 := g.s0 ^^^ s3
  let s2 := s2 ^^^ t
  let s3 := rotl64 s3 45
  (result, ⟨s0, s1, s2, s3⟩)

/-- High 64 bits of the full 128-bit product of two 64-bit words, by 32-bit
split — the multiply-high at the heart of Lemire's method, without leaving
fixed-width arithmetic. -/
@[inline]
def mulHi64 (a b : UInt64) : UInt64 :=
  let al := a &&& 0xFFFFFFFF
  let ah := a >>> 32
  let bl := b &&& 0xFFFFFFFF
  let bh := b >>> 32
  let lolo := al * bl
  let hilo := ah * bl
  let lohi := al * bh
  let hihi := ah * bh
  let cross := (lolo >>> 32) + (hilo &&& 0xFFFFFFFF) + lohi
  hihi + (hilo >>> 32) + (cross >>> 32)

/-- `Xoshiro256::next_below`: near-uniform pseudorandom integer in `[0, n)`
via multiply-shift. The Rust signature takes `NonZeroU64`; every call site in
the mirrored system passes a positive constant, and `AcornVerif.Rng` carries
the `< n` range proof for the identical formula. -/
@[inline]
def Xoshiro256.nextBelow (g : Xoshiro256) (n : UInt64) : UInt64 × Xoshiro256 :=
  let (x, g) := g.next
  (mulHi64 x n, g)

/-- `rng::hash2` — position-stable hash of two signed coordinates plus a
seed. Coordinates arrive as their two's-complement `u64` images, exactly the
`x as u64` reinterpretation the Rust source performs. -/
@[inline]
def hash2 (x y : UInt64) (seed : UInt64) : UInt64 :=
  let h := seed ^^^ 0x9E3779B97F4A7C15
  let h := mix64 (h ^^^ x)
  let h := mix64 (h ^^^ rotl64 y 32)
  mix64 h

/-- `rng::hash3` — position-stable hash of three words. -/
@[inline]
def hash3 (a b c : UInt64) : UInt64 :=
  let h := a ^^^ 0x9E3779B97F4A7C15
  let h := mix64 (h ^^^ b)
  mix64 (h ^^^ rotl64 c 17)

/-- `rng::fnv1a` over a byte list — used only to reproduce the handful of
compile-time stream-tag constants (`fnv1a(b"...")`); never on a hot path. -/
def fnv1a (bytes : List UInt8) : UInt64 :=
  bytes.foldl (fun h b => (h ^^^ b.toUInt64) * 0x00000100000001B3) 0xCBF29CE484222325

/-- `fnv1a` of a string's UTF-8 bytes — the form the Rust byte-string tags
take. Every tag in the system is ASCII, where UTF-8 bytes are the code
points. -/
def fnv1aStr (s : String) : UInt64 :=
  fnv1a (s.toUTF8.toList)

end AcornSpec
