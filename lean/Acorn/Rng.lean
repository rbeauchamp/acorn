/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Word
import Acorn.Arithmetic

/-!
# Current seeded word streams

Reference sources: Sebastiano Vigna, SplitMix64 reference implementation (2015),
author's PRNG source collection, `next`:
https://prng.di.unimi.it/splitmix64.c.
David Blackman and Sebastiano Vigna, xoshiro256** reference implementation
(2018), same collection, `rotl` and `next`:
https://prng.di.unimi.it/xoshiro256starstar.c.
Landon Curt Noll, Kiem-Phong Vo, Donald Eastlake 3rd and Tony Hansen,
The FNV Non-Cryptographic Hash Algorithm, RFC 9923 (2026), sections 2, 5
and 8.2.2: https://www.rfc-editor.org/rfc/rfc9923.html.

Acorn's seed sequence has two additions of the SplitMix increment per output:
one advances stored state; the other belongs to `mix64`. This is part of the
current stream identity, not the reference source's single-increment sequence.
Raw all-zero xoshiro state remains admitted. These total deterministic functions
establish no IID or uniform-seed hypothesis; distribution results state their
separate source-word assumptions in `AcornVerif.CurrentRng`.
-/

namespace Acorn.Rng

/-- The fixed increment shared by the state transition and mixer. -/
def increment : UInt64 := 0x9e3779b97f4a7c15

/-- Rotate a word with a modulo-width count, including a zero rotation. -/
def rotateLeft (word count : UInt64) : UInt64 :=
  (word <<< (count &&& 63)) ||| (word >>> ((64 - count) &&& 63))

/-- SplitMix's two multiply/xor rounds and final xor, without a state advance. -/
def mixFinal (word : UInt64) : UInt64 :=
  let first := (word ^^^ (word >>> 30)) * 0xbf58476d1ce4e5b9
  let second := (first ^^^ (first >>> 27)) * 0x94d049bb133111eb
  second ^^^ (second >>> 31)

/-- The current Acorn mixer includes its own wrapping increment. -/
def mix64 (word : UInt64) : UInt64 := mixFinal (word + increment)

/-- The complete SplitMix state; every raw word is admitted. -/
structure SplitMix64 where
  /-- Exact stored state word. -/
  state : UInt64
  deriving DecidableEq

/-- Advance stored state once, then call the current incrementing mixer. -/
def SplitMix64.next (stream : SplitMix64) : UInt64 × SplitMix64 :=
  let advanced := stream.state + increment
  (mix64 advanced, ⟨advanced⟩)

/-- The two seed offsets are visible in the actual step, for every starting word. -/
theorem splitmix_two_offsets (stream : SplitMix64) :
    stream.next = (mixFinal ((stream.state + increment) + increment),
      SplitMix64.mk (stream.state + increment)) := rfl

/-- Complete raw xoshiro state, including the all-zero state. -/
structure Xoshiro256 where
  /-- Stored word zero. -/
  s0 : UInt64
  /-- Stored word one, read by the output scrambler. -/
  s1 : UInt64
  /-- Stored word two. -/
  s2 : UInt64
  /-- Stored word three. -/
  s3 : UInt64
  deriving DecidableEq

/-- Four successive current SplitMix outputs, in stored-word order. -/
def Xoshiro256.seed (seed : UInt64) : Xoshiro256 :=
  let (a, stream) := (SplitMix64.mk seed).next
  let (b, stream) := stream.next
  let (c, stream) := stream.next
  let (d, _) := stream.next
  ⟨a, b, c, d⟩

/-- Deterministic stream-key derivation; no probabilistic independence is asserted. -/
def streamKey (seed id : UInt64) : UInt64 :=
  mix64 (seed ^^^ (mix64 id * increment))

/-- One current xoshiro output and transition, preserving sequential xor order. -/
def Xoshiro256.next (stream : Xoshiro256) : UInt64 × Xoshiro256 :=
  let output := rotateLeft (stream.s1 * 5) 7 * 9
  let shifted := stream.s1 <<< 17
  let s2 := stream.s2 ^^^ stream.s0
  let s3 := stream.s3 ^^^ stream.s1
  let s1 := stream.s1 ^^^ s2
  let s0 := stream.s0 ^^^ s3
  let s2 := s2 ^^^ shifted
  let s3 := rotateLeft s3 45
  (output, ⟨s0, s1, s2, s3⟩)

/-- Every next-range result carries the bound of the actual receiving count. -/
def Xoshiro256.nextBelow (stream : Xoshiro256) (count : Word.Count) :
    { word : UInt64 // word.toNat < count.word.toNat } × Xoshiro256 :=
  let (word, next) := stream.next
  (Word.below word count, next)

/-- The range operation consumes exactly the same single transition as `next`. -/
theorem nextBelow_transition (stream : Xoshiro256) (count : Word.Count) :
    (stream.nextBelow count).2 = stream.next.2 := rfl

/-- Range selection uses the full product of the actual output word and count. -/
theorem nextBelow_quotient (stream : Xoshiro256) (count : Word.Count) :
    (stream.nextBelow count).1.val.toNat = stream.next.1.toNat * count.word.toNat / 2 ^ 64 :=
  Word.multiplyHigh_exact _ _

/-- A 53-bit numerator whose declared denominator is exactly 2^53. -/
structure Fraction53 where
  /-- Stored numerator word. -/
  numerator : UInt64
  /-- The fraction is in [0,1) by integer arithmetic, independently of RNG law. -/
  bounded : numerator.toNat < 2 ^ 53

/-- Right shifting discards the eleven low bits of every source word. -/
def Fraction53.ofWord (word : UInt64) : Fraction53 where
  numerator := word >>> 11
  bounded := by
    have hw := word.toNat_lt
    change (word.toNat >>> 11) < 2 ^ 53
    rw [Nat.shiftRight_eq_div_pow]
    omega

/-- The current numerical conversion recipe, using the same modeled native
integer conversion and binary64 multiply as the arithmetic layer. -/
def Fraction53.toBinary64 (fraction : Fraction53) : Binary64 :=
  (Binary64.ofUInt64 fraction.numerator).mul ⟨0x3ca0000000000000⟩

/-- One RNG draw with its exact retained 53-bit numerator. -/
def Xoshiro256.nextFraction (stream : Xoshiro256) : Fraction53 × Xoshiro256 :=
  let (word, next) := stream.next
  (Fraction53.ofWord word, next)

/-- Current floating draw, sharing the one-word draw and fraction constructor. -/
def Xoshiro256.nextF64 (stream : Xoshiro256) : Binary64 × Xoshiro256 :=
  let (fraction, next) := stream.nextFraction
  (fraction.toBinary64, next)

/-- Numerical conversion consumes no additional stream transitions. -/
theorem nextF64_transition (stream : Xoshiro256) : stream.nextF64.2 = stream.next.2 := rfl

/-- A finite prefix of outputs and its final state. This is an executable
observation of the transition, not a stochastic or learning-history model. -/
def runPrefix : Nat → Xoshiro256 → List UInt64 × Xoshiro256
  | 0, stream => ([], stream)
  | count + 1, stream =>
    let (word, next) := stream.next
    let (tail, finalState) := runPrefix count next
    (word :: tail, finalState)

/-- Advance without retaining output words; storage does not grow with the prefix. -/
def advance : Nat → Xoshiro256 → Xoshiro256
  | 0, stream => stream
  | count + 1, stream => advance count stream.next.2

/-- Output length is exactly the requested count on every admitted raw state. -/
theorem prefix_length (count : Nat) (stream : Xoshiro256) :
    (runPrefix count stream).1.length = count := by
  induction count generalizing stream with
  | zero => rfl
  | succ count ih => simp [runPrefix, ih]

/-- Output-free execution and runPrefix observation have the same final state. -/
theorem prefix_state (count : Nat) (stream : Xoshiro256) :
    (runPrefix count stream).2 = advance count stream := by
  induction count generalizing stream with
  | zero => rfl
  | succ count ih => simp [runPrefix, advance, ih]

/-- Every finite execution splits at any boundary without changing draw order. -/
theorem prefix_append (first second : Nat) (stream : Xoshiro256) :
    runPrefix (first + second) stream =
      ((runPrefix first stream).1 ++ (runPrefix second (runPrefix first stream).2).1,
        (runPrefix second (runPrefix first stream).2).2) := by
  induction first generalizing stream with
  | zero => simp [runPrefix]
  | succ first ih =>
    simp [Nat.succ_add, runPrefix, ih]

/-- The raw zero state is an admitted absorbing state, not a seed repair. -/
def Xoshiro256.zero : Xoshiro256 := ⟨0, 0, 0, 0⟩

/-- Every finite prefix from the zero state consists of zero outputs and
retains that state. No nonzero-state assumption is hidden in admission. -/
theorem prefix_zero_state (count : Nat) :
    runPrefix count Xoshiro256.zero = (List.replicate count 0, Xoshiro256.zero) := by
  have hstep : Xoshiro256.zero.next = (0, Xoshiro256.zero) := by rfl
  induction count with
  | zero => rfl
  | succ count ih => simp [runPrefix, hstep, ih, List.replicate_succ]

/-- A coordinate hash accepts the exact two's-complement coordinate words. -/
def hash2 (x y seed : UInt64) : UInt64 :=
  let first := mix64 ((seed ^^^ increment) ^^^ x)
  mix64 (mix64 (first ^^^ rotateLeft y 32))

/-- Stable mixing of three raw words. -/
def hash3 (a b c : UInt64) : UInt64 :=
  mix64 (mix64 ((a ^^^ increment) ^^^ b) ^^^ rotateLeft c 17)

/-- Ordered hashing of any finite word list, preserving the per-word offset. -/
def hashMany (words : List UInt64) : UInt64 :=
  words.foldl (fun state word => mix64 (state ^^^ (word + increment))) increment

/-- Exact FNV offset basis, read by every byte fold. -/
def fnvOffset : UInt64 := 0xcbf29ce484222325

/-- The single executable FNV byte step. -/
def fnvStep (state : UInt64) (byte : UInt8) : UInt64 :=
  (state ^^^ byte.toUInt64) * 0x00000100000001b3

/-- A fixed-byte FNV step is injective on every state word. The single closed
inverse identity supplies an algebraic witness; no state is enumerated. -/
theorem fnvStep_injective (byte : UInt8) (left right : UInt64)
    (h : fnvStep left byte = fnvStep right byte) : left = right := by
  have hx := Word.multiplier_injective 0x00000100000001b3 0xce965057aff6957b
    (by decide) (left ^^^ byte.toUInt64) (right ^^^ byte.toUInt64) h
  exact Word.xor_word_injective left right byte.toUInt64 hx

/-- A byte stream uses the same step as incremental checkpoint hashing. -/
def fnv (bytes : List UInt8) : UInt64 := bytes.foldl fnvStep fnvOffset

/-- Byte-sequence composition is exactly incremental folding from the prefix. -/
theorem fnv_append (first second : List UInt8) :
    fnv (first ++ second) = second.foldl fnvStep (fnv first) := by
  simp [fnv, List.foldl_append]

/-- The actual state rotation is injective on all words. -/
theorem state_rotation_injective (left right : UInt64)
    (h : rotateLeft left 45 = rotateLeft right 45) : left = right := by
  apply UInt64.toBitVec_inj.mp
  apply Word.rotate_injective (rotation := 45) (by decide)
  have hb := congrArg UInt64.toBitVec h
  change (left.toBitVec <<< 45 ||| left.toBitVec >>> 19) =
    (right.toBitVec <<< 45 ||| right.toBitVec >>> 19) at hb
  simpa only [BitVec.rotateLeft_def] using hb

/-- The sequential xoshiro state transition loses no admitted raw state. -/
theorem next_state_injective (left right : Xoshiro256)
    (h : left.next.2 = right.next.2) : left = right := by
  have h3 := state_rotation_injective _ _ (congrArg Xoshiro256.s3 h)
  have hb := congrArg (fun state => (state.s1 ^^^ state.s2).toBitVec) h
  change (left.s1.toBitVec ^^^ (left.s2.toBitVec ^^^ left.s0.toBitVec)) ^^^
      ((left.s2.toBitVec ^^^ left.s0.toBitVec) ^^^ (left.s1.toBitVec <<< 17)) =
    (right.s1.toBitVec ^^^ (right.s2.toBitVec ^^^ right.s0.toBitVec)) ^^^
      ((right.s2.toBitVec ^^^ right.s0.toBitVec) ^^^ (right.s1.toBitVec <<< 17)) at hb
  have cancel (a b c : BitVec 64) : (a ^^^ b) ^^^ (b ^^^ c) = a ^^^ c := by
    rw [BitVec.xor_assoc, ← BitVec.xor_assoc b b, BitVec.xor_self, BitVec.zero_xor]
  rw [cancel, cancel] at hb
  have h1 : left.s1 = right.s1 := UInt64.toBitVec_inj.mp
    (Word.xor_shiftLeft_injective (by decide : 0 < 17) _ _ hb)
  have h0 := Word.xor_word_injective _ _ (right.s3 ^^^ right.s1)
    (by simpa only [Xoshiro256.next, h3] using congrArg Xoshiro256.s0 h)
  have h2 := Word.xor_word_injective left.s2 right.s2 right.s0
    (by
      have he := congrArg (fun state => state.s1.toBitVec) h
      change left.s1.toBitVec ^^^ (left.s2.toBitVec ^^^ left.s0.toBitVec) =
        right.s1.toBitVec ^^^ (right.s2.toBitVec ^^^ right.s0.toBitVec) at he
      rw [h1, h0] at he
      exact UInt64.toBitVec_inj.mp ((BitVec.xor_right_inj right.s1.toBitVec).mp he))
  have hd : left.s3 = right.s3 := Word.xor_word_injective _ _ right.s1 (by simpa [h1] using h3)
  cases left; cases right
  simp_all
/-- A positive in-word right xor shift is injective over machine words. -/
theorem word_right_xor_injective (shift : UInt64) (positive : 0 < shift.toNat)
    (small : shift.toNat < 64) (left right : UInt64)
    (h : left ^^^ (left >>> shift) = right ^^^ (right >>> shift)) : left = right := by
  apply UInt64.toBitVec_inj.mp
  apply Word.xor_shiftRight_injective positive
  have hb := congrArg UInt64.toBitVec h
  simpa [UInt64.toBitVec_xor, UInt64.toBitVec_shiftRight,
    BitVec.ushiftRight_eq', BitVec.toNat_umod, UInt64.toNat_toBitVec,
    Nat.mod_eq_of_lt small] using hb

/-- The actual SplitMix finalizer is injective by shift cancellation and two
closed multiplier inverse witnesses. No 64-bit domain is enumerated. -/
theorem mixFinal_injective (left right : UInt64) (h : mixFinal left = mixFinal right) :
    left = right := by
  have last := word_right_xor_injective 31 (by decide) (by decide) _ _ h
  have second := Word.multiplier_injective 0x94d049bb133111eb 0x319642b2d24d8ec3
    (by decide) _ _ last
  have middle := word_right_xor_injective 27 (by decide) (by decide) _ _ second
  have first := Word.multiplier_injective 0xbf58476d1ce4e5b9 0x96de1b173f119089
    (by decide) _ _ middle
  exact word_right_xor_injective 30 (by decide) (by decide) _ _ first

/-- The incrementing mixer remains injective; addition is cancellative modulo 2^64. -/
theorem mix64_injective (left right : UInt64) (h : mix64 left = mix64 right) : left = right := by
  have hx := mixFinal_injective _ _ h
  have hc := congrArg (fun word => word - increment) hx
  simpa using hc

/-- Any fixed finite state advance is injective, including raw zero admission. -/
theorem advance_injective (count : Nat) (left right : Xoshiro256)
    (h : advance count left = advance count right) : left = right := by
  induction count generalizing left right with
  | zero => exact h
  | succ count ih => exact next_state_injective left right (ih _ _ h)

/-- A nonzero raw state stays nonzero through every finite number of draws. -/
theorem advance_nonzero (count : Nat) (stream : Xoshiro256) (h : stream ≠ .zero) :
    advance count stream ≠ .zero := by
  intro hz
  have hzero : advance count Xoshiro256.zero = Xoshiro256.zero := by
    rw [← prefix_state]
    exact congrArg Prod.snd (prefix_zero_state count)
  exact h (advance_injective count stream Xoshiro256.zero (hz.trans hzero.symm))

/-- Successive seed words differ because the incrementing mixer is injective
and the fixed increment is nonzero. Thus seeding never produces raw zero state. -/
theorem seed_nonzero (seed : UInt64) : Xoshiro256.seed seed ≠ Xoshiro256.zero := by
  intro hz
  have ha := congrArg Xoshiro256.s0 hz
  have hb := congrArg Xoshiro256.s1 hz
  have same : mix64 (seed + increment) = mix64 ((seed + increment) + increment) := ha.trans hb.symm
  have hi := mix64_injective _ _ same
  have hc := congrArg (fun word => word - (seed + increment)) hi
  have impossible : (0 : UInt64) = increment := by simpa [UInt64.add_comm] using hc
  contradiction
end Acorn.Rng
