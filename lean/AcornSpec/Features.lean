/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Rng
import AcornSpec.FeatureSpace

/-!
# Integer feature encoding and its universal index contracts

The fixed-bank featurizer hashes opaque sensor words and patch bytes. This
module owns the pure encoding definitions and theorems about their masked
indices, first-occurrence order, and uniqueness. It needs neither a world nor
a learner. The observer-specific adapter lives in `HistoricalEncoding`.

These theorems quantify over this Lean encoder at the declared 2¹⁴ weight
space. The current dimension-parametric encoder has separate execution contracts;
these index and uniqueness results concern only the definitions below.
-/

namespace AcornSpec

/-- `AgentConfig::new` imprint-unit count. -/
def imprintUnits : Nat := 512
/-- Cells sampled by one imprinting unit. -/
def imprintCellsPerUnit : Nat := 32
/-- `AgentConfig::new` tiling count. -/
def nTilings : UInt64 := 8

/-- `features::Featurizer` — initial bank is a pure function of the seed;
replacement mutates one unit and continues the constructor SplitMix64
stream. Imprint cells are packed `(row <<< 4) ||| col` (both < 11); signs
are `1` for `+1`, `0` for `−1`. -/
structure Featurizer where
  /-- Campaign seed (feature identity salt). -/
  seed : UInt64
  /-- Packed imprint cells, unit-major. -/
  cells : ByteArray
  /-- Imprint signs, unit-major. -/
  signs : ByteArray
  /-- Leftover constructor stream; replacement draws the next 32 cells. -/
  sm : SplitMix64

namespace Featurizer

/-- `features::imprint_cell` — one 64-bit word to a patch cell and sign, at
span 11 (`PATCH_SIDE`). -/
@[inline]
def imprintCell (w : UInt64) : UInt8 × UInt8 × Bool :=
  let col := (w % 11).toUInt8
  let row := ((w >>> 8) % 11).toUInt8
  let positive := (w >>> 16) &&& 1 == 1
  (row, col, positive)

/-- `Featurizer::new` — draw the 512 × 32 imprint cells from the seed's
dedicated SplitMix64 stream. -/
def new (seed : UInt64) : Featurizer :=
  Id.run do
    let mut cells := ByteArray.emptyWithCapacity (imprintUnits * imprintCellsPerUnit)
    let mut signs := ByteArray.emptyWithCapacity (imprintUnits * imprintCellsPerUnit)
    let mut sm : SplitMix64 := ⟨Xoshiro256.streamKey seed 0x1D1D000000000001⟩
    for _ in [0:imprintUnits] do
      for _ in [0:imprintCellsPerUnit] do
        let (w, sm') := sm.next
        sm := sm'
        let (row, col, positive) := imprintCell w
        cells := cells.push ((row <<< 4) ||| col)
        signs := signs.push (if positive then 1 else 0)
    pure { seed, cells, signs, sm }

/-- `mask_to_space` at `N = 2¹⁴`: the one `FeatIdx` constructor. -/
@[inline]
def mask (h : UInt64) : UInt32 :=
  h.toUInt32 &&& 0x3FFF

/-- `Featurizer::feat` — index for a `(tiling, tag, value)` triple. -/
@[inline]
def feat (f : Featurizer) (t tag value : UInt64) : UInt32 :=
  mask (hash3 (f.seed ^^^ t) tag value)

/-- `Featurizer::imprint_feat`. -/
@[inline]
def imprintFeat (f : Featurizer) (unit : UInt64) : UInt32 :=
  mask (hash3 (f.seed ^^^ 0x1D) 0x1D unit)

/-- `Featurizer::replace_unit` — draw 32 new cells from the leftover
constructor stream and write them over unit `u`. The bank length is
unchanged. -/
def replaceUnit (f : Featurizer) (u : Nat) : Featurizer :=
  Id.run do
    let mut cells := f.cells
    let mut signs := f.signs
    let mut sm := f.sm
    for j in [0:imprintCellsPerUnit] do
      let (w, sm') := sm.next
      sm := sm'
      let (row, col, positive) := imprintCell w
      let idx := u * imprintCellsPerUnit + j
      cells := cells.set! idx ((row <<< 4) ||| col)
      signs := signs.set! idx (if positive then 1 else 0)
    pure { f with cells, signs, sm }

/-- Word-tiling inner loop of `encode`: push `feat t tag value` for every
word of one tiling. -/
def encodeWordsGo (f : Featurizer) (t : UInt64) (words : Array (UInt64 × UInt64))
    (out : Array UInt32) (k : Nat) : Nat → Array UInt32
  | 0 => out
  | fuel + 1 =>
    let wv := words[k]!
    encodeWordsGo f t words (out.push (f.feat t wv.1 wv.2)) (k + 1) fuel

/-- Tiling loop of `encode`. -/
def encodeTilingsGo (f : Featurizer) (words : Array (UInt64 × UInt64))
    (out : Array UInt32) (t : Nat) : Nat → Array UInt32
  | 0 => out
  | fuel + 1 =>
    encodeTilingsGo f words (encodeWordsGo f t.toUInt64 words out 0 words.size)
      (t + 1) fuel

/-- One imprint unit's projection: the signed sum over its 32 cells, as an
integer accumulator. -/
def imprintAccGo (f : Featurizer) (patch : ByteArray) (u : Nat) (acc : Int)
    (j : Nat) : Nat → Int
  | 0 => acc
  | fuel + 1 =>
    let packed := f.cells.get! (u * imprintCellsPerUnit + j)
    let row := (packed >>> 4).toNat
    let col := (packed &&& 0xF).toNat
    let code := patch.get! (row * 11 + col)
    let bit : Int := ((hash3 (f.seed ^^^ u.toUInt64) j.toUInt64 code.toUInt64) &&& 1).toNat
    let sign : Int := if f.signs.get! (u * imprintCellsPerUnit + j) == 1 then 1 else -1
    imprintAccGo f patch u (acc + sign * bit) (j + 1) fuel

/-- One imprint unit of `encode`: push the unit's index when its projection
is positive. -/
def imprintPush (f : Featurizer) (patch : ByteArray) (out : Array UInt32) (u : Nat) :
    Array UInt32 :=
  if 0 < imprintAccGo f patch u 0 0 imprintCellsPerUnit then out.push (f.imprintFeat u.toUInt64)
  else out

/-- Imprint-unit loop of `encode`. -/
def imprintUnitsGo (f : Featurizer) (patch : ByteArray) (out : Array UInt32)
    (u : Nat) : Nat → Array UInt32
  | 0 => out
  | fuel + 1 => imprintUnitsGo f patch (imprintPush f patch out u) (u + 1) fuel

/-! ## The unique pass

`firstOccurrences` specifies filtering by first occurrence using a list of seen
indices. `uniqueIndices` implements the same filter with a packed seen set of
`weightSpace / 64` words. `uniqueIndices_eq` proves their equality for every
array of masked indices. `uniqueIndices_nodup` and `uniqueIndices_sublist`
establish uniqueness and preservation of input order for these definitions.
Correspondence with a separately implemented encoder requires its own proof. -/

/-- First-occurrence filter: keep `x` when it is not in `seen`, and treat it
as seen from then on. The statement of uniquing. -/
def firstOccurrences (seen : List UInt32) : List UInt32 → List UInt32
  | [] => []
  | x :: xs =>
    if x ∈ seen then firstOccurrences seen xs
    else x :: firstOccurrences (x :: seen) xs

/-- The filter returns a subsequence of its input, whatever is already seen. -/
theorem firstOccurrences_sublist (seen xs : List UInt32) :
    (firstOccurrences seen xs).Sublist xs := by
  induction xs generalizing seen with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
    unfold firstOccurrences
    split
    · exact List.Sublist.cons x (ih seen)
    · exact List.Sublist.cons_cons x (ih (x :: seen))

/-- Nothing the filter keeps was already seen. -/
theorem firstOccurrences_not_mem_seen (seen xs : List UInt32) :
    ∀ y ∈ firstOccurrences seen xs, y ∉ seen := by
  induction xs generalizing seen with
  | nil => intro y hy; simp [firstOccurrences] at hy
  | cons x xs ih =>
    intro y hy
    unfold firstOccurrences at hy
    split at hy
    · exact ih seen y hy
    · rename_i hx
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact fun h => ih (x :: seen) y hy (List.mem_cons_of_mem x h)

/-- The filter's output has no repeated index. -/
theorem firstOccurrences_nodup (seen xs : List UInt32) :
    (firstOccurrences seen xs).Nodup := by
  induction xs generalizing seen with
  | nil => simp [firstOccurrences]
  | cons x xs ih =>
    unfold firstOccurrences
    split
    · exact ih seen
    · rw [List.nodup_cons]
      exact ⟨fun hx => firstOccurrences_not_mem_seen (x :: seen) xs x hx List.mem_cons_self,
        ih (x :: seen)⟩

/-- The seen set as packed words: one bit per weight, `weightSpace / 64`
words. -/
def seenWords : Nat := weightSpace / 64

/-- The word holding index `i`'s bit — `idx >> 6`, reduced modulo the word
count so the definition is total; below `weightSpace` the reduction is the
identity (`wordOf_eq_div`). -/
def wordOf (i : Nat) : Nat := (i >>> 6) % seenWords

/-- `wordOf` indexes the word array. -/
theorem wordOf_lt (i : Nat) : wordOf i < seenWords := Nat.mod_lt _ (by decide)

/-- The bit of index `i` inside its word — `1 << (idx & 63)`. -/
def bitOf (i : Nat) : UInt64 := (1 : UInt64) <<< UInt64.ofNat (i &&& 63)

/-- Whether index `i`'s bit is set — `seen[word] & bit != 0`. -/
def seenBit (seen : Vector UInt64 seenWords) (i : Nat) : Prop :=
  seen[wordOf i]'(wordOf_lt i) &&& bitOf i ≠ 0

instance (seen : Vector UInt64 seenWords) (i : Nat) : Decidable (seenBit seen i) :=
  inferInstanceAs (Decidable (seen[wordOf i]'(wordOf_lt i) &&& bitOf i ≠ 0))

/-- Set index `i`'s bit — `seen[word] |= bit`. -/
def markSeen (seen : Vector UInt64 seenWords) (i : Nat) : Vector UInt64 seenWords :=
  seen.set (wordOf i) (seen[wordOf i]'(wordOf_lt i) ||| bitOf i) (wordOf_lt i)

/-- One index of the pass: keep it when its bit is clear, and set the bit. -/
def uniqueStep (acc : Vector UInt64 seenWords × Array UInt32) (x : UInt32) :
    Vector UInt64 seenWords × Array UInt32 :=
  if seenBit acc.1 x.toNat then acc else (markSeen acc.1 x.toNat, acc.2.push x)

/-- `ActiveSet::unique`: first-occurrence unique over the packed seen set, in
one pass with no allocation beyond the output. -/
def uniqueIndices (xs : Array UInt32) : Array UInt32 :=
  (xs.foldl uniqueStep (Vector.replicate seenWords 0, Array.emptyWithCapacity xs.size)).2

/-- `x &&& 2^b` is non-zero exactly when bit `b` of `x` is set. -/
theorem and_two_pow_ne_zero_iff (x b : Nat) : x &&& 2 ^ b ≠ 0 ↔ x.testBit b = true := by
  constructor
  · intro h
    cases hb : x.testBit b with
    | true => rfl
    | false =>
      exfalso
      apply h
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : b = j
      · subst hj
        simp [hb]
      · simp [hj]
  · intro hb h
    have := congrArg (fun n => n.testBit b) h
    simp [Nat.testBit_and, hb] at this

/-- A word is non-zero exactly when its `Nat` image is. -/
theorem uint64_ne_zero_iff (a : UInt64) : a ≠ 0 ↔ a.toNat ≠ 0 := by
  constructor
  · intro h h0
    exact h (UInt64.toNat_inj.1 (by simpa using h0))
  · intro h h0
    exact h (by simp [h0])

/-- `bitOf i` is the single bit `i % 64`. -/
theorem toNat_bitOf (i : Nat) : (bitOf i).toNat = 2 ^ (i % 64) := by
  have h63 : i &&& 63 = i % 64 := Nat.and_two_pow_sub_one_eq_mod i 6
  have hlt : i % 64 < 64 := Nat.mod_lt _ (by decide)
  unfold bitOf
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', h63,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (by decide)), Nat.mod_eq_of_lt hlt]
  rw [show (1 : UInt64).toNat = 1 from rfl, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hlt)

/-- Below `weightSpace`, `wordOf` is the plain quotient `i / 64`. -/
theorem wordOf_eq_div (i : Nat) (hi : i < weightSpace) : wordOf i = i / 64 := by
  have hw : weightSpace = 16384 := rfl
  rw [hw] at hi
  unfold wordOf
  rw [Nat.shiftRight_eq_div_pow]
  show i / 64 % 256 = i / 64
  exact Nat.mod_eq_of_lt (by omega)

/-- Marking `i` sets exactly `i`'s bit: `j` is seen afterwards iff it was seen
before or `j = i`, for indices inside the space. -/
theorem seenBit_markSeen (seen : Vector UInt64 seenWords) (i j : Nat)
    (hi : i < weightSpace) (hj : j < weightSpace) :
    seenBit (markSeen seen i) j ↔ seenBit seen j ∨ i = j := by
  unfold seenBit markSeen
  by_cases hw : wordOf i = wordOf j
  · have hdiv : i / 64 = j / 64 := by rwa [wordOf_eq_div i hi, wordOf_eq_div j hj] at hw
    have hij : i = j ↔ i % 64 = j % 64 := ⟨fun h => h ▸ rfl, fun _ => by omega⟩
    simp only [← hw, Vector.getElem_set_self]
    rw [uint64_ne_zero_iff, uint64_ne_zero_iff, UInt64.toNat_and, UInt64.toNat_and,
      UInt64.toNat_or, toNat_bitOf, toNat_bitOf, and_two_pow_ne_zero_iff,
      and_two_pow_ne_zero_iff, Nat.testBit_or, Nat.testBit_two_pow, hij]
    simp
  · rw [Vector.getElem_set_ne (wordOf_lt i) (wordOf_lt j) hw]
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact absurd rfl hw

/-- The all-zero seen set has no bit set. -/
theorem not_seenBit_replicate_zero (i : Nat) : ¬ seenBit (Vector.replicate seenWords 0) i := by
  unfold seenBit
  rw [Vector.getElem_replicate, uint64_ne_zero_iff, UInt64.toNat_and]
  simp

/-- The packed pass, started from a seen set that represents `S`, computes the
list statement started from `S`, for every list of in-space indices. -/
theorem foldl_uniqueStep_eq (l : List UInt32) (seen : Vector UInt64 seenWords)
    (S : List UInt32) (out : Array UInt32)
    (hrepr : ∀ x : UInt32, x.toNat < weightSpace → (seenBit seen x.toNat ↔ x ∈ S))
    (hl : ∀ x ∈ l, x.toNat < weightSpace) :
    (l.foldl uniqueStep (seen, out)).2.toList = out.toList ++ firstOccurrences S l := by
  induction l generalizing seen S out with
  | nil => simp [firstOccurrences]
  | cons x l ih =>
    have hx : x.toNat < weightSpace := hl x List.mem_cons_self
    have hl' : ∀ y ∈ l, y.toNat < weightSpace := fun y hy => hl y (List.mem_cons_of_mem x hy)
    rw [List.foldl_cons]
    have hstep : uniqueStep (seen, out) x =
        if seenBit seen x.toNat then (seen, out) else (markSeen seen x.toNat, out.push x) := rfl
    rw [hstep]
    unfold firstOccurrences
    by_cases hs : seenBit seen x.toNat
    · rw [if_pos hs, if_pos ((hrepr x hx).1 hs)]
      exact ih seen S out hrepr hl'
    · rw [if_neg hs, if_neg (fun h => hs ((hrepr x hx).2 h))]
      rw [ih (markSeen seen x.toNat) (x :: S) (out.push x) ?_ hl']
      · simp
      · intro y hy
        rw [seenBit_markSeen seen x.toNat y.toNat hx hy, hrepr y hy, List.mem_cons,
          UInt32.toNat_inj]
        exact ⟨fun h => h.elim Or.inr (fun e => Or.inl e.symm),
          fun h => h.elim (fun e => Or.inr e.symm) Or.inl⟩

/-- The mirror computes the statement: for every array of in-space indices,
`uniqueIndices` is `firstOccurrences` from the empty seen set. -/
theorem uniqueIndices_eq (xs : Array UInt32) (h : ∀ x ∈ xs, x.toNat < weightSpace) :
    (uniqueIndices xs).toList = firstOccurrences [] xs.toList := by
  unfold uniqueIndices
  rw [← Array.foldl_toList,
    foldl_uniqueStep_eq xs.toList (Vector.replicate seenWords 0) [] (Array.emptyWithCapacity xs.size)]
  · simp
  · intro x _
    exact ⟨fun hs => absurd hs (not_seenBit_replicate_zero _), fun hx => absurd hx List.not_mem_nil⟩
  · intro x hx
    exact h x (Array.mem_def.2 hx)

/-- No index appears twice in the mirror's output. -/
theorem uniqueIndices_nodup (xs : Array UInt32) (h : ∀ x ∈ xs, x.toNat < weightSpace) :
    (uniqueIndices xs).toList.Nodup := by
  rw [uniqueIndices_eq xs h]
  exact firstOccurrences_nodup [] _

/-- The mirror's output is a subsequence of its input: first-occurrence order
is preserved and nothing is invented. -/
theorem uniqueIndices_sublist (xs : Array UInt32) (h : ∀ x ∈ xs, x.toNat < weightSpace) :
    (uniqueIndices xs).toList.Sublist xs.toList := by
  rw [uniqueIndices_eq xs h]
  exact firstOccurrences_sublist [] _

/-- Every masked index is inside the weight space — the `FeatIdx` bound. -/
theorem mask_lt (h : UInt64) : (mask h).toNat < weightSpace := by
  unfold mask
  rw [UInt32.toNat_and]
  exact Nat.and_lt_two_pow (n := 14) _ (by decide)

/-- Every index `encodeWordsGo` pushes is masked. -/
theorem encodeWordsGo_lt (f : Featurizer) (t : UInt64) (words : Array (UInt64 × UInt64))
    (out : Array UInt32) (k fuel : Nat) (hout : ∀ x ∈ out, x.toNat < weightSpace) :
    ∀ x ∈ encodeWordsGo f t words out k fuel, x.toNat < weightSpace := by
  induction fuel generalizing out k with
  | zero => simpa [encodeWordsGo] using hout
  | succ fuel ih =>
    unfold encodeWordsGo
    apply ih
    intro x hx
    rcases Array.mem_push.1 hx with hx | rfl
    · exact hout x hx
    · exact mask_lt _

/-- Every index `encodeTilingsGo` pushes is masked. -/
theorem encodeTilingsGo_lt (f : Featurizer) (words : Array (UInt64 × UInt64))
    (out : Array UInt32) (t fuel : Nat) (hout : ∀ x ∈ out, x.toNat < weightSpace) :
    ∀ x ∈ encodeTilingsGo f words out t fuel, x.toNat < weightSpace := by
  induction fuel generalizing out t with
  | zero => simpa [encodeTilingsGo] using hout
  | succ fuel ih =>
    unfold encodeTilingsGo
    exact ih _ _ (encodeWordsGo_lt f _ words out 0 words.size hout)

/-- An imprint unit pushes only a masked index. -/
theorem imprintPush_lt (f : Featurizer) (patch : ByteArray) (out : Array UInt32) (u : Nat)
    (hout : ∀ x ∈ out, x.toNat < weightSpace) :
    ∀ x ∈ imprintPush f patch out u, x.toNat < weightSpace := by
  unfold imprintPush
  split
  · intro x hx
    rcases Array.mem_push.1 hx with hx | rfl
    · exact hout x hx
    · exact mask_lt _
  · exact hout

/-- Every index `imprintUnitsGo` pushes is masked. -/
theorem imprintUnitsGo_lt (f : Featurizer) (patch : ByteArray) (out : Array UInt32)
    (u fuel : Nat) (hout : ∀ x ∈ out, x.toNat < weightSpace) :
    ∀ x ∈ imprintUnitsGo f patch out u fuel, x.toNat < weightSpace := by
  induction fuel generalizing out u with
  | zero => exact hout
  | succ fuel ih => exact ih (imprintPush f patch out u) (u + 1) (imprintPush_lt f patch out u hout)

/-- The raw hash image of `encode`: the tile-coded sensor words, then the
active imprinting units' indices, before the unique pass. -/
def rawEncode (f : Featurizer) (words : Array (UInt64 × UInt64)) (patch : ByteArray) :
    Array UInt32 :=
  imprintUnitsGo f patch (encodeTilingsGo f words (Array.emptyWithCapacity 4096) 0 nTilings.toNat)
    0 imprintUnits

/-- Every raw index is masked into the weight space. -/
theorem rawEncode_lt (f : Featurizer) (words : Array (UInt64 × UInt64)) (patch : ByteArray) :
    ∀ x ∈ rawEncode f words patch, x.toNat < weightSpace := by
  have hraw := imprintUnitsGo_lt f patch
    (encodeTilingsGo f words (Array.emptyWithCapacity 4096) 0 nTilings.toNat) 0 imprintUnits
    (encodeTilingsGo_lt f words (Array.emptyWithCapacity 4096) 0 nTilings.toNat
      (fun x hx => by simp at hx))
  unfold rawEncode
  exact hraw

/-- `Featurizer::encode` — the raw hash image uniqued in construction order,
so each index appears at most once. `patch` is the 121 opaque tile codes,
row-major. -/
def encode (f : Featurizer) (words : Array (UInt64 × UInt64)) (patch : ByteArray) :
    Array UInt32 :=
  uniqueIndices (rawEncode f words patch)

/-- No learner in the specification sees a repeated index. -/
theorem encode_nodup (f : Featurizer) (words : Array (UInt64 × UInt64)) (patch : ByteArray) :
    (f.encode words patch).toList.Nodup := by
  unfold encode
  exact uniqueIndices_nodup _ (rawEncode_lt f words patch)

/-- The encoded vector is the raw hash image with later repeats dropped —
first-occurrence order, nothing invented. -/
theorem encode_sublist_raw (f : Featurizer) (words : Array (UInt64 × UInt64))
    (patch : ByteArray) :
    (f.encode words patch).toList.Sublist (rawEncode f words patch).toList := by
  unfold encode
  exact uniqueIndices_sublist _ (rawEncode_lt f words patch)

end Featurizer

/-- `features::bucket` — log-scale bucket for resource counts. -/
def bucket (n : UInt32) : UInt8 :=
  let rec
    /-- Shift-count loop, fuel-bounded at the 8-bucket cap. -/
    go (n : UInt32) (b : UInt8) : Nat → UInt8
      | 0 => b
      | fuel + 1 => if 0 < n then go (n >>> 1) (b + 1) fuel else b
  go n 0 8

end AcornSpec
