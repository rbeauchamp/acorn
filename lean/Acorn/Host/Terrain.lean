import Acorn.Host.Geometry
import Acorn.Rng

namespace Acorn.Host

inductive TileKind where
  | water
  | sand
  | grass
  | forest
  | tree
  | mountain
  | stone
  | ore
  deriving DecidableEq

def TileKind.code : TileKind → UInt8
  | .water => 0 | .sand => 1 | .grass => 2 | .forest => 3
  | .tree => 4 | .mountain => 5 | .stone => 6 | .ore => 7

def TileKind.fromCode (code : UInt8) : TileKind :=
  if code == 0 then .water else if code == 1 then .sand
  else if code == 2 then .grass else if code == 3 then .forest
  else if code == 4 then .tree else if code == 5 then .mountain
  else if code == 6 then .stone else .ore

theorem TileKind.code_roundtrip (kind : TileKind) : fromCode kind.code = kind := by
  cases kind <;> rfl

theorem TileKind.code_bound (kind : TileKind) : kind.code.toNat < 8 := by
  cases kind <;> decide

def TileKind.walkable : TileKind → Bool
  | .water | .mountain => false
  | .sand | .grass | .forest | .tree | .stone | .ore => true

def TileKind.Walkable (kind : TileKind) : Prop := kind ≠ .water ∧ kind ≠ .mountain

theorem TileKind.walkable_iff (kind : TileKind) : kind.walkable = true ↔ kind.Walkable := by
  cases kind <;> simp [TileKind.walkable, TileKind.Walkable]

instance (kind : TileKind) : Decidable kind.Walkable := decidable_of_iff _ kind.walkable_iff

theorem TileKind.decide_walkable (kind : TileKind) : decide kind.Walkable = kind.walkable := by
  cases kind <;> rfl

def TileKind.harvestYield : TileKind → Option Item
  | .tree => some .wood | .stone => some .stone | .ore => some .gold
  | .water | .sand | .grass | .forest | .mountain => none

inductive WorldError where
  | coordinateOverflow
  | inadmissibleConfig
  deriving DecidableEq

def assemble32 (negative : Bool) (exponent fraction : Nat) : Binary32 :=
  ⟨((if negative then 2 ^ 31 else 0) + exponent * 2 ^ 23 + fraction).toUInt32⟩

def floorFraction (negative : Bool) (fraction divisor : Nat) : Nat :=
  (fraction / divisor + if negative && fraction % divisor != 0 then 1 else 0) * divisor

def floor32Spec (value : Binary32) : Binary32 :=
  let exponent := value.magnitude / 2 ^ 23
  let fraction := value.magnitude % 2 ^ 23
  if exponent = 255 then value
  else if exponent ≥ 150 then value
  else if exponent < 127 then
    if value.negative && value.magnitude != 0 then ⟨0xbf800000⟩
    else assemble32 value.negative 0 0
  else
    assemble32 value.negative exponent
      (floorFraction value.negative fraction (2 ^ (150 - exponent)))

def floorFractionWord (negative : Bool) (fraction divisor : UInt64) : UInt64 :=
  (fraction / divisor + if negative && fraction % divisor != 0 then 1 else 0) * divisor

theorem floorFractionWord_exact (negative : Bool) (fraction divisor : UInt64)
    (hf : fraction.toNat < 2^23) (hd : divisor.toNat ≤ 2^23) :
    (floorFractionWord negative fraction divisor).toNat =
      floorFraction negative fraction.toNat divisor.toNat := by
  have hq := Nat.div_le_self fraction.toNat divisor.toNat
  have hm := Nat.div_mul_le_self fraction.toNat divisor.toNat
  have cond : (negative && fraction % divisor != 0) =
      (negative && fraction.toNat % divisor.toNat != 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, ← UInt64.toNat_inj,
      UInt64.toNat_mod, UInt64.toNat_zero]
  simp only [floorFractionWord, floorFraction, cond]
  split <;> simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_div,
    UInt64.toNat_one, UInt64.toNat_zero]
  · have sum : fraction.toNat / divisor.toNat + 1 < 2^64 := by omega
    rw [Nat.mod_eq_of_lt sum, Nat.add_mul, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega : fraction.toNat / divisor.toNat < 2^64)]
    exact Nat.mod_eq_of_lt (by omega)

def floorFractionShift (negative : Bool) (fraction shift : UInt64) : UInt64 :=
  let divisor := (1 : UInt64) <<< shift
  ((fraction >>> shift) +
    if negative && fraction &&& (divisor - 1) != 0 then 1 else 0) * divisor

theorem floorFractionShift_exact (negative : Bool) (fraction shift : UInt64)
    (bounded : shift.toNat < 64) :
    floorFractionShift negative fraction shift =
      floorFractionWord negative fraction ((1 : UInt64) <<< shift) := by
  simp only [floorFractionShift, floorFractionWord,
    Rounding.shiftQuotient_exact fraction shift bounded,
    Rounding.maskRemainder_exact fraction shift bounded]

def assemble32Word (negative : Bool) (exponent fraction : UInt64) : Binary32 :=
  ⟨((if negative then 0x80000000 else 0) + exponent * 0x800000 + fraction).toUInt32⟩

theorem assemble32Word_exact (negative : Bool) (exponent fraction : UInt64) :
    assemble32Word negative exponent fraction = assemble32 negative exponent.toNat fraction.toNat := by
  cases negative <;> apply congrArg Binary32.mk <;> apply UInt32.toNat.inj <;>
    simp [UInt64.toNat_toUInt32, Nat.add_mod, Nat.mul_mod]

def floor32 (value : Binary32) : Binary32 :=
  let magnitude := (value.bits &&& 0x7fffffff).toUInt64
  let exponent := magnitude / 0x800000
  let fraction := magnitude % 0x800000
  if exponent ≥ 150 then value
  else if exponent < 127 then
    if decide value.Negative && magnitude != 0 then ⟨0xbf800000⟩
    else assemble32Word (decide value.Negative) 0 0
  else
    assemble32Word (decide value.Negative) exponent
      (floorFractionShift (decide value.Negative) fraction (150 - exponent))

theorem floor32_eq_spec (value : Binary32) : floor32 value = floor32Spec value := by
  have hm : ((value.bits &&& 0x7fffffff).toUInt64).toNat = value.magnitude := by
    rw [UInt32.toNat_toUInt64]
    rfl
  have he : (((value.bits &&& 0x7fffffff).toUInt64) / 0x800000).toNat =
      value.magnitude / 2^23 := by rw [UInt64.toNat_div, hm]; rfl
  have hf : (((value.bits &&& 0x7fffffff).toUInt64) % 0x800000).toNat =
      value.magnitude % 2^23 := by rw [UInt64.toNat_mod, hm]; rfl
  unfold floor32 floor32Spec
  simp only [ge_iff_le, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat, he, Binary32.decide_negative]
  by_cases high : 150 ≤ value.magnitude / 2^23
  · simp [high]
  have notExceptional : value.magnitude / 2^23 ≠ 255 := by omega
  simp only [high, notExceptional, ↓reduceIte]
  split
  · have hz : ((value.bits &&& 0x7fffffff).toUInt64 != 0) = (value.magnitude != 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne, ne_eq, ← UInt64.toNat_inj, hm, UInt64.toNat_zero]
    simp only [hz, assemble32Word_exact, UInt64.toNat_zero]
  · rename_i low
    have hs : (150 - (((value.bits &&& 0x7fffffff).toUInt64) / 0x800000)).toNat =
        150 - value.magnitude / 2^23 := by
      rw [UInt64.toNat_sub_of_le]
      · rw [he]; rfl
      · rw [UInt64.le_iff_toNat_le, he]; change _ ≤ 150; omega
    have shiftBound : (150 - (((value.bits &&& 0x7fffffff).toUInt64) / 0x800000)).toNat ≤ 23 := by
      rw [hs]; omega
    have hd := Rounding.shiftDenominator_exact
      (150 - (((value.bits &&& 0x7fffffff).toUInt64) / 0x800000)) (by omega)
    rw [floorFractionShift_exact _ _ _ (by omega), assemble32Word_exact,
      floorFractionWord_exact, he, hf, hd, hs]
    · rw [hf]; exact Nat.mod_lt _ (by decide)
    · rw [hd]
      exact Nat.pow_le_pow_right (by decide) shiftBound

theorem floor32_exceptional (value : Binary32)
    (h : value.magnitude / 2 ^ 23 = 255) : floor32 value = value := by rw [floor32_eq_spec]; simp [floor32Spec, h]

@[noinline] def castWord (value : Binary32) : Binary64 :=
  if value.IsNaN then ⟨0x7ff8000000000000⟩ else Conversion.widen value

def coordinateCast (value : Binary32) : Coordinate :=
  ⟨Conversion.toI64 (castWord value), by
    rw [Conversion.toI64_eq_signedCast]
    exact Conversion.signedCast_bounds 63 _⟩

def coordinateWord (coordinate : Coordinate) : UInt64 :=
  (Int64.ofInt coordinate.val).toUInt64

theorem coordinateWord_eq (coordinate : Coordinate) : coordinateWord coordinate =
    (coordinate.val % (2 ^ 64 : Int)).toNat.toUInt64 := by
  apply UInt64.toNat.inj
  change (BitVec.ofInt 64 coordinate.val).toNat = _
  rw [BitVec.toNat_ofInt, UInt64.toNat_ofNat']
  have bound := Int.emod_lt_of_pos coordinate.val (show (0 : Int) < 2^64 by decide)
  omega

def smooth (value : Binary32) : Binary32 :=
  (value.mul value).mul ((⟨0x40400000⟩ : Binary32).sub ((⟨0x40000000⟩ : Binary32).mul value))

def lattice (x y : Coordinate) (seed : UInt64) : Binary32 :=
  (Binary32.ofUInt64 (Rng.hash2 (coordinateWord x) (coordinateWord y) seed >>> 32)).mul
    ⟨0x2f800000⟩

def valueNoise (position : Position) (scale : Binary32) (seed : UInt64) :
    Except WorldError Binary32 := do
  let fx := (coordinateFloat position.x).div scale
  let fy := (coordinateFloat position.y).div scale
  let x0 := floor32 fx
  let y0 := floor32 fy
  let tx := smooth (fx.sub x0)
  let ty := smooth (fy.sub y0)
  let xi := coordinateCast x0
  let yi := coordinateCast y0
  let some x1 := Coordinate.checked (xi.val + 1) | .error .coordinateOverflow
  let some y1 := Coordinate.checked (yi.val + 1) | .error .coordinateOverflow
  let h00 := lattice xi yi seed
  let h10 := lattice x1 yi seed
  let h01 := lattice xi y1 seed
  let h11 := lattice x1 y1 seed
  let top := h00.add ((h10.sub h00).mul tx)
  let bot := h01.add ((h11.sub h01).mul tx)
  return top.add ((bot.sub top).mul ty)

def octaveLoop : Nat → Position → UInt64 → Binary32 → Binary32 → Binary32 →
    Except WorldError Binary32
  | 0, _, _, _, _, sum => .ok sum
  | count + 1, position, seed, scale, amplitude, sum => do
    let noise ← valueNoise position scale seed
    octaveLoop count position seed (scale.mul ⟨0x40000000⟩)
      (amplitude.mul ⟨0x3f000000⟩) (sum.add (amplitude.mul noise))

def fbm (position : Position) (seed : UInt64) (baseScale : Binary32) :
    Except WorldError Binary32 := octaveLoop 4 position seed baseScale ⟨0x3f000000⟩ ⟨0⟩

def classifyTerrain (position : Position) (seed : UInt64) (elevation moisture : Binary32) : TileKind :=
  if elevation.Less ⟨Acorn.Constants.band030Bits⟩ then .water
  else if elevation.Less ⟨Acorn.Constants.band0335Bits⟩ then .sand
  else if elevation.Less ⟨Acorn.Constants.band060Bits⟩ then .grass
  else if elevation.Less ⟨Acorn.Constants.band072Bits⟩ then
    if decide ((⟨Acorn.Constants.moist040Bits⟩ : Binary32).Less moisture) &&
        Rng.hash2 (coordinateWord position.x) (coordinateWord position.y) (seed ^^^ 7) % 100 < 60
    then .tree else .forest
  else if elevation.Less ⟨Acorn.Constants.band080Bits⟩ then
    if Rng.hash2 (coordinateWord position.x) (coordinateWord position.y) (seed ^^^ 9) % 100 < 10
    then .ore else .stone
  else .mountain

def terrain (position : Position) (seed : UInt64) (baseScale : Binary32) :
    Except WorldError TileKind := do
  let elevation ← fbm position (seed ^^^ 0xe1e0e1e000000001) baseScale
  let moisture ← fbm position (seed ^^^ 0xe1e0e1e000000002) baseScale
  return classifyTerrain position seed elevation moisture

end Acorn.Host
