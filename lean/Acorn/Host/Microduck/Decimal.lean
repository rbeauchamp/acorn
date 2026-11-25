import Acorn.Json

namespace Acorn.Host.Microduck

def width (value : Nat) : Nat :=
  value.log2 / 3 + 1

theorem width_bound (value : Nat) : value < 10 ^ width value := by
  have binary : value < 2 ^ (value.log2 + 1) := Nat.lt_log2_self
  have octal : 2 ^ (value.log2 + 1) ≤ (2 ^ 3) ^ width value := by
    rw [← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by unfold width; omega)
  have ten : (2 ^ 3) ^ width value ≤ 10 ^ width value :=
    Nat.pow_le_pow_left (by decide) _
  exact Nat.lt_of_lt_of_le binary (Nat.le_trans octal ten)

theorem width_positive (value : Nat) : 0 < width value := by
  unfold width
  omega

structure Decimal where
  negative : Bool
  digits : Nat
  exponent : Int

structure Scale where
  places : Nat
  low : Int
  high : Int
  ordered : low ≤ high

abbrev Scale.Word (scale : Scale) : Type :=
  { value : Int // scale.low ≤ value ∧ value ≤ scale.high }

def Scale.width (scale : Scale) : Nat :=
  Microduck.width (max scale.low.natAbs scale.high.natAbs)

theorem Scale.width_bound (scale : Scale) :
    scale.low.natAbs < 10 ^ scale.width ∧ scale.high.natAbs < 10 ^ scale.width := by
  have larger := Microduck.width_bound (max scale.low.natAbs scale.high.natAbs)
  have left := Nat.le_max_left scale.low.natAbs scale.high.natAbs
  have right := Nat.le_max_right scale.low.natAbs scale.high.natAbs
  unfold Scale.width
  constructor <;> omega

def Scale.clamp (scale : Scale) (value : Int) : scale.Word :=
  if below : value < scale.low then ⟨scale.low, Int.le_refl _, scale.ordered⟩
  else if above : scale.high < value then ⟨scale.high, scale.ordered, Int.le_refl _⟩
  else ⟨value, Int.not_lt.mp below, Int.not_lt.mp above⟩

theorem Scale.clamp_value (scale : Scale) (value : Int) :
    (scale.clamp value).val = max scale.low (min scale.high value) := by
  have ordered := scale.ordered
  unfold Scale.clamp
  split
  · show scale.low = _
    omega
  · split
    · show scale.high = _
      omega
    · show value = _
      omega

def Decimal.shift (decimal : Decimal) (places : Nat) : Int :=
  decimal.exponent + places

def Decimal.magnitude (decimal : Decimal) (places : Nat) : Nat :=
  (2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
      10 ^ (-decimal.shift places).toNat) /
    (2 * 10 ^ (-decimal.shift places).toNat)

theorem Decimal.magnitude_bounds (decimal : Decimal) (places : Nat) :
    2 * decimal.magnitude places * 10 ^ (-decimal.shift places).toNat ≤
        2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
          10 ^ (-decimal.shift places).toNat ∧
      2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
          10 ^ (-decimal.shift places).toNat <
        2 * (decimal.magnitude places + 1) * 10 ^ (-decimal.shift places).toNat := by
  have unit : 0 < 2 * 10 ^ (-decimal.shift places).toNat :=
    Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  have lower := Nat.div_mul_le_self
    (2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
      10 ^ (-decimal.shift places).toNat) (2 * 10 ^ (-decimal.shift places).toNat)
  have upper := Nat.lt_mul_div_succ
    (2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
      10 ^ (-decimal.shift places).toNat) unit
  unfold Decimal.magnitude
  constructor
  · rw [Nat.mul_comm 2, Nat.mul_assoc]
    exact lower
  · rw [Nat.mul_right_comm]
    exact upper

theorem Decimal.magnitude_vanishes (decimal : Decimal) (places : Nat)
    (small : decimal.digits = 0 ∨
      (width decimal.digits : Int) + decimal.shift places < 0) :
    decimal.magnitude places = 0 := by
  have unit : 0 < 10 ^ (-decimal.shift places).toNat := Nat.pow_pos (by decide)
  unfold Decimal.magnitude
  apply Nat.div_eq_of_lt
  rcases small with none | far
  · rw [none]
    omega
  · have count := width_bound decimal.digits
    have whole : (decimal.shift places).toNat = 0 := by omega
    have grows : 10 ^ (width decimal.digits + 1) ≤ 10 ^ (-decimal.shift places).toNat :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at grows
    rw [whole, Nat.pow_zero, Nat.mul_one]
    omega

theorem Decimal.magnitude_beyond (decimal : Decimal) (places bound : Nat)
    (present : decimal.digits ≠ 0) (far : (bound : Int) ≤ decimal.shift places) :
    10 ^ bound ≤ decimal.magnitude places := by
  have none : (-decimal.shift places).toNat = 0 := by omega
  have grows : 10 ^ bound ≤ 10 ^ (decimal.shift places).toNat :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have scaled : 10 ^ (decimal.shift places).toNat ≤
      decimal.digits * 10 ^ (decimal.shift places).toNat :=
    Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero present)
  unfold Decimal.magnitude
  rw [none, Nat.pow_zero, Nat.mul_one]
  omega

def Decimal.rounded (decimal : Decimal) (places : Nat) : Int :=
  if decimal.negative then -(decimal.magnitude places : Int) else decimal.magnitude places

def Decimal.fixed (scale : Scale) (decimal : Decimal) : scale.Word :=
  if decimal.digits = 0 ∨
      (width decimal.digits : Int) + decimal.shift scale.places < 0 then
    scale.clamp 0
  else if (scale.width : Int) ≤ decimal.shift scale.places then
    if decimal.negative then ⟨scale.low, Int.le_refl _, scale.ordered⟩
    else ⟨scale.high, scale.ordered, Int.le_refl _⟩
  else scale.clamp (decimal.rounded scale.places)

theorem Decimal.fixed_clamp (scale : Scale) (decimal : Decimal) :
    decimal.fixed scale = scale.clamp (decimal.rounded scale.places) := by
  have ordered := scale.ordered
  have reach := scale.width_bound
  unfold Decimal.fixed
  split
  · rename_i small
    have zero := decimal.magnitude_vanishes scale.places small
    unfold Decimal.rounded
    rw [zero]
    cases decimal.negative <;> rfl
  · rename_i large
    split
    · rename_i far
      have present : decimal.digits ≠ 0 := fun none => large (Or.inl none)
      have beyond := decimal.magnitude_beyond scale.places scale.width present far
      split
      · rename_i minus
        apply Subtype.ext
        rw [Scale.clamp_value]
        unfold Decimal.rounded
        simp only [minus, ↓reduceIte]
        omega
      · rename_i plus
        apply Subtype.ext
        rw [Scale.clamp_value]
        unfold Decimal.rounded
        simp only [plus, Bool.false_eq_true, ↓reduceIte]
        omega
    · rfl

theorem Decimal.shift_between (scale : Scale) (decimal : Decimal)
    (large : ¬(decimal.digits = 0 ∨
      (width decimal.digits : Int) + decimal.shift scale.places < 0))
    (near : ¬(scale.width : Int) ≤ decimal.shift scale.places) :
    (decimal.shift scale.places).toNat < scale.width ∧
      (-decimal.shift scale.places).toNat ≤ width decimal.digits := by
  have count : ¬(width decimal.digits : Int) + decimal.shift scale.places < 0 :=
    fun far => large (Or.inr far)
  have some := width_positive (max scale.low.natAbs scale.high.natAbs)
  unfold Scale.width at near ⊢
  constructor <;> omega

def spelled (digits : List Char) : Nat :=
  digits.foldl (fun total c => 10 * total + (c.toNat - 48)) 0

theorem spelled_from (total : Nat) (digits : List Char) :
    digits.foldl (fun total c => 10 * total + (c.toNat - 48)) total =
      total * 10 ^ digits.length + spelled digits := by
  unfold spelled
  induction digits generalizing total with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  | cons head tail hold =>
    have move : total * (10 ^ tail.length * 10) = 10 * total * 10 ^ tail.length := by
      rw [Nat.mul_comm (10 ^ tail.length) 10, ← Nat.mul_assoc, Nat.mul_comm total 10]
    rw [List.foldl_cons, List.foldl_cons, hold (10 * total + (head.toNat - 48)),
      hold (10 * 0 + (head.toNat - 48)), List.length_cons, Nat.pow_succ, move, Nat.mul_zero,
      Nat.zero_add, Nat.add_mul, Nat.add_assoc]

theorem spelled_append (first second : List Char) :
    spelled (first ++ second) = spelled first * 10 ^ second.length + spelled second := by
  unfold spelled
  rw [List.foldl_append]
  exact spelled_from _ second

def power : Option Json.Exponent → Int
  | none => 0
  | some part =>
    if part.sign = some true then -(spelled part.digits : Int) else spelled part.digits

def Decimal.ofNumeral (numeral : Json.Numeral) : Decimal :=
  ⟨numeral.negative, spelled (numeral.whole ++ numeral.fraction.getD []),
    power numeral.exponent - (numeral.fraction.getD []).length⟩

def Decimal.read (value : Json.Value) : Option Decimal :=
  value.numeral.map Decimal.ofNumeral

theorem Decimal.read_iff (value : Json.Value) (decimal : Decimal) :
    Decimal.read value = some decimal ↔
      ∃ numeral : Json.Numeral, numeral.Formed ∧
        value = .number (String.ofList numeral.chars) ∧
          Decimal.ofNumeral numeral = decimal := by
  unfold Decimal.read
  constructor
  · intro found
    cases scanned : value.numeral with
    | none =>
      rw [scanned] at found
      exact nomatch found
    | some numeral =>
      rw [scanned] at found
      obtain ⟨formed, same⟩ := (Json.Value.numeral_iff value numeral).mp scanned
      exact ⟨numeral, formed, same, Option.some.inj found⟩
  · rintro ⟨numeral, formed, same, rfl⟩
    rw [(Json.Value.numeral_iff value numeral).mpr ⟨formed, same⟩]
    rfl

def Scale.Kept (scale : Scale) (json : Json.Value) (word : scale.Word) : Prop :=
  ∃ numeral : Json.Numeral, numeral.Formed ∧
    json = .number (String.ofList numeral.chars) ∧
      (Decimal.ofNumeral numeral).fixed scale = word

def Counted (json : Json.Value) (natural : Nat) : Prop :=
  ∃ digits : List Char, (⟨false, digits, none, none⟩ : Json.Numeral).Formed ∧
    json = .number (String.ofList digits) ∧ spelled digits = natural

def Signed (json : Json.Value) (integer : Int) : Prop :=
  ∃ (negative : Bool) (digits : List Char),
    (⟨negative, digits, none, none⟩ : Json.Numeral).Formed ∧
      json = .number (String.ofList (⟨negative, digits, none, none⟩ : Json.Numeral).chars) ∧
        (if negative then -(spelled digits : Int) else spelled digits) = integer

theorem spelled_digits (natural : Nat) : spelled (Json.Numeral.digits natural) = natural := by
  have single : ∀ digit : Fin 10, spelled [Json.Numeral.figure digit] = digit.val := fun digit => by
    show 10 * 0 + ((Json.Numeral.figure digit).toNat - 48) = digit.val
    rw [(Json.Numeral.figure_digit digit).2, Nat.mul_zero, Nat.zero_add]
  induction natural using Nat.strongRecOn with
  | ind natural hold =>
    unfold Json.Numeral.digits
    split
    · exact single _
    · rename_i large
      rw [spelled_append, hold (natural / 10) (by omega), single]
      show natural / 10 * 10 ^ 1 + natural % 10 = natural
      omega

theorem counted_natural (natural : Nat) :
    Counted (.number (String.ofList (Json.Numeral.natural natural).chars)) natural :=
  ⟨Json.Numeral.digits natural, Json.Numeral.natural_formed natural, by
    simp [Json.Numeral.natural, Json.Numeral.chars, Json.Numeral.fractionChars,
      Json.Numeral.exponentChars], spelled_digits natural⟩

end Acorn.Host.Microduck
