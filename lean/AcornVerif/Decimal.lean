import Acorn.Host.Microduck.Wire
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace AcornVerif.Decimal
open Acorn.Host.Microduck

def value (decimal : Decimal) : ℚ :=
  (if decimal.negative then -1 else 1) * (decimal.digits : ℚ) * (10 : ℚ) ^ decimal.exponent

def Nearest (target : ℚ) (integer : ℤ) : Prop :=
  |(integer : ℚ) - target| ≤ 1 / 2 ∧
    (|(integer : ℚ) - target| = 1 / 2 → |target| < |(integer : ℚ)|)

theorem Nearest.apart {target : ℚ} {lesser greater : ℤ} (first : Nearest target lesser)
    (second : Nearest target greater) (ordered : lesser < greater) : False := by
  have step : (lesser : ℚ) + 1 ≤ greater := by exact_mod_cast ordered
  obtain ⟨_, above⟩ := abs_le.mp first.1
  obtain ⟨below, _⟩ := abs_le.mp second.1
  obtain ⟨under, _⟩ := abs_le.mp first.1
  obtain ⟨_, over⟩ := abs_le.mp second.1
  have atLesser : (lesser : ℚ) - target = -(1 / 2) := by linarith
  have atGreater : (greater : ℚ) - target = 1 / 2 := by linarith
  have tieLesser : |target| < |(lesser : ℚ)| :=
    first.2 (by rw [atLesser, abs_neg, abs_of_pos (by norm_num)])
  have tieGreater : |target| < |(greater : ℚ)| :=
    second.2 (by rw [atGreater, abs_of_pos (by norm_num)])
  rcases le_or_gt 0 lesser with natural | negative
  · have cast : (0 : ℚ) ≤ lesser := by exact_mod_cast natural
    rw [abs_of_nonneg cast, abs_of_nonneg (by linarith)] at tieLesser
    linarith
  · have cast : (lesser : ℚ) + 1 ≤ 0 := by exact_mod_cast negative
    rw [abs_of_nonpos (by linarith : (greater : ℚ) ≤ 0),
      abs_of_nonpos (by linarith : target ≤ 0)] at tieGreater
    linarith

theorem Nearest.unique {target : ℚ} {first second : ℤ} (one : Nearest target first)
    (other : Nearest target second) : first = second := by
  rcases lt_trichotomy first second with less | same | more
  · exact (one.apart other less).elim
  · exact same
  · exact (other.apart one more).elim

theorem power_split (shift : ℤ) :
    (10 : ℚ) ^ shift = (10 : ℚ) ^ shift.toNat / (10 : ℚ) ^ (-shift).toNat := by
  rcases le_or_gt 0 shift with whole | part
  · have none : (-shift).toNat = 0 := by omega
    have same : shift = (shift.toNat : ℤ) := (Int.toNat_of_nonneg whole).symm
    rw [none, pow_zero, div_one]
    conv_lhs => rw [same]
    exact zpow_natCast _ _
  · have none : shift.toNat = 0 := by omega
    have same : shift = -((-shift).toNat : ℤ) := by omega
    rw [none, pow_zero, one_div]
    conv_lhs => rw [same]
    rw [zpow_neg, zpow_natCast]

theorem rounded_nearest (decimal : Decimal) (places : ℕ) :
    Nearest (value decimal * (10 : ℚ) ^ places) (decimal.rounded places) := by
  obtain ⟨least, greatest⟩ := decimal.magnitude_bounds places
  have unit : (0 : ℚ) < (10 : ℚ) ^ (-decimal.shift places).toNat := by positivity
  have leastCast : 2 * (decimal.magnitude places : ℚ) * (10 : ℚ) ^ (-decimal.shift places).toNat ≤
      2 * ((decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat) +
        (10 : ℚ) ^ (-decimal.shift places).toNat := by exact_mod_cast least
  have greatestCast : 2 * ((decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat) +
        (10 : ℚ) ^ (-decimal.shift places).toNat <
      2 * ((decimal.magnitude places : ℚ) + 1) * (10 : ℚ) ^ (-decimal.shift places).toNat := by
    exact_mod_cast greatest
  have sum : (10 : ℚ) ^ decimal.exponent * (10 : ℚ) ^ places =
      (10 : ℚ) ^ decimal.shift places := by
    unfold Decimal.shift
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
  have scaled : (decimal.digits : ℚ) * (10 : ℚ) ^ decimal.exponent * (10 : ℚ) ^ places =
      (decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
        (10 : ℚ) ^ (-decimal.shift places).toNat := by
    rw [mul_assoc, sum, power_split, mul_div_assoc]
  have lower : (decimal.magnitude places : ℚ) - 1 / 2 ≤
      (decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
        (10 : ℚ) ^ (-decimal.shift places).toNat := by
    rw [le_div_iff₀ unit]
    linarith
  have upper : (decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
        (10 : ℚ) ^ (-decimal.shift places).toNat <
      (decimal.magnitude places : ℚ) + 1 / 2 := by
    rw [div_lt_iff₀ unit]
    linarith
  have natural : (0 : ℚ) ≤ (decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
      (10 : ℚ) ^ (-decimal.shift places).toNat := by positivity
  have whole : (0 : ℚ) ≤ (decimal.magnitude places : ℚ) := Nat.cast_nonneg _
  unfold Nearest value Decimal.rounded
  cases decimal.negative
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Int.cast_natCast]
    rw [scaled]
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, fun tie => ?_⟩
    rw [abs_of_nonneg natural, abs_of_nonneg whole]
    rcases (abs_eq (by norm_num : (0 : ℚ) ≤ 1 / 2)).mp tie with half | half <;> linarith
  · simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast]
    have flip : -1 * (decimal.digits : ℚ) * (10 : ℚ) ^ decimal.exponent * (10 : ℚ) ^ places =
        -((decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
          (10 : ℚ) ^ (-decimal.shift places).toNat) := by
      rw [← scaled]
      ring
    rw [flip]
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, fun tie => ?_⟩
    rw [abs_neg, abs_neg, abs_of_nonneg natural, abs_of_nonneg whole]
    rcases (abs_eq (by norm_num : (0 : ℚ) ≤ 1 / 2)).mp tie with half | half <;> linarith

theorem fixed_nearest (scale : Scale) (decimal : Decimal) (nearest : ℤ)
    (near : Nearest (value decimal * (10 : ℚ) ^ scale.places) nearest) :
    (decimal.fixed scale).val = max scale.low (min scale.high nearest) := by
  rw [Decimal.fixed_clamp, Scale.clamp_value,
    (rounded_nearest decimal scale.places).unique near]

def digit : Char → ℕ
  | '0' => 0
  | '1' => 1
  | '2' => 2
  | '3' => 3
  | '4' => 4
  | '5' => 5
  | '6' => 6
  | '7' => 7
  | '8' => 8
  | '9' => 9
  | _ => 0

def numberOf : List Char → ℕ
  | [] => 0
  | head :: tail => digit head * 10 ^ tail.length + numberOf tail

def exponentOf : Option Acorn.Json.Exponent → ℤ
  | none => 0
  | some ⟨_, some true, digits⟩ => -(numberOf digits : ℤ)
  | some ⟨_, _, digits⟩ => numberOf digits

def written (numeral : Acorn.Json.Numeral) : ℚ :=
  (if numeral.negative then -1 else 1) *
    ((numberOf numeral.whole : ℚ) +
      (numberOf (numeral.fraction.getD []) : ℚ) /
        (10 : ℚ) ^ (numeral.fraction.getD []).length) *
    (10 : ℚ) ^ exponentOf numeral.exponent

theorem digit_code (c : Char) (decimal : Acorn.Json.Numeral.Digit c) :
    c.toNat - 48 = digit c := by
  obtain ⟨low, high⟩ := decimal
  have same : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
  have code : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨ c.toNat = 51 ∨ c.toNat = 52 ∨
      c.toNat = 53 ∨ c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56 ∨ c.toNat = 57 := by omega
  rcases code with at_ | at_ | at_ | at_ | at_ | at_ | at_ | at_ | at_ | at_ <;>
    (rw [same, at_]; rfl)

theorem spelled_numberOf (digits : List Char)
    (decimal : ∀ c ∈ digits, Acorn.Json.Numeral.Digit c) : spelled digits = numberOf digits := by
  induction digits with
  | nil => rfl
  | cons head tail hold =>
    have first := digit_code head (decimal head List.mem_cons_self)
    have rest := hold fun c inside => decimal c (List.mem_cons_of_mem head inside)
    have moved := spelled_from (10 * 0 + (head.toNat - 48)) tail
    unfold spelled at moved ⊢
    rw [List.foldl_cons, moved]
    unfold spelled at rest
    rw [rest, first, Nat.mul_zero, Nat.zero_add]
    rfl

theorem formed_whole {numeral : Acorn.Json.Numeral} (formed : numeral.Formed) :
    ∀ c ∈ numeral.whole, Acorn.Json.Numeral.Digit c := by
  rcases formed.whole with zero | ⟨_, decimal, _⟩
  · intro c inside
    rw [zero, List.mem_singleton] at inside
    rw [inside]
    exact ⟨by decide, by decide⟩
  · exact decimal

theorem formed_fraction {numeral : Acorn.Json.Numeral} (formed : numeral.Formed) :
    ∀ c ∈ numeral.fraction.getD [], Acorn.Json.Numeral.Digit c := by
  cases part : numeral.fraction with
  | none => exact fun _ inside => nomatch inside
  | some digits => exact (formed.fraction digits part).2

theorem power_exponentOf {numeral : Acorn.Json.Numeral} (formed : numeral.Formed) :
    power numeral.exponent = exponentOf numeral.exponent := by
  cases part : numeral.exponent with
  | none => rfl
  | some exponent =>
    obtain ⟨upper, sign, digits⟩ := exponent
    have same := spelled_numberOf digits (formed.exponent _ part).2
    unfold power exponentOf
    rcases sign with _ | _ | _ <;> simp [same]

theorem ofNumeral_value (numeral : Acorn.Json.Numeral) (formed : numeral.Formed) :
    value (Decimal.ofNumeral numeral) = written numeral := by
  have positive : (10 : ℚ) ^ (numeral.fraction.getD []).length ≠ 0 := by positivity
  have whole := spelled_numberOf numeral.whole (formed_whole formed)
  have fraction := spelled_numberOf (numeral.fraction.getD []) (formed_fraction formed)
  unfold value written Decimal.ofNumeral
  simp only [spelled_append]
  rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast, power_exponentOf formed, whole,
    fraction]
  push_cast
  field_simp

theorem read_nearest (scale : Scale) (json : Acorn.Json.Value) (decimal : Decimal)
    (read : Decimal.read json = some decimal) :
    ∃ numeral : Acorn.Json.Numeral, numeral.Formed ∧
      json = .number (String.ofList numeral.chars) ∧
        ∀ nearest : ℤ, Nearest (written numeral * (10 : ℚ) ^ scale.places) nearest →
          (decimal.fixed scale).val = max scale.low (min scale.high nearest) := by
  obtain ⟨numeral, formed, same, rfl⟩ := (Decimal.read_iff json decimal).mp read
  refine ⟨numeral, formed, same, fun nearest near => ?_⟩
  rw [← ofNumeral_value numeral formed] at near
  exact fixed_nearest scale _ nearest near

theorem kept_nearest (scale : Scale) (json : Acorn.Json.Value) (word : scale.Word)
    (kept : scale.Kept json word) :
    ∃ numeral : Acorn.Json.Numeral, numeral.Formed ∧
      json = .number (String.ofList numeral.chars) ∧
        ∃ nearest : ℤ, Nearest (written numeral * (10 : ℚ) ^ scale.places) nearest ∧
          word.val = max scale.low (min scale.high nearest) := by
  obtain ⟨numeral, formed, same, rfl⟩ := kept
  refine ⟨numeral, formed, same, (Decimal.ofNumeral numeral).rounded scale.places, ?_, ?_⟩
  · rw [← ofNumeral_value numeral formed]
    exact rounded_nearest _ _
  · rw [Decimal.fixed_clamp, Scale.clamp_value]

theorem counted_numberOf (json : Acorn.Json.Value) (natural : ℕ)
    (counted : Counted json natural) :
    ∃ digits : List Char, (∀ c ∈ digits, Acorn.Json.Numeral.Digit c) ∧
      json = .number (String.ofList digits) ∧ numberOf digits = natural := by
  obtain ⟨digits, formed, same, rfl⟩ := counted
  exact ⟨digits, formed_whole formed, same,
    (spelled_numberOf digits (formed_whole formed)).symm⟩

theorem signed_numberOf (json : Acorn.Json.Value) (integer : ℤ)
    (signed : Signed json integer) :
    ∃ (negative : Bool) (digits : List Char), (∀ c ∈ digits, Acorn.Json.Numeral.Digit c) ∧
      json =
        .number (String.ofList (⟨negative, digits, none, none⟩ : Acorn.Json.Numeral).chars) ∧
        (if negative then -(numberOf digits : ℤ) else numberOf digits) = integer := by
  obtain ⟨negative, digits, formed, same, rfl⟩ := signed
  refine ⟨negative, digits, formed_whole formed, same, ?_⟩
  rw [spelled_numberOf digits (formed_whole formed)]

theorem spelling_twist (velocity : Velocity) :
    (velocity.spelling.forward.Formed ∧
        written velocity.spelling.forward = (velocity.twist.forward : ℚ) / 1000) ∧
      (velocity.spelling.left.Formed ∧
        written velocity.spelling.left = (velocity.twist.left : ℚ) / 1000) ∧
      (velocity.spelling.turn.Formed ∧
        written velocity.spelling.turn = (velocity.twist.turn : ℚ) / 1000) := by
  have formed : ∀ numeral : Acorn.Json.Numeral,
      Acorn.Json.Numeral.scan numeral.chars = some (numeral, []) → numeral.Formed :=
    fun _ scanned => (Acorn.Json.Numeral.scan_formed scanned).1
  cases velocity <;>
    refine ⟨⟨formed _ (by decide), ?_⟩, ⟨formed _ (by decide), ?_⟩,
      ⟨formed _ (by decide), ?_⟩⟩ <;>
    norm_num [written, numberOf, digit, exponentOf, Velocity.spelling, nought,
      Velocity.twist]

end AcornVerif.Decimal
