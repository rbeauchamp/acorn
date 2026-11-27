import Acorn.Json
import Acorn.Digits
import Acorn.Host.Viewer.WireNumber

namespace Acorn.Host.Viewer.DecimalText

structure Decimal where
  negative : Bool
  mantissa : Nat
  exp10 : Int
  deriving DecidableEq, BEq

inductive Scalar where
  | nonFinite
  | finite (value : Decimal)
  deriving DecidableEq, BEq

private def digitsFold (init : Nat) (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) init

private def digitsValue (cs : List Char) : Nat :=
  digitsFold 0 cs

def Decimal.parse (spelling : String) : Option Decimal := do
  let (numeral, rest) ← Json.Numeral.scan spelling.toList
  guard rest.isEmpty
  let whole := digitsValue numeral.whole
  let (mantissa, fracLen) := match numeral.fraction with
    | none => (whole, 0)
    | some frac => (whole * 10 ^ frac.length + digitsValue frac, frac.length)
  let expVal : Int := match numeral.exponent with
    | none => 0
    | some exp =>
      let mag : Int := digitsValue exp.digits
      if exp.sign == some true then -mag else mag
  let totalExp : Int := expVal - (fracLen : Int)
  return ⟨numeral.negative, mantissa, totalExp⟩

def Scalar.fromJson : Json.Value → Except String Scalar
  | .null => .ok .nonFinite
  | .number spelling =>
    match Decimal.parse spelling with
    | some value => .ok (.finite value)
    | none => .error "invalid decimal number"
  | _ => .error "expected number or null"

def Decimal.isPositive (d : Decimal) : Bool := !d.negative && d.mantissa > 0

def Scalar.isFinite : Scalar → Bool
  | .nonFinite => false
  | .finite _ => true

def maxPositiveScaleShift : Nat := 400

def natDecimalLen (n : Nat) : Nat :=
  if h : n = 0 then 0 else natDecimalLen (n / 10) + 1
termination_by n

def Decimal.roundExact (d : Decimal) (places : Nat) : Int :=
  if d.mantissa == 0 then 0
  else
    let shift : Int := d.exp10 + (places : Int)
    let mag : Nat :=
      if shift ≥ 0 then
        d.mantissa * 10 ^ shift.toNat
      else
        let denom := 10 ^ (-shift).toNat
        (d.mantissa + denom / 2) / denom
    if d.negative then -(mag : Int) else (mag : Int)

def Decimal.scaled? (d : Decimal) (places : Nat) : Option Int :=
  if d.mantissa == 0 then some 0
  else
    let shift : Int := d.exp10 + (places : Int)
    if shift ≥ 0 then
      let p := shift.toNat
      if p ≤ maxPositiveScaleShift then
        let mag := d.mantissa * 10 ^ p
        some (if d.negative then -(mag : Int) else (mag : Int))
      else none
    else
      let p := (-shift).toNat
      let mag :=
        if p > natDecimalLen d.mantissa then 0
        else
          let denom := 10 ^ p
          (d.mantissa + denom / 2) / denom
      some (if d.negative then -(mag : Int) else (mag : Int))

def Scalar.scaled6 : Scalar → Option Int
  | .nonFinite => none
  | .finite d => d.scaled? 6

def formatNatCommas (n : Nat) : String :=
  let digits := (toString n).toList.reverse
  let rec go : List Char → Nat → List Char → List Char
    | [], _, acc => acc
    | c :: rest, count, acc =>
      let acc := if count > 0 && count % 3 == 0 then c :: ',' :: acc else c :: acc
      go rest (count + 1) acc
  String.ofList (go digits 0 [])

def padLeftZero (width : Nat) (s : String) : String :=
  if s.length ≥ width then s else String.ofList (List.replicate (width - s.length) '0') ++ s

def formatScaledFixed (value : Int) (scalePlaces : Nat) (displayPlaces : Nat) : String :=
  let neg := value < 0
  let mag := value.natAbs
  let scaled :=
    if displayPlaces ≥ scalePlaces then
      mag * 10 ^ (displayPlaces - scalePlaces)
    else
      let div := 10 ^ (scalePlaces - displayPlaces)
      (mag + div / 2) / div
  let base := 10 ^ displayPlaces
  let whole := scaled / base
  let frac := scaled % base
  let sign := if neg && scaled > 0 then "-" else ""
  if displayPlaces == 0 then sign ++ formatNatCommas whole
  else sign ++ formatNatCommas whole ++ "." ++ padLeftZero displayPlaces (toString frac)

private def trimTrailingZeros (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '0')).reverse

def Decimal.formatSci (d : Decimal) (sigFigs : Nat := 3) : String :=
  if d.mantissa == 0 then "0"
  else
    let raw := (toString d.mantissa).toList
    let sciExp : Int := d.exp10 + ((raw.length : Int) - 1)
    let keep := max 1 sigFigs
    let (roundedDigits, adjExp) :=
      if raw.length ≤ keep then
        (raw, sciExp)
      else
        let dropCount := raw.length - keep
        let div := 10 ^ dropCount
        let rounded := (d.mantissa + div / 2) / div
        let rList := (toString rounded).toList
        if rList.length > keep then
          (rList.take keep, sciExp + 1)
        else
          (rList, sciExp)
    let sign := if d.negative then "-" else ""
    let lead := roundedDigits.headD '0'
    let tail := trimTrailingZeros (roundedDigits.drop 1)
    let body := if tail.isEmpty then String.singleton lead
      else String.singleton lead ++ "." ++ String.ofList tail
    let expStr := if adjExp < 0 then "-" ++ toString (-adjExp).toNat else toString adjExp.toNat
    sign ++ body ++ "e" ++ expStr

def Decimal.formatCompact (d : Decimal) (fixedPlaces : Nat := 3) : String :=
  if d.mantissa == 0 then "0"
  else
    let raw := (toString d.mantissa).toList
    let sciExp : Int := d.exp10 + ((raw.length : Int) - 1)
    if sciExp < -2 || sciExp ≥ 6 then
      d.formatSci 3
    else
      match d.scaled? fixedPlaces with
      | some v => formatScaledFixed v fixedPlaces fixedPlaces
      | none => d.formatSci 3

def Scalar.formatCompact (s : Scalar) (fixedPlaces : Nat := 3) : String :=
  match s with
  | .nonFinite => "⚠ non-finite"
  | .finite d => d.formatCompact fixedPlaces

def Scalar.formatFixed (s : Scalar) (places : Nat := 3) : String :=
  match s with
  | .nonFinite => "⚠ non-finite"
  | .finite d =>
    match d.scaled? places with
    | some v => formatScaledFixed v places places
    | none => d.formatSci 3

def Decimal.log10Scaled100 (d : Decimal) : Option Int :=
  if d.negative || d.mantissa == 0 then none
  else
    let raw := (toString d.mantissa).toList
    let sciExp : Int := d.exp10 + ((raw.length : Int) - 1)
    let top3 : Nat :=
      if raw.length ≥ 3 then digitsValue (raw.take 3)
      else if raw.length == 2 then digitsValue raw * 10
      else digitsValue raw * 100
    let frac100 : Int :=
      if top3 < 112 then 0 else if top3 < 126 then 5 else if top3 < 141 then 10
      else if top3 < 158 then 15 else if top3 < 178 then 20 else if top3 < 200 then 25
      else if top3 < 224 then 30 else if top3 < 251 then 35 else if top3 < 282 then 40
      else if top3 < 316 then 45 else if top3 < 355 then 50 else if top3 < 398 then 55
      else if top3 < 447 then 60 else if top3 < 501 then 65 else if top3 < 562 then 70
      else if top3 < 631 then 75 else if top3 < 708 then 80 else if top3 < 794 then 85
      else if top3 < 891 then 90 else 95
    some (sciExp * 100 + frac100)

def formatDecimal1 (tenths : Nat) : String :=
  toString (tenths / 10) ++ "." ++ toString (tenths % 10)

def formatPercent1 (num denom : Nat) : String :=
  if denom == 0 then "—"
  else formatDecimal1 (num * 1000 / denom) ++ "%"

def formatDurationMs (ms : Nat) : String :=
  let secs := ms / 1000
  if secs < 60 then s!"{secs}s"
  else if secs < 3600 then s!"{secs / 60}m {secs % 60}s"
  else s!"{secs / 3600}h {(secs % 3600) / 60}m"

def formatBytes (bytes : Nat) : String :=
  if bytes < 1024 then s!"{bytes} B"
  else if bytes < 1024 * 1024 then formatDecimal1 (bytes * 10 / 1024) ++ " KiB"
  else formatDecimal1 (bytes * 10 / (1024 * 1024)) ++ " MiB"

def formatCompactNat (n : Nat) : String :=
  if n < 1000 then toString n
  else if n < 1000000 then formatDecimal1 (n / 100) ++ "k"
  else formatDecimal1 (n / 100000) ++ "M"

def meanPositiveScaled (values : List Scalar) : Option Decimal :=
  let rec go : List Scalar → Int → Nat → Option Decimal
    | [], sum, count =>
      if count == 0 then some ⟨false, 0, 0⟩
      else
        let avg := (sum + (count : Int) / 2) / (count : Int)
        some ⟨avg < 0, avg.natAbs, -9⟩
    | .nonFinite :: _, _, _ => none
    | .finite d :: rest, sum, count =>
      if d.isPositive then
        match d.scaled? 9 with
        | some s => go rest (sum + s) (count + 1)
        | none => none
      else go rest sum count
  go values 0 0

private theorem digitChar_spec (d : Nat) (lt : d < 10) :
    Json.Numeral.Digit (Nat.digitChar d) ∧ (Nat.digitChar d).toNat - 48 = d ∧
      (Nat.digitChar d = '0' ↔ d = 0) := by
  unfold Json.Numeral.Digit
  have h : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem toDigitsCore_digits (fuel n : Nat) (acc : List Char)
    (hacc : ∀ c ∈ acc, Json.Numeral.Digit c) :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n acc, Json.Numeral.Digit c := by
  induction fuel generalizing n acc with
  | zero => exact hacc
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    dsimp only
    have hd : Json.Numeral.Digit (Nat.digitChar (n % 10)) :=
      (digitChar_spec (n % 10) (Nat.mod_lt n (by decide))).1
    split
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | rest
      · exact hd
      · exact hacc c rest
    · exact ih (n / 10) (Nat.digitChar (n % 10) :: acc) fun c hc => by
        rcases List.mem_cons.mp hc with rfl | rest
        · exact hd
        · exact hacc c rest

private theorem toDigitsCore_nonempty (fuel n : Nat) (acc : List Char)
    (hpos : 0 < fuel ∨ acc ≠ []) :
    Nat.toDigitsCore 10 fuel n acc ≠ [] := by
  induction fuel generalizing n acc with
  | zero =>
    rcases hpos with h | h
    · omega
    · simpa [Nat.toDigitsCore] using h
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    dsimp only
    split
    · exact List.cons_ne_nil _ _
    · exact ih (n / 10) (Nat.digitChar (n % 10) :: acc) (.inr (List.cons_ne_nil _ _))

private theorem toDigitsCore_pos_head (fuel n : Nat) (acc : List Char)
    (hpos : 0 < n) (hlt : n < fuel) :
    (Nat.toDigitsCore 10 fuel n acc).head? ≠ some '0' := by
  induction fuel generalizing n acc with
  | zero => omega
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    dsimp only
    split
    · rename_i hdiv
      have hmod : n % 10 ≠ 0 := by omega
      intro heq
      have hc : Nat.digitChar (n % 10) = '0' := Option.some.inj heq
      exact hmod ((digitChar_spec (n % 10) (Nat.mod_lt n (by decide))).2.2.mp hc)
    · rename_i hdiv
      exact ih (n / 10) (Nat.digitChar (n % 10) :: acc) (by omega) (by omega)

private theorem digitsFold_toDigitsCore (fuel n : Nat) (acc : List Char) (hlt : n < fuel) :
    digitsFold 0 (Nat.toDigitsCore 10 fuel n acc) = digitsFold n acc := by
  induction fuel generalizing n acc with
  | zero => omega
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    dsimp only
    split
    · rename_i hdiv
      have hmod : n % 10 = n := by omega
      have hval : (Nat.digitChar (n % 10)).toNat - 48 = n := by
        rw [(digitChar_spec (n % 10) (Nat.mod_lt n (by decide))).2.1, hmod]
      simp [digitsFold, hval]
    · rename_i hdiv
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: acc) (by omega)]
      have hval : (Nat.digitChar (n % 10)).toNat - 48 = n % 10 :=
        (digitChar_spec (n % 10) (Nat.mod_lt n (by decide))).2.1
      simp only [digitsFold, List.foldl_cons, hval]
      have hrec : n / 10 * 10 + n % 10 = n := by omega
      rw [hrec]

private theorem nat_toString_toList (n : Nat) :
    (toString n).toList = Nat.toDigits 10 n := by
  simp [toString, Nat.repr]

private theorem digitsValue_toString (n : Nat) :
    digitsValue (toString n).toList = n := by
  rw [nat_toString_toList]
  exact digitsFold_toDigitsCore (n + 1) n [] (Nat.lt_succ_self n)

private def wireDecimalNumeral (w : WireDecimal) : Json.Numeral where
  negative := w.negative
  whole := (toString w.coefficient).toList
  fraction := none
  exponent := if w.scale = 0 then none
    else some ⟨false, some true, (toString w.scale).toList⟩

private theorem wireDecimalNumeral_formed (w : WireDecimal) :
    (wireDecimalNumeral w).Formed := by
  refine ⟨?_, ?_, ?_⟩
  · show (toString w.coefficient).toList = ['0'] ∨
      ((toString w.coefficient).toList ≠ [] ∧
        (∀ c ∈ (toString w.coefficient).toList, Json.Numeral.Digit c) ∧
        (toString w.coefficient).toList.head? ≠ some '0')
    rw [nat_toString_toList]
    by_cases hz : w.coefficient = 0
    · left
      rw [hz]
      rfl
    · right
      refine ⟨toDigitsCore_nonempty (w.coefficient + 1) w.coefficient [] (.inl (Nat.zero_lt_succ _)),
        toDigitsCore_digits (w.coefficient + 1) w.coefficient [] (fun _ h => nomatch h),
        toDigitsCore_pos_head (w.coefficient + 1) w.coefficient [] (Nat.pos_of_ne_zero hz)
          (Nat.lt_succ_self w.coefficient)⟩
  · intro _ h
    exact nomatch h
  · intro exp h
    dsimp [wireDecimalNumeral] at h
    split at h
    · exact nomatch h
    · cases Option.some.inj h
      rw [nat_toString_toList]
      exact ⟨toDigitsCore_nonempty (w.scale + 1) w.scale [] (.inl (Nat.zero_lt_succ _)),
        toDigitsCore_digits (w.scale + 1) w.scale [] (fun _ hc => nomatch hc)⟩

private theorem wireDecimalNumeral_chars (w : WireDecimal) :
    (wireDecimalNumeral w).chars = w.text.toList := by
  unfold Json.Numeral.chars WireDecimal.text wireDecimalNumeral
  dsimp only
  simp only [Json.Numeral.fractionChars, List.append_nil, String.toList_append]
  have hneg : (if w.negative then ['-'] else []) =
      (if w.negative then "-" else "").toList := by
    cases w.negative <;> rfl
  have hexp : Json.Numeral.exponentChars
      (if w.scale = 0 then none else some ⟨false, some true, (toString w.scale).toList⟩) =
      (if w.scale = 0 then "" else "e-" ++ toString w.scale).toList := by
    by_cases hz : w.scale = 0
    · simp [hz, Json.Numeral.exponentChars]
    · simp [hz, Json.Numeral.exponentChars, Json.Exponent.chars, Json.Exponent.signChars,
        String.toList_append]
  rw [hneg, hexp]

theorem Decimal.parse_wireDecimal (w : WireDecimal) :
    Decimal.parse w.text = some ⟨w.negative, w.coefficient, -(w.scale : Int)⟩ := by
  unfold Decimal.parse
  rw [← wireDecimalNumeral_chars w, Json.Numeral.scan_chars _ (wireDecimalNumeral_formed w)]
  change some (Decimal.mk
    w.negative
    (digitsValue (toString w.coefficient).toList)
    ((match (if w.scale = 0 then none
      else some (Json.Exponent.mk false (some true) (toString w.scale).toList)) with
      | none => (0 : Int)
      | some exp =>
        let mag : Int := digitsValue exp.digits
        if exp.sign == some true then -mag else mag) - (0 : Int))) = _
  rw [digitsValue_toString]
  by_cases hz : w.scale = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, digitsValue_toString, BEq.rfl, Int.sub_zero]

theorem Decimal.parse_wireDyadic (d : WireDyadic) :
    Decimal.parse d.decimal.text =
      some ⟨d.negative, d.decimal.coefficient, -(d.decimal.scale : Int)⟩ := by
  simpa [WireDyadic.decimal_sign] using Decimal.parse_wireDecimal d.decimal

theorem Decimal.parse_wireDyadic_exact (d : WireDyadic) :
    ∃ dec, Decimal.parse d.decimal.text = some dec ∧
      dec.negative = d.negative ∧
      dec.mantissa * d.denominator = d.numerator * 10 ^ (-dec.exp10).toNat := by
  refine ⟨⟨d.negative, d.decimal.coefficient, -(d.decimal.scale : Int)⟩,
    Decimal.parse_wireDyadic d, rfl, ?_⟩
  simpa using WireDyadic.decimal_exact d

theorem Scalar.fromJson_binary32 (b : Binary32) :
    match binary32Dyadic b with
    | none => binary32Text b = "null" ∧ Scalar.fromJson .null = .ok .nonFinite
    | some d =>
      Scalar.fromJson (.number (binary32Text b)) =
        .ok (.finite ⟨d.decimal.negative, d.decimal.coefficient, -(d.decimal.scale : Int)⟩) := by
  unfold binary32Text
  cases hd : binary32Dyadic b with
  | none => exact ⟨rfl, rfl⟩
  | some d =>
    simp only [Scalar.fromJson, Decimal.parse_wireDecimal]

theorem Scalar.fromJson_binary64 (b : Binary64) :
    match binary64Dyadic b with
    | none => binary64Text b = "null" ∧ Scalar.fromJson .null = .ok .nonFinite
    | some d =>
      Scalar.fromJson (.number (binary64Text b)) =
        .ok (.finite ⟨d.decimal.negative, d.decimal.coefficient, -(d.decimal.scale : Int)⟩) := by
  unfold binary64Text
  cases hd : binary64Dyadic b with
  | none => exact ⟨rfl, rfl⟩
  | some d =>
    simp only [Scalar.fromJson, Decimal.parse_wireDecimal]

theorem natDecimalLen_spec (n : Nat) : n < 10 ^ natDecimalLen n := by
  induction n using natDecimalLen.induct with
  | case1 => simp [natDecimalLen]
  | case2 n hne ih =>
    rw [natDecimalLen, dite_eq_right hne, Nat.pow_succ]
    omega

private theorem roundDiv_eq_zero_of_gt_len (m p : Nat) (hgt : natDecimalLen m < p) :
    (m + 10 ^ p / 2) / 10 ^ p = 0 := by
  have hm : m < 10 ^ natDecimalLen m := natDecimalLen_spec m
  have hle : natDecimalLen m ≤ p - 1 := by omega
  have hpowLe : 10 ^ natDecimalLen m ≤ 10 ^ (p - 1) :=
    Nat.pow_le_pow_right (by decide) hle
  have hp : p = (p - 1) + 1 := by omega
  have hpow : 10 ^ p = 10 ^ (p - 1) * 10 := by
    conv => lhs; rw [hp, Nat.pow_succ]
  have hnum : m + 10 ^ p / 2 < 10 ^ p := by omega
  exact Nat.div_eq_of_lt hnum

theorem Decimal.scaled?_iff (d : Decimal) (places : Nat) :
    d.scaled? places =
      if d.mantissa = 0 ∨ d.exp10 + (places : Int) ≤ (maxPositiveScaleShift : Int) then
        some (d.roundExact places)
      else none := by
  unfold Decimal.scaled? Decimal.roundExact
  by_cases hm : d.mantissa = 0
  · simp [hm]
  · have hbeq : (d.mantissa == 0) = false := beq_false_of_ne hm
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, hm, false_or]
    by_cases hnonneg : d.exp10 + (places : Int) ≥ 0
    · simp only [hnonneg, ↓reduceIte]
      by_cases hcap : (d.exp10 + (places : Int)).toNat ≤ maxPositiveScaleShift
      · have hle : d.exp10 + (places : Int) ≤ (maxPositiveScaleShift : Int) := by omega
        simp [hcap, hle]
      · have hgt : ¬ (d.exp10 + (places : Int) ≤ (maxPositiveScaleShift : Int)) := by omega
        simp [hcap, hgt]
    · have hle : d.exp10 + (places : Int) ≤ (maxPositiveScaleShift : Int) := by omega
      simp only [hnonneg, ↓reduceIte, hle]
      by_cases hlen : (-(d.exp10 + (places : Int))).toNat > natDecimalLen d.mantissa
      · simp only [hlen, ↓reduceIte]
        rw [roundDiv_eq_zero_of_gt_len d.mantissa _ hlen]
      · simp [hlen]

theorem Decimal.scaled?_eq_roundExact (d : Decimal) (places : Nat) (result : Int)
    (h : d.scaled? places = some result) : result = d.roundExact places := by
  rw [Decimal.scaled?_iff] at h
  split at h
  · exact (Option.some.inj h).symm
  · exact nomatch h

theorem Decimal.scaled?_of_nonpos_exp (d : Decimal) (places : Nat)
    (hExp : d.exp10 ≤ 0) (hPlaces : places ≤ maxPositiveScaleShift) :
    d.scaled? places = some (d.roundExact places) := by
  rw [Decimal.scaled?_iff]
  have hle : d.exp10 + (places : Int) ≤ (maxPositiveScaleShift : Int) := by omega
  simp [hle]

theorem Decimal.parse_wireDecimal_scaled? (w : WireDecimal) (places : Nat)
    (hPlaces : places ≤ maxPositiveScaleShift) :
    (Decimal.parse w.text).bind (·.scaled? places) =
      some ((Decimal.mk w.negative w.coefficient (-(w.scale : Int))).roundExact places) := by
  rw [Decimal.parse_wireDecimal, Option.bind_some]
  exact Decimal.scaled?_of_nonpos_exp ⟨w.negative, w.coefficient, -(w.scale : Int)⟩ places
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg w.scale)) hPlaces

end Acorn.Host.Viewer.DecimalText
