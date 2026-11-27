import Acorn.Json
import Acorn.Digits

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

private def digitsValue (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

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
  let boundedExp : Int := max (-1000) (min 1000 totalExp)
  return ⟨numeral.negative, mantissa, boundedExp⟩

def Scalar.fromJson : Json.Value → Except String Scalar
  | .null => .ok .nonFinite
  | .number spelling =>
    match Decimal.parse spelling with
    | some value => .ok (.finite value)
    | none => .error "invalid decimal number"
  | _ => .error "expected number or null"

def Decimal.isZero (d : Decimal) : Bool := d.mantissa == 0

def Decimal.isPositive (d : Decimal) : Bool := !d.negative && d.mantissa > 0

def Decimal.isNegative (d : Decimal) : Bool := d.negative && d.mantissa > 0

def Scalar.isFinite : Scalar → Bool
  | .nonFinite => false
  | .finite _ => true

def Scalar.isZero : Scalar → Bool
  | .finite d => d.isZero
  | .nonFinite => false

def Decimal.scaled (d : Decimal) (places : Nat) : Int :=
  if d.mantissa == 0 then 0
  else
    let shift : Int := d.exp10 + (places : Int)
    let mag : Nat :=
      if shift ≥ 0 then
        let p := min shift.toNat 36
        d.mantissa * (10 ^ p)
      else
        let p := min (-shift).toNat 400
        let denom := 10 ^ p
        (d.mantissa + denom / 2) / denom
    if d.negative then -(mag : Int) else (mag : Int)

def Decimal.scaled6 (d : Decimal) : Int := d.scaled 6

def Scalar.scaled6 : Scalar → Option Int
  | .nonFinite => none
  | .finite d => some d.scaled6

def formatNatCommas (n : Nat) : String :=
  let digits := (toString n).toList.reverse
  let rec go : List Char → Nat → List Char → List Char
    | [], _, acc => acc
    | c :: rest, count, acc =>
      let acc := if count > 0 && count % 3 == 0 then c :: ',' :: acc else c :: acc
      go rest (count + 1) acc
  String.ofList (go digits 0 [])

def formatIntCommas (n : Int) : String :=
  if n < 0 then "−" ++ formatNatCommas (-n).toNat else formatNatCommas n.toNat

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
      formatScaledFixed (d.scaled fixedPlaces) fixedPlaces fixedPlaces

def Scalar.formatCompact (s : Scalar) (fixedPlaces : Nat := 3) : String :=
  match s with
  | .nonFinite => "⚠ non-finite"
  | .finite d => d.formatCompact fixedPlaces

def Scalar.formatFixed (s : Scalar) (places : Nat := 3) : String :=
  match s with
  | .nonFinite => "⚠ non-finite"
  | .finite d => formatScaledFixed (d.scaled places) places places

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

def formatStepRange (lo hi : Nat) : String :=
  let a := formatCompactNat lo
  let b := formatCompactNat hi
  if a == b then formatNatCommas lo ++ "–" ++ formatNatCommas hi
  else a ++ "–" ++ b

def trendDirection (newer older : Int) : Int :=
  let absOlder := older.natAbs
  let diff := newer - older
  if absOlder == 0 then
    if newer == older then 0 else if newer > older then 1 else -1
  else if diff.natAbs * 20 < absOlder then 0
  else if diff > 0 then 1 else -1

def meanPositiveScaled (values : List Scalar) : Option Decimal :=
  let rec go : List Scalar → Int → Nat → Option Decimal
    | [], sum, count =>
      if count == 0 then some ⟨false, 0, 0⟩
      else
        let avg := (sum + (count : Int) / 2) / (count : Int)
        some ⟨avg < 0, avg.natAbs, -9⟩
    | .nonFinite :: _, _, _ => none
    | .finite d :: rest, sum, count =>
      if d.isPositive then go rest (sum + d.scaled 9) (count + 1)
      else go rest sum count
  go values 0 0

def meanScalars (values : List Scalar) : Option Decimal :=
  let rec go : List Scalar → Int → Nat → Option Decimal
    | [], sum, count =>
      if count == 0 then none
      else
        let avg := sum / (count : Int)
        some ⟨avg < 0, avg.natAbs, -6⟩
    | .nonFinite :: _, _, _ => none
    | .finite d :: rest, sum, count => go rest (sum + d.scaled 6) (count + 1)
  go values 0 0

end Acorn.Host.Viewer.DecimalText
