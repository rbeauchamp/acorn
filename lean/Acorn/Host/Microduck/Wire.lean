/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Microduck.Sensing

/-!
# The Microduck's JSON text, read into the proved types

The Microduck's daemons send each frame of their two streams as one line of JSON: a
`robot.state` notification for the state of the body and a `tof.frame` notification for
the depth grid. The record of both, with a state frame whose list of body links is
shortened and two depth frames, is at
https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6051119525. This module reads
the `params` object of each, as a value that `Acorn.Json.parse` gave, into a `State` and
a `Depth` of `Acorn.Host.Microduck.Sensing`.

`State.read` and `Depth.read` give a frame or nothing. What each accepts and what it
gives is stated member by member, by `State.Written` and `Depth.Written`: a proposition
for each field, which names the member that the field is read from and relates the two.
A frame is read exactly when it is written so (`State.read_iff`, `Depth.read_iff`, for
every JSON value and every frame). The two specifications name no reader of this module:
the readers are private. Three of the relations, on one number (`Scale.Kept`, `Counted`
and `Signed`), are written with the arithmetic of `Acorn.Host.Microduck.Decimal`, and the
proof library states each without it (`AcornVerif.Decimal.kept_nearest`,
`AcornVerif.Decimal.counted_numberOf`, `AcornVerif.Decimal.signed_numberOf`). The
relations are these.

- `Json.Value.Member` of `Acorn.Json`: the first member of an object with a name. `Within`
  requires the member. `Lacking` is a member of an object that can be missing: there is no
  result when the object has no member with the name or the member is null, and otherwise
  the member is read. A value that is no object lacks nothing: `Lacking` does not hold of
  it.
- `Scale.Kept`: the word that a scale keeps of a JSON number, by the conversion of
  `Acorn.Host.Microduck.Decimal`. It is the integer nearest to the number as the text
  writes it, in the units of the scale, saturated (`AcornVerif.Decimal.kept_nearest`).
- `Counted`: the natural number of a JSON number that digits alone spell, with no sign,
  point or exponent, so `1.0` and `1e3` are not counted. The stamps, the statuses, the gain,
  the distance of a depth zone with a valid return (`Ranged`, at most 32,767) and the stated
  numbers of rows and columns are read so
  (`AcornVerif.Decimal.counted_numberOf` states the number by the places of its digits).
  It is read from the numeral of the one scanner of `Acorn.Json` and not by
  `Acorn.Json.Value.natural`, which no theorem states the accepted spellings of and which
  refuses a number of two to the sixty-four or more.
- `Signed`: the integer of a JSON number that digits with an optional minus sign spell,
  with no point or exponent (`AcornVerif.Decimal.signed_numberOf` states the integer by
  the places of its digits and its sign). The distance of a depth zone with no valid
  return must be one from -32,768 to 32,767.
- `Zoned`: the distance of a depth zone, by its status (`Depth.read_distances`).
- `Listed`: an array whose values correspond to the entries of a vector one to one, in
  order (`Each`), so an array of another length is no vector (`Each.length`). `Texts` is
  an array of strings with the texts of a list, in order.
- `Driven`: a string, and the policy that the table of labels gives it
  (`Policy.Labelled`; `Policy.named_iff` states that the function of names is that table).
  A string outside the ten labels is `Policy.other`, and a value that is no string is
  refused.
- `Limited`: the list of names in `limited_by`, which can be missing, and the limits that
  those names state (`Limits.Named`, with `Limits.named_iff`).

**What a state frame is read from.** The stamp from `t_ns`; the joint angles from
`joints`, fifteen numbers; the joint rates from `velocities`, fifteen numbers or missing;
the gravity direction from `safety.gravity` and the turning rates from `imu.gyro`, three
numbers each; the height from the third number of `odom.position`; the policy from
`policy`; the two reports from `safety.fallen` and `safety.limp`; the gain from
`safety.gain`, a natural number below 65,536 or missing; the limits from
`move.limited_by`. Every member except the three that can be missing is required, and
`move` must be an object: a frame whose `move` is null or a number is refused, and one
whose `move` is an object with no list has no limit.

**What a depth frame is read from.** `rows` and `cols` must both be the number 8, since
the reader lays the sixty-four zones out row by row in eight columns and a frame of
another shape would be laid out wrongly. The stamp from `t_ns`; the statuses from
`status`, sixty-four natural numbers below 256; the distances from `distance_mm`,
sixty-four integers, each read by the status of its zone. With the status 5, a valid
return, the distance is a whole number of millimetres from 0 to 32,767. With another
status the value is an integer from -32,768 to 32,767, and the zone keeps the distance 0.

**Which numbers are converted and which are read exactly.** The daemon writes a real
quantity as a decimal fraction: the joint angles and rates, the gravity direction, the
turning rates and the position of the odometry. For these, and for these only, the
rounding and the saturation of the thousandths scale are the declared rule
(`Scale.Kept`). Every quantity that the daemon writes as an integer is read exactly, by
`Counted` or `Signed`, and a frame with another spelling there is refused and not
repaired: the two stamps, the gain, the stated rows and columns, the statuses and the
distances. The record gives a distance as a signed sixteen-bit integer. The distance of a
zone with the status 5 is a number of at most 32,767 that digits alone spell, so a frame
with such a zone at `-1` is refused whole. The distance of a zone without a valid return
is not kept, because no consumer reads it (`Acorn.Handcrafted.Microduck.symbol`, `near`
and `clear` read a distance only with the status 5): it must be an integer of the
record's type, and the zone keeps 0. A frame with a distance of `65536`, of `2.5` or of
`1e3` is refused whole whatever the status of its zone (`Depth.read_distances`). The two
reports of a state frame are booleans and its policy is a string, and neither is a
number.

**Decisions and their limits.**

- A missing member and a null member are both read as nothing measured. The record says
  that the daemon leaves `limited_by` out when it is empty and that the gain is a number
  or null; for the joint rates it says only that they can be absent, and not which of the
  two the daemon writes.
- A frame is refused whole: one member that is not read gives no frame, and the result
  carries no reason. What a host does at a refused frame is not decided here.
- A member that neither reader names is not read, so its value does not matter. Two
  readings are made and not kept: the stated rows and columns of a depth frame, which
  must be 8, and the first two numbers of `odom.position`, which must be numbers.
- The names of the members, the order of each array and the labels are those of the
  record, from one observed run of the vendor's simulator. The limit name `not_finite`,
  a missing rate and a null gain are from the vendor's source: the record reports the
  rates in every frame and the gains 160 and 200, and no frame without either. No theorem
  relates this module to what a daemon sends: that a robot's daemon writes these names is
  checked only by reading its frames.

Not built: the envelope of a notification (its method and its `params`), the reply to a
request, and the text of a command. `Acorn.Json.parse` reads the line, and no theorem
here is about that parser.

The lookup of a member searches the members of the object in order, and the reader of a
state frame searches `safety` four times. The cost of reading a frame is not otherwise
stated.
-/
namespace Acorn.Host.Microduck

/-! ## The parts of a frame -/

/-- The word of a scale that a JSON number is kept as: the conversion of its decimal. -/
private def Scale.read (scale : Scale) (json : Json.Value) : Option scale.Word :=
  (Decimal.read json).map (·.fixed scale)

/-- A value is read as a word exactly when the word is what the scale keeps of it. -/
private theorem Scale.read_iff (scale : Scale) (json : Json.Value) (word : scale.Word) :
    scale.read json = some word ↔ scale.Kept json word := by
  unfold Scale.read Scale.Kept
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨decimal, read, rfl⟩
    obtain ⟨numeral, formed, same, rfl⟩ := (Decimal.read_iff json decimal).mp read
    exact ⟨numeral, formed, same, rfl⟩
  · rintro ⟨numeral, formed, same, rfl⟩
    exact ⟨_, (Decimal.read_iff json _).mpr ⟨numeral, formed, same, rfl⟩, rfl⟩

/-- The natural number of a JSON value: for a number whose numeral has no minus sign, no
point and no exponent part, the number that its digits spell. It reads the spelling and
rounds nothing, so `1.0` and `1e3` have no natural number. -/
private def count (json : Json.Value) : Option Nat :=
  match json.numeral with
  | some ⟨false, whole, none, none⟩ => some (spelled whole)
  | _ => none

/-- A value has a natural number exactly when digits alone spell it. -/
private theorem count_iff (json : Json.Value) (natural : Nat) :
    count json = some natural ↔ Counted json natural := by
  have plain : ∀ digits : List Char,
      (⟨false, digits, none, none⟩ : Json.Numeral).chars = digits := fun digits => by
    simp [Json.Numeral.chars, Json.Numeral.fractionChars, Json.Numeral.exponentChars]
  unfold count Counted
  constructor
  · intro found
    cases scanned : json.numeral with
    | none =>
      rw [scanned] at found
      exact nomatch found
    | some numeral =>
      rw [scanned] at found
      obtain ⟨negative, whole, fraction, exponent⟩ := numeral
      cases negative <;> cases fraction <;> cases exponent <;>
        first
        | (simp at found; done)
        | (obtain ⟨formed, same⟩ := (Json.Value.numeral_iff json _).mp scanned
           rw [plain] at same
           exact ⟨whole, formed, same, Option.some.inj found⟩)
  · rintro ⟨digits, formed, same, rfl⟩
    rw [(Json.Value.numeral_iff json ⟨false, digits, none, none⟩).mpr
      ⟨formed, by rw [plain]; exact same⟩]

/-- Every value of a list read, in order, or nothing when one is not read. -/
private def collect {α : Type} (read : Json.Value → Option α) : List Json.Value → Option (List α)
  | [] => some []
  | head :: tail => (read head).bind fun first => (collect read tail).map (first :: ·)

/-- The values and the results correspond one to one, in order, and the relation holds of
each value with its result. -/
inductive Each {α : Type} (Read : Json.Value → α → Prop) : List Json.Value → List α → Prop where
  /-- No value and no result. -/
  | nil : Each Read [] []
  /-- One more value with its result, before the others. -/
  | cons {value : Json.Value} {result : α} {values : List Json.Value} {results : List α}
      (first : Read value result) (rest : Each Read values results) :
      Each Read (value :: values) (result :: results)

/-- Values and results that correspond are as many. -/
theorem Each.length {α : Type} {Read : Json.Value → α → Prop} {values : List Json.Value}
    {results : List α} (each : Each Read values results) : values.length = results.length := by
  induction each with
  | nil => rfl
  | cons _ _ hold => rw [List.length_cons, List.length_cons, hold]

/-- Where values and results correspond, the relation holds of each value with the result
in its place. -/
theorem Each.zip {α : Type} {Read : Json.Value → α → Prop} {values : List Json.Value}
    {results : List α} (each : Each Read values results) :
    ∀ pair ∈ values.zip results, Read pair.1 pair.2 := by
  induction each with
  | nil => exact fun _ inside => nomatch inside
  | cons first _ hold =>
    intro pair inside
    rcases List.mem_cons.mp inside with rfl | later
    · exact first
    · exact hold pair later

/-- A list is read exactly when its values and the results correspond one to one, in
order. For every reader and the relation it decides. -/
private theorem collect_iff {α : Type} {read : Json.Value → Option α}
    {Read : Json.Value → α → Prop}
    (each : ∀ value result, read value = some result ↔ Read value result)
    (values : List Json.Value) (results : List α) :
    collect read values = some results ↔ Each Read values results := by
  induction values generalizing results with
  | nil =>
    constructor
    · intro found
      cases Option.some.inj found
      exact .nil
    · intro related
      cases related
      rfl
  | cons head tail hold =>
    unfold collect
    rw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨first, one, more⟩
      obtain ⟨others, rest, rfl⟩ := Option.map_eq_some_iff.mp more
      exact .cons ((each head first).mp one) ((hold others).mp rest)
    · intro related
      cases related with
      | cons one rest =>
        exact ⟨_, (each head _).mpr one, Option.map_eq_some_iff.mpr ⟨_, (hold _).mpr rest, rfl⟩⟩

/-- An array of exactly `size` values, each read. Nothing for an array of another length,
for an array with a value that is not read and for a value that is no array. -/
private def vector {α : Type} (size : Nat) (read : Json.Value → Option α) :
    Json.Value → Option (Vector α size)
  | .array values =>
    (collect read values).bind fun results =>
      if exact : results.length = size then some ⟨results.toArray, exact⟩ else none
  | _ => none

/-- The value is an array whose values correspond to the entries of the vector one to one,
in order. So the array has the length of the vector. -/
def Listed {α : Type} {size : Nat} (Read : Json.Value → α → Prop) (json : Json.Value)
    (results : Vector α size) : Prop :=
  ∃ values : List Json.Value, json = .array values ∧ Each Read values results.toList

/-- An array is read as a vector exactly when its values correspond to the entries one to
one. For every size, reader and the relation it decides. -/
private theorem vector_iff {α : Type} {size : Nat} {read : Json.Value → Option α}
    {Read : Json.Value → α → Prop}
    (each : ∀ value result, read value = some result ↔ Read value result)
    (json : Json.Value) (results : Vector α size) :
    vector size read json = some results ↔ Listed Read json results := by
  unfold Listed
  cases json with
  | array values =>
    unfold vector
    rw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨items, collected, sized⟩
      split at sized
      · cases Option.some.inj sized
        exact ⟨values, rfl, (collect_iff each values items).mp collected⟩
      · exact nomatch sized
    · rintro ⟨_, same, related⟩
      cases same
      refine ⟨results.toList, (collect_iff each values _).mpr related, ?_⟩
      simp [Vector.toList]
  | null | bool _ | number _ | string _ | object _ =>
    exact ⟨fun found => (nomatch found), fun ⟨_, same, _⟩ => (nomatch same)⟩

/-- The value that a reader gives for the member of an object with a name. Nothing for an
object with no such member. -/
private def within {α : Type} (name : String) (read : Json.Value → Option α) (json : Json.Value) :
    Option α :=
  (json.member name).bind read

/-- The object has a member with the name, and the relation holds of the first one. -/
def Within {α : Type} (name : String) (Read : Json.Value → α → Prop) (json : Json.Value)
    (result : α) : Prop :=
  ∃ inner : Json.Value, Json.Value.Member name json inner ∧ Read inner result

/-- A member is read exactly when the object has it and the relation holds of it. -/
private theorem within_iff {α : Type} {read : Json.Value → Option α} {Read : Json.Value → α → Prop}
    (each : ∀ value result, read value = some result ↔ Read value result) (name : String)
    (json : Json.Value) (result : α) :
    within name read json = some result ↔ Within name Read json result := by
  unfold within Within
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨inner, found, read⟩
    exact ⟨inner, (Json.Value.member_iff name json inner).mp found, (each inner result).mp read⟩
  · rintro ⟨inner, found, read⟩
    exact ⟨inner, (Json.Value.member_iff name json inner).mpr found, (each inner result).mpr read⟩

/-- What a reader gives for a member that was looked up: no value for no member and for
null, and otherwise what the reader gives for the member. -/
private def found {α : Type} (read : Json.Value → Option α) :
    Option Json.Value → Option (Option α)
  | none => some none
  | some .null => some none
  | some inner => (read inner).map some

/-- The value that a reader gives for a member of an object that can be missing: no value
when the object has no member with the name or the member is null, and otherwise what the
reader gives for the member. Nothing when the reader refuses a member that is not null,
and for a value that is no object. -/
private def lacking {α : Type} (name : String) (read : Json.Value → Option α) :
    Json.Value → Option (Option α)
  | .object fields => found read ((Json.Value.object fields).member name)
  | _ => none

/-- The value is an object. Either there is no result, and the object has no member with
the name except null; or there is a result, and the relation holds of it and of the first
member with the name, which is not null. -/
def Lacking {α : Type} (name : String) (Read : Json.Value → α → Prop) (json : Json.Value)
    (result : Option α) : Prop :=
  (result = none ∧ (∃ fields, json = .object fields) ∧
      ∀ inner, Json.Value.Member name json inner → inner = .null) ∨
    ∃ inner value, Json.Value.Member name json inner ∧ inner ≠ .null ∧ Read inner value ∧
      result = some value

/-- A member that can be missing is read exactly as the relation of the missing member
says. For every name, reader and the relation it decides. -/
private theorem lacking_iff {α : Type} {read : Json.Value → Option α} {Read : Json.Value → α → Prop}
    (each : ∀ value result, read value = some result ↔ Read value result) (name : String)
    (json : Json.Value) (result : Option α) :
    lacking name read json = some result ↔ Lacking name Read json result := by
  have single : ∀ first second : Json.Value, json.member name = some first →
      Json.Value.Member name json second → second = first := fun first second found other =>
    Option.some.inj (((Json.Value.member_iff name json second).mpr other).symm.trans found)
  unfold Lacking
  cases json with
  | object fields =>
    show found read ((Json.Value.object fields).member name) = some result ↔ _
    cases looked : (Json.Value.object fields).member name with
    | none =>
      constructor
      · intro same
        refine .inl ⟨(Option.some.inj same).symm, ⟨fields, rfl⟩, fun inner member => ?_⟩
        rw [(Json.Value.member_iff name _ inner).mpr member] at looked
        exact nomatch looked
      · rintro (⟨rfl, _⟩ | ⟨inner, _, member, _⟩)
        · rfl
        · rw [(Json.Value.member_iff name _ inner).mpr member] at looked
          exact nomatch looked
    | some first =>
      have member := (Json.Value.member_iff name _ first).mp looked
      by_cases empty : first = .null
      · subst empty
        constructor
        · intro same
          exact .inl ⟨(Option.some.inj same).symm, ⟨fields, rfl⟩,
            fun inner other => single _ inner looked other⟩
        · rintro (⟨rfl, _⟩ | ⟨inner, _, other, filled, _⟩)
          · rfl
          · exact absurd (single _ inner looked other) filled
      · have filled : found read (some first) = (read first).map some := by
          cases first <;> first | rfl | exact absurd rfl empty
        rw [filled, Option.map_eq_some_iff]
        constructor
        · rintro ⟨value, one, rfl⟩
          exact .inr ⟨first, value, member, empty, (each first value).mp one, rfl⟩
        · rintro (⟨_, _, absent⟩ | ⟨inner, value, other, _, one, rfl⟩)
          · exact absurd (absent first member) empty
          · cases single _ inner looked other
            exact ⟨value, (each first value).mpr one, rfl⟩
  | null | bool _ | number _ | string _ | array _ =>
    constructor
    · intro wrong
      exact nomatch wrong
    · rintro (⟨_, ⟨_, wrong⟩, _⟩ | ⟨_, _, ⟨_, _, wrong, _⟩, _⟩) <;> exact nomatch wrong

/-- The stamp of a JSON value: its natural number, as nanoseconds. -/
private def stamp (json : Json.Value) : Option Stamp :=
  (count json).map Stamp.mk

/-- A value is read as a stamp exactly when digits alone spell its nanoseconds. -/
private theorem stamp_iff (json : Json.Value) (taken : Stamp) :
    stamp json = some taken ↔ Counted json taken.nanoseconds := by
  unfold stamp
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨natural, counted, rfl⟩
    exact (count_iff json natural).mp counted
  · intro counted
    exact ⟨taken.nanoseconds, (count_iff json _).mpr counted, rfl⟩

/-- The byte of a JSON value: its natural number, when that is below 256. -/
private def byte (json : Json.Value) : Option UInt8 :=
  (count json).bind fun natural => if natural < 256 then some natural.toUInt8 else none

/-- A value is read as a byte exactly when digits alone spell the number of the byte. So a
number of 256 or more is no byte. -/
private theorem byte_iff (json : Json.Value) (result : UInt8) :
    byte json = some result ↔ Counted json result.toNat := by
  unfold byte
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨natural, counted, sized⟩
    split at sized
    · rename_i small
      cases Option.some.inj sized
      have same : natural.toUInt8.toNat = natural := by
        rw [Nat.toUInt8_eq, UInt8.toNat_ofNat']
        exact Nat.mod_eq_of_lt small
      rw [same]
      exact (count_iff json natural).mp counted
    · exact nomatch sized
  · intro counted
    refine ⟨result.toNat, (count_iff json _).mpr counted, ?_⟩
    simp only [result.toNat_lt, ↓reduceIte]
    exact congrArg some (UInt8.ofNat_toNat)

/-- The sixteen-bit register of a JSON value: its natural number, when that is below
65,536. -/
private def register (json : Json.Value) : Option UInt16 :=
  (count json).bind fun natural => if natural < 65536 then some natural.toUInt16 else none

/-- A value is read as a register exactly when digits alone spell the number of the
register. So a number of 65,536 or more is no register. -/
private theorem register_iff (json : Json.Value) (result : UInt16) :
    register json = some result ↔ Counted json result.toNat := by
  unfold register
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨natural, counted, sized⟩
    split at sized
    · rename_i small
      cases Option.some.inj sized
      have same : natural.toUInt16.toNat = natural := by
        rw [Nat.toUInt16_eq, UInt16.toNat_ofNat']
        exact Nat.mod_eq_of_lt small
      rw [same]
      exact (count_iff json natural).mp counted
    · exact nomatch sized
  · intro counted
    refine ⟨result.toNat, (count_iff json _).mpr counted, ?_⟩
    simp only [result.toNat_lt, ↓reduceIte]
    exact congrArg some (UInt16.ofNat_toNat)

/-- The distance of a JSON value: its natural number, when that is at most 32,767. The
result is the bounded integer itself. Nothing is rounded and nothing is saturated: a
number with a sign, a point or an exponent has no distance, and a larger number has
none. -/
private def distance (json : Json.Value) : Option Declared.range.Word :=
  (count json).bind fun natural =>
    if inside : natural ≤ 32767 then
      some ⟨natural, Int.natCast_nonneg natural, Int.ofNat_le.mpr inside⟩
    else none

/-- The value is a number that digits alone spell, and the digits spell the distance: a
whole number of millimetres from 0 to 32,767, with no sign, no point and no exponent. -/
def Ranged (json : Json.Value) (distance : Declared.range.Word) : Prop :=
  ∃ natural : Nat, Counted json natural ∧ (natural : Int) = distance.val

/-- A value is read as a distance exactly when digits alone spell the distance. So a
negative number, a fraction and a number above 32,767 are no distance. -/
private theorem distance_iff (json : Json.Value) (result : Declared.range.Word) :
    distance json = some result ↔ Ranged json result := by
  unfold distance Ranged
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨natural, counted, sized⟩
    split at sized
    · cases Option.some.inj sized
      exact ⟨natural, (count_iff json natural).mp counted, rfl⟩
    · exact nomatch sized
  · rintro ⟨natural, counted, same⟩
    have inside : natural ≤ 32767 := Int.ofNat_le.mp (same ▸ result.property.2)
    refine ⟨natural, (count_iff json natural).mpr counted, ?_⟩
    simp only [inside, ↓reduceDIte]
    exact congrArg some (Subtype.ext same)

/-- The integer of a JSON value: for a number whose numeral has no point and no exponent
part, the number that its digits spell, negated when the numeral has a minus sign. It
reads the spelling and rounds nothing. -/
private def integer (json : Json.Value) : Option Int :=
  match json.numeral with
  | some ⟨negative, whole, none, none⟩ =>
    some (if negative then -(spelled whole : Int) else spelled whole)
  | _ => none

/-- A value has an integer exactly when digits with an optional minus sign spell it. -/
private theorem integer_iff (json : Json.Value) (result : Int) :
    integer json = some result ↔ Signed json result := by
  unfold integer Signed
  constructor
  · intro found
    cases scanned : json.numeral with
    | none =>
      rw [scanned] at found
      exact nomatch found
    | some numeral =>
      rw [scanned] at found
      obtain ⟨negative, whole, fraction, exponent⟩ := numeral
      cases fraction <;> cases exponent <;>
        first
        | (simp at found; done)
        | (obtain ⟨formed, same⟩ := (Json.Value.numeral_iff json _).mp scanned
           exact ⟨negative, whole, formed, same, Option.some.inj found⟩)
  · rintro ⟨negative, digits, formed, same, rfl⟩
    rw [(Json.Value.numeral_iff json ⟨negative, digits, none, none⟩).mpr ⟨formed, same⟩]

/-- The truth value of a JSON value that is `true` or `false`. -/
private def flag : Json.Value → Option Bool
  | .bool value => some value
  | _ => none

/-- A value is read as a truth value exactly when it is that boolean. -/
private theorem flag_iff (json : Json.Value) (value : Bool) :
    flag json = some value ↔ json = .bool value := by
  cases json <;> simp [flag]

/-- The text of a JSON value that is a string. -/
private def text : Json.Value → Option String
  | .string value => some value
  | _ => none

/-- A value is read as a text exactly when it is that string. -/
private theorem text_iff (json : Json.Value) (value : String) :
    text json = some value ↔ json = .string value := by
  cases json <;> simp [text]

/-- The texts of an array of strings, in order. -/
private def texts : Json.Value → Option (List String)
  | .array values => collect text values
  | _ => none

/-- The value is an array of strings, and the texts are those strings in order. -/
def Texts (json : Json.Value) (names : List String) : Prop :=
  ∃ values : List Json.Value, json = .array values ∧
    Each (fun value name => value = .string name) values names

/-- A value is read as texts exactly when it is the array of those strings. -/
private theorem texts_iff (json : Json.Value) (names : List String) :
    texts json = some names ↔ Texts json names := by
  unfold Texts
  cases json with
  | array values =>
    unfold texts
    rw [collect_iff text_iff]
    exact ⟨fun related => ⟨values, rfl, related⟩, fun ⟨_, same, related⟩ => by
      cases same
      exact related⟩
  | null | bool _ | number _ | string _ | object _ =>
    exact ⟨fun found => (nomatch found), fun ⟨_, same, _⟩ => (nomatch same)⟩

/-! ## The two tables of a state frame -/

/-- The policy that a label names: one of the ten of the table, and `Policy.other` for
every other text. -/
def Policy.named : String → Policy
  | "stand" => .stand
  | "walk" => .walk
  | "held" => .held
  | "homing" => .homing
  | "sit" => .sit
  | "rise" => .rise
  | "kick_left" => .kickLeft
  | "kick_right" => .kickRight
  | "ground_pick" => .groundPick
  | "roulade" => .roulade
  | _ => .other

/-- The table of labels: the text is the label of the policy, or the policy is
`Policy.other` and the text is none of the ten labels. -/
inductive Policy.Labelled : String → Policy → Prop where
  /-- `stand` labels the standing network. -/
  | stand : Policy.Labelled "stand" .stand
  /-- `walk` labels the walking network. -/
  | walk : Policy.Labelled "walk" .walk
  /-- `held` labels a disabled policy. -/
  | held : Policy.Labelled "held" .held
  /-- `homing` labels the ramp to the home pose. -/
  | homing : Policy.Labelled "homing" .homing
  /-- `sit` labels sitting. -/
  | sit : Policy.Labelled "sit" .sit
  /-- `rise` labels standing up. -/
  | rise : Policy.Labelled "rise" .rise
  /-- `kick_left` labels the kick with the left foot. -/
  | kickLeft : Policy.Labelled "kick_left" .kickLeft
  /-- `kick_right` labels the kick with the right foot. -/
  | kickRight : Policy.Labelled "kick_right" .kickRight
  /-- `ground_pick` labels the pick from the ground. -/
  | groundPick : Policy.Labelled "ground_pick" .groundPick
  /-- `roulade` labels the forward roll. -/
  | roulade : Policy.Labelled "roulade" .roulade
  /-- Every other text labels `Policy.other`. -/
  | other (label : String)
      (unknown : label ∉ ["stand", "walk", "held", "homing", "sit", "rise", "kick_left",
        "kick_right", "ground_pick", "roulade"]) : Policy.Labelled label .other

/-- **The function of names is the table of labels.** For every text and policy: the
function gives the policy for the text exactly when the table has the pair. -/
theorem Policy.named_iff (label : String) (policy : Policy) :
    Policy.named label = policy ↔ Policy.Labelled label policy := by
  constructor
  · rintro rfl
    unfold Policy.named
    split
    all_goals first
      | exact .stand
      | exact .walk
      | exact .held
      | exact .homing
      | exact .sit
      | exact .rise
      | exact .kickLeft
      | exact .kickRight
      | exact .groundPick
      | exact .roulade
      | exact .other _ (by simp_all)
  · intro labelled
    cases labelled with
    | other label unknown =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unknown
      unfold Policy.named
      split <;> first | rfl | simp_all
    | _ => rfl

/-- What limited the daemon's commands, from the names of a state frame's list. -/
def Limits.named (names : List String) : Limits :=
  ⟨names.contains "deadman", names.contains "joint_range", names.contains "not_finite",
    names.any fun name => name != "deadman" && name != "joint_range" && name != "not_finite"⟩

/-- Each of the three fields with a name is true exactly when the list has the name, and
the fourth exactly when the list has a name outside the three. -/
def Limits.Named (names : List String) (limits : Limits) : Prop :=
  (limits.deadman = true ↔ "deadman" ∈ names) ∧
    (limits.range = true ↔ "joint_range" ∈ names) ∧
      (limits.finite = true ↔ "not_finite" ∈ names) ∧
        (limits.other = true ↔
          ∃ name ∈ names, name ≠ "deadman" ∧ name ≠ "joint_range" ∧ name ≠ "not_finite")

/-- **The limits of a list of names are the ones the names state.** For every list and
limits. -/
theorem Limits.named_iff (names : List String) (limits : Limits) :
    Limits.named names = limits ↔ Limits.Named names limits := by
  unfold Limits.Named
  constructor
  · rintro rfl
    simp [Limits.named, and_assoc]
  · rintro ⟨deadman, range, finite, other⟩
    obtain ⟨first, second, third, fourth⟩ := limits
    simp only [Limits.named, Limits.mk.injEq]
    refine ⟨Bool.eq_iff_iff.mpr ?_, Bool.eq_iff_iff.mpr ?_, Bool.eq_iff_iff.mpr ?_,
      Bool.eq_iff_iff.mpr ?_⟩
    · rw [deadman]; simp
    · rw [range]; simp
    · rw [finite]; simp
    · rw [other]; simp [and_assoc]

/-- The policy of a JSON value: the policy that its text names. -/
private def Policy.read (json : Json.Value) : Option Policy :=
  (text json).map Policy.named

/-- The value is a string, and the policy is the one the table of labels gives for it. -/
def Driven (json : Json.Value) (policy : Policy) : Prop :=
  ∃ label : String, json = .string label ∧ Policy.Labelled label policy

/-- A value is read as a policy exactly when it is a string that the policy is labelled
with. -/
private theorem Policy.read_iff (json : Json.Value) (result : Policy) :
    Policy.read json = some result ↔ Driven json result := by
  unfold Policy.read Driven
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨label, read, named⟩
    exact ⟨label, (text_iff json label).mp read, (Policy.named_iff label result).mp named⟩
  · rintro ⟨label, same, labelled⟩
    exact ⟨label, (text_iff json label).mpr same, (Policy.named_iff label result).mpr labelled⟩

/-- The limits of the object that holds a state frame's velocity command: the limits that
the names of its list state, and no limit when the list is missing. -/
private def Limits.read (json : Json.Value) : Option Limits :=
  (lacking "limited_by" texts json).map fun names => Limits.named (names.getD [])

/-- The value is an object that has a list of names or lacks one, and the limits are the
ones that those names state, or that no name states. -/
def Limited (json : Json.Value) (limits : Limits) : Prop :=
  ∃ names : Option (List String), Lacking "limited_by" Texts json names ∧
    Limits.Named (names.getD []) limits

/-- A value is read as limits exactly when they are the ones its list of names states. -/
private theorem Limits.read_iff (json : Json.Value) (result : Limits) :
    Limits.read json = some result ↔ Limited json result := by
  unfold Limits.read Limited
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨names, read, named⟩
    exact ⟨names, (lacking_iff texts_iff _ json names).mp read,
      (Limits.named_iff _ result).mp named⟩
  · rintro ⟨names, lacks, named⟩
    exact ⟨names, (lacking_iff texts_iff _ json names).mpr lacks,
      (Limits.named_iff _ result).mpr named⟩

/-! ## A state frame -/

/-- The state frame that the parameters of a `robot.state` notification hold. Nothing
when a required member is missing, and when a member that the reader names is there and
is not read. The joint rates, the gain and the list of limit names can be missing. -/
def State.read (json : Json.Value) : Option State :=
  (within "t_ns" stamp json).bind fun taken =>
  (within "joints" (vector 15 Declared.milli.read) json).bind fun joints =>
  (lacking "velocities" (vector 15 Declared.milli.read) json).bind fun speeds =>
  (within "safety" (within "gravity" (vector 3 Declared.milli.read)) json).bind fun gravity =>
  (within "imu" (within "gyro" (vector 3 Declared.milli.read)) json).bind fun gyro =>
  (within "odom" (within "position" (vector 3 Declared.milli.read)) json).bind fun position =>
  (within "policy" Policy.read json).bind fun driven =>
  (within "safety" (within "fallen" flag) json).bind fun fallen =>
  (within "safety" (within "limp" flag) json).bind fun limp =>
  (within "safety" (lacking "gain" register) json).bind fun gain =>
  (within "move" Limits.read json).map fun limited =>
    ⟨taken, joints, speeds, gravity, gyro, position[2], driven, fallen, limp, gain, limited⟩

/-- What a state frame keeps of the parameters of a `robot.state` notification, member by
member. It names the member that each field is read from, and no reader of this module.
`Counted` and `Scale.Kept` are written with the arithmetic of the decimal module. -/
structure State.Written (json : Json.Value) (state : State) : Prop where
  /-- The stamp is the natural number of `t_ns`. -/
  taken : Within "t_ns" (fun inner (taken : Stamp) => Counted inner taken.nanoseconds) json
    state.taken
  /-- The joint angles are the fifteen numbers of `joints`, in thousandths. -/
  joints : Within "joints" (Listed Declared.milli.Kept) json state.joints
  /-- The joint rates are the fifteen numbers of `velocities`, in thousandths, and absent
  when that member is missing or null. -/
  speeds : Lacking "velocities" (Listed Declared.milli.Kept) json state.speeds
  /-- The gravity direction is the three numbers of `safety.gravity`, in thousandths. -/
  gravity : Within "safety" (Within "gravity" (Listed Declared.milli.Kept)) json state.gravity
  /-- The turning rates are the three numbers of `imu.gyro`, in thousandths. -/
  gyro : Within "imu" (Within "gyro" (Listed Declared.milli.Kept)) json state.gyro
  /-- The height is the third of the three numbers of `odom.position`, in thousandths. -/
  height : ∃ position : Vector Declared.milli.Word 3,
    Within "odom" (Within "position" (Listed Declared.milli.Kept)) json position ∧
      position[2] = state.height
  /-- The policy is the one that the string of `policy` labels. -/
  policy : Within "policy" Driven json state.policy
  /-- The fall report is the boolean of `safety.fallen`. -/
  fallen : Within "safety" (Within "fallen" fun inner value => inner = .bool value) json
    state.fallen
  /-- The limp report is the boolean of `safety.limp`. -/
  limp : Within "safety" (Within "limp" fun inner value => inner = .bool value) json state.limp
  /-- The gain is the natural number of `safety.gain`, below 65,536, and absent when that
  member is missing or null. -/
  gain : Within "safety"
    (Lacking "gain" fun inner (gain : UInt16) => Counted inner gain.toNat) json state.gain
  /-- The limits are the ones that the names of `move.limited_by` state. -/
  limits : Within "move" Limited json state.limits

/-- **A state frame is read exactly when it is what the parameters write, member by
member.** For every JSON value and every state frame. -/
theorem State.read_iff (json : Json.Value) (state : State) :
    State.read json = some state ↔ State.Written json state := by
  have words := fun size => @vector_iff _ size _ _ Declared.milli.read_iff
  unfold State.read
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨taken, one, joints, two, speeds, three, gravity, four, gyro, five, position, six,
      driven, seven, fallen, eight, limp, nine, gain, ten, limited, eleven, rfl⟩
    exact
      { taken := (within_iff stamp_iff _ json taken).mp one
        joints := (within_iff (words 15) _ json joints).mp two
        speeds := (lacking_iff (words 15) _ json speeds).mp three
        gravity := (within_iff (within_iff (words 3) _) _ json gravity).mp four
        gyro := (within_iff (within_iff (words 3) _) _ json gyro).mp five
        height := ⟨position, (within_iff (within_iff (words 3) _) _ json position).mp six, rfl⟩
        policy := (within_iff Policy.read_iff _ json driven).mp seven
        fallen := (within_iff (within_iff flag_iff _) _ json fallen).mp eight
        limp := (within_iff (within_iff flag_iff _) _ json limp).mp nine
        gain := (within_iff (lacking_iff register_iff _) _ json gain).mp ten
        limits := (within_iff Limits.read_iff _ json limited).mp eleven }
  · intro written
    obtain ⟨position, placed, height⟩ := written.height
    refine ⟨state.taken, (within_iff stamp_iff _ json _).mpr written.taken,
      state.joints, (within_iff (words 15) _ json _).mpr written.joints,
      state.speeds, (lacking_iff (words 15) _ json _).mpr written.speeds,
      state.gravity, (within_iff (within_iff (words 3) _) _ json _).mpr written.gravity,
      state.gyro, (within_iff (within_iff (words 3) _) _ json _).mpr written.gyro,
      position, (within_iff (within_iff (words 3) _) _ json _).mpr placed,
      state.policy, (within_iff Policy.read_iff _ json _).mpr written.policy,
      state.fallen, (within_iff (within_iff flag_iff _) _ json _).mpr written.fallen,
      state.limp, (within_iff (within_iff flag_iff _) _ json _).mpr written.limp,
      state.gain, (within_iff (lacking_iff register_iff _) _ json _).mpr written.gain,
      state.limits, (within_iff Limits.read_iff _ json _).mpr written.limits, ?_⟩
    rw [height]

/-! ## A depth frame -/

/-- The zone of a status and of the JSON value of its distance. With the status 5, a valid
return, the distance is the one that `distance` reads. With another status the value must
be an integer of the record's signed sixteen-bit type, and the zone keeps the distance 0:
the distance of a zone without a valid return is not kept, because no consumer reads it. -/
private def zone (status : UInt8) (json : Json.Value) : Option Cell :=
  if status = 5 then (distance json).map (Cell.mk · status)
  else
    (integer json).bind fun value =>
      if -32768 ≤ value ∧ value ≤ 32767 then some ⟨⟨0, by decide, by decide⟩, status⟩
      else none

/-- The value is the distance of the zone, by the status of the zone. With the status 5, a
valid return, digits alone spell the distance (`Ranged`). With another status the value is
an integer from -32,768 to 32,767, the record's signed sixteen-bit type, that `Signed`
spells, and the distance of the zone is 0. -/
def Zoned (json : Json.Value) (cell : Cell) : Prop :=
  if cell.status = 5 then Ranged json cell.distance
  else (∃ integer : Int, Signed json integer ∧ -32768 ≤ integer ∧ integer ≤ 32767) ∧
    cell.distance.val = 0

/-- A value is read as the zone of a status exactly when the zone has that status and the
value is its distance. -/
private theorem zone_iff (status : UInt8) (json : Json.Value) (cell : Cell) :
    zone status json = some cell ↔ cell.status = status ∧ Zoned json cell := by
  obtain ⟨⟨measured, bounds⟩, stated⟩ := cell
  unfold zone Zoned
  dsimp only
  by_cases valid : status = 5
  · subst valid
    rw [ite_eq_left rfl, Option.map_eq_some_iff]
    constructor
    · rintro ⟨word, read, same⟩
      cases same
      exact ⟨rfl, by rw [ite_eq_left rfl]; exact (distance_iff json _).mp read⟩
    · rintro ⟨rfl, ranged⟩
      rw [ite_eq_left rfl] at ranged
      exact ⟨_, (distance_iff json _).mpr ranged, rfl⟩
  · rw [ite_eq_right valid, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨value, read, sized⟩
      split at sized
      · rename_i inside
        cases sized
        exact ⟨rfl, by
          rw [ite_eq_right valid]
          exact ⟨⟨value, (integer_iff json value).mp read, inside.1, inside.2⟩, rfl⟩⟩
      · exact nomatch sized
    · rintro ⟨rfl, zoned⟩
      rw [ite_eq_right valid] at zoned
      obtain ⟨⟨value, signed, low, high⟩, zero⟩ := zoned
      subst zero
      refine ⟨value, (integer_iff json value).mpr signed, ?_⟩
      rw [ite_eq_left ⟨low, high⟩]

/-- The zones of a list of statuses and of the JSON values of their distances, in order.
Nothing when the lists differ in length or one zone is not read. -/
private def zones : List UInt8 → List Json.Value → Option (List Cell)
  | [], [] => some []
  | [], _ :: _ => none
  | _ :: _, [] => none
  | status :: statuses, value :: values =>
    (zone status value).bind fun first => (zones statuses values).map (first :: ·)

/-- A list of values is read as zones exactly when each value is the distance of the zone
in its place, and the zones have the statuses, in order. -/
private theorem zones_iff (statuses : List UInt8) (values : List Json.Value) (cells : List Cell) :
    zones statuses values = some cells ↔
      Each Zoned values cells ∧ cells.map (·.status) = statuses := by
  induction values generalizing statuses cells with
  | nil =>
    cases statuses with
    | nil =>
      simp only [zones, Option.some.injEq, List.map_eq_nil_iff]
      constructor
      · rintro rfl
        exact ⟨.nil, rfl⟩
      · rintro ⟨related, _⟩
        cases related
        rfl
    | cons status statuses =>
      simp only [zones, reduceCtorEq, false_iff]
      rintro ⟨related, same⟩
      cases related
      simp at same
  | cons head tail hold =>
    cases statuses with
    | nil =>
      simp only [zones, reduceCtorEq, false_iff]
      rintro ⟨related, same⟩
      cases related
      simp at same
    | cons status statuses =>
      simp only [zones, Option.bind_eq_some_iff, Option.map_eq_some_iff]
      constructor
      · rintro ⟨first, one, others, rest, rfl⟩
        obtain ⟨stated, zoned⟩ := (zone_iff status head first).mp one
        obtain ⟨related, same⟩ := (hold statuses others).mp rest
        exact ⟨.cons zoned related, by rw [List.map_cons, stated, same]⟩
      · rintro ⟨related, same⟩
        cases related with
        | cons zoned rest =>
          rw [List.map_cons, List.cons.injEq] at same
          exact ⟨_, (zone_iff status head _).mpr ⟨same.1, zoned⟩,
            _, (hold statuses _).mpr ⟨rest, same.2⟩, rfl⟩

/-- The sixty-four zones of a depth frame, from its statuses and from the value of its
distances, an array of one distance for each status. Nothing for an array of another
length, for an array with a zone that is not read and for a value that is no array. -/
private def grid (statuses : Vector UInt8 64) : Json.Value → Option (Vector Cell 64)
  | .array values =>
    (zones statuses.toList values).bind fun cells =>
      if exact : cells.length = 64 then some ⟨cells.toArray, exact⟩ else none
  | _ => none

/-- A value is read as the zones of the statuses exactly when each of its values is the
distance of the zone in its place, and the zones have the statuses. -/
private theorem grid_iff (statuses : Vector UInt8 64) (json : Json.Value)
    (cells : Vector Cell 64) :
    grid statuses json = some cells ↔
      Listed Zoned json cells ∧ cells.map (·.status) = statuses := by
  unfold Listed
  cases json with
  | array values =>
    unfold grid
    rw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨items, collected, sized⟩
      split at sized
      · cases Option.some.inj sized
        obtain ⟨related, same⟩ := (zones_iff _ values items).mp collected
        refine ⟨⟨values, rfl, related⟩, Vector.toList_inj.mp ?_⟩
        simpa using same
      · exact nomatch sized
    · rintro ⟨⟨_, same, related⟩, stated⟩
      cases same
      refine ⟨cells.toList, (zones_iff _ values _).mpr ⟨related, ?_⟩, ?_⟩
      · rw [← stated, Vector.toList_map]
      · simp [Vector.toList]
  | null | bool _ | number _ | string _ | object _ =>
    exact ⟨fun found => (nomatch found), fun ⟨⟨_, same, _⟩, _⟩ => (nomatch same)⟩

/-- The depth frame that the parameters of a `tof.frame` notification hold. Nothing when
the frame does not state eight rows and eight columns, and when a member that the frame
keeps is missing or is not read. The distance of a zone is read by its status (`Zoned`): a
frame with a zone of the status 5 whose distance is not a whole number of millimetres from
0 to 32,767, or with a zone of another status whose distance is not an integer of sixteen
signed bits, is refused whole. -/
def Depth.read (json : Json.Value) : Option Depth :=
  (within "rows" count json).bind fun rows =>
  (within "cols" count json).bind fun columns =>
    if rows = 8 then
      if columns = 8 then
        (within "t_ns" stamp json).bind fun taken =>
        (within "status" (vector 64 byte) json).bind fun statuses =>
        (within "distance_mm" (grid statuses) json).map fun cells => ⟨taken, cells⟩
      else none
    else none

/-- What a depth frame keeps of the parameters of a `tof.frame` notification, member by
member. It names the member that each field is read from, and no reader of this module.
`Counted` and `Signed` are written with the arithmetic of the decimal module. No number of
a depth frame is rounded or saturated. -/
structure Depth.Written (json : Json.Value) (depth : Depth) : Prop where
  /-- The frame states eight rows. -/
  rows : Within "rows" Counted json 8
  /-- The frame states eight columns. -/
  columns : Within "cols" Counted json 8
  /-- The stamp is the natural number of `t_ns`. -/
  taken : Within "t_ns" (fun inner (taken : Stamp) => Counted inner taken.nanoseconds) json
    depth.taken
  /-- The sixty-four values of `distance_mm` are the distances of the zones, in order, each
  by the status of its zone (`Zoned`): with the status 5, the distance written, a whole
  number of millimetres from 0 to 32,767 that digits alone spell; with another status, an
  integer from -32,768 to 32,767, and the distance of the zone is 0. -/
  distances : Within "distance_mm" (Listed Zoned) json depth.cells
  /-- The statuses of the zones are the sixty-four natural numbers of `status`, in order,
  each below 256. -/
  statuses : Within "status" (Listed fun inner (status : UInt8) => Counted inner status.toNat)
    json (depth.cells.map (·.status))

/-- **A depth frame is read exactly when it is what the parameters write, member by
member.** For every JSON value and every depth frame. -/
theorem Depth.read_iff (json : Json.Value) (depth : Depth) :
    Depth.read json = some depth ↔ Depth.Written json depth := by
  have bytes := @vector_iff _ 64 _ _ byte_iff
  have zoned := fun statuses => within_iff (grid_iff statuses) "distance_mm" json
  unfold Depth.read
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨rows, one, columns, two, rest⟩
    split at rest
    · split at rest
      · rename_i eight wide
        subst eight wide
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at rest
        obtain ⟨taken, three, statuses, four, cells, five, rfl⟩ := rest
        obtain ⟨inner, member, listed, stated⟩ := (zoned statuses cells).mp five
        exact
          { rows := (within_iff count_iff _ json 8).mp one
            columns := (within_iff count_iff _ json 8).mp two
            taken := (within_iff stamp_iff _ json taken).mp three
            distances := ⟨inner, member, listed⟩
            statuses := by
              show Within _ _ json (cells.map (·.status))
              rw [stated]
              exact (within_iff bytes _ json statuses).mp four }
      · exact nomatch rest
    · exact nomatch rest
  · intro written
    refine ⟨8, (within_iff count_iff _ json 8).mpr written.rows,
      8, (within_iff count_iff _ json 8).mpr written.columns, ?_⟩
    simp only [↓reduceIte, Option.bind_eq_some_iff, Option.map_eq_some_iff]
    obtain ⟨inner, member, listed⟩ := written.distances
    exact ⟨depth.taken, (within_iff stamp_iff _ json _).mpr written.taken,
      depth.cells.map (·.status), (within_iff bytes _ json _).mpr written.statuses,
      depth.cells, (zoned _ _).mpr ⟨inner, member, listed, rfl⟩, rfl⟩

/-- **Every zone of a depth frame that is read keeps the distance that its status calls
for.** For every JSON value that is read as a depth frame: its member `distance_mm` is an
array of sixty-four values, and each value is paired with the zone in its place. With the
status 5, a valid return, the value is a number that digits alone spell, of at most
32,767, and it is the distance of the zone. With another status the value is an integer
from -32,768 to 32,767 with an optional minus sign and no point or exponent, and the
distance of the zone is 0. So a frame with a distance of `65536`, of `2.5` or of `1e3` is
not read, whatever the status of its zone, and a frame with a distance of `-1` is read only
when the status of its zone is not 5. -/
theorem Depth.read_distances (json : Json.Value) (depth : Depth)
    (read : Depth.read json = some depth) :
    ∃ values : List Json.Value, Json.Value.Member "distance_mm" json (.array values) ∧
      values.length = 64 ∧ ∀ pair ∈ values.zip depth.cells.toList,
        (pair.2.status = 5 → ∃ natural : Nat, Counted pair.1 natural ∧ natural ≤ 32767 ∧
          (natural : Int) = pair.2.distance.val) ∧
        (pair.2.status ≠ 5 → (∃ integer : Int, Signed pair.1 integer ∧ -32768 ≤ integer ∧
          integer ≤ 32767) ∧ pair.2.distance.val = 0) := by
  obtain ⟨_, member, values, rfl, each⟩ := ((Depth.read_iff json depth).mp read).distances
  refine ⟨values, member, by rw [each.length]; simp, fun pair inside => ?_⟩
  have zoned := each.zip pair inside
  unfold Zoned at zoned
  constructor
  · intro valid
    rw [ite_eq_left valid] at zoned
    obtain ⟨natural, counted, same⟩ := zoned
    exact ⟨natural, counted, Int.ofNat_le.mp (same ▸ pair.2.distance.property.2), same⟩
  · intro other
    rw [ite_eq_right other] at zoned
    exact zoned

end Acorn.Host.Microduck
