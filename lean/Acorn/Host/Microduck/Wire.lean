import Acorn.Host.Microduck.Bridge
import Acorn.Host.Microduck.Sensing

namespace Acorn.Host.Microduck

private def Scale.read (scale : Scale) (json : Json.Value) : Option scale.Word :=
  (Decimal.read json).map (·.fixed scale)

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

private def count (json : Json.Value) : Option Nat :=
  match json.numeral with
  | some ⟨false, whole, none, none⟩ => some (spelled whole)
  | _ => none

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

private def collect {α : Type} (read : Json.Value → Option α) : List Json.Value → Option (List α)
  | [] => some []
  | head :: tail => (read head).bind fun first => (collect read tail).map (first :: ·)

inductive Each {α : Type} (Read : Json.Value → α → Prop) : List Json.Value → List α → Prop where
  | nil : Each Read [] []
  | cons {value : Json.Value} {result : α} {values : List Json.Value} {results : List α}
      (first : Read value result) (rest : Each Read values results) :
      Each Read (value :: values) (result :: results)

theorem Each.length {α : Type} {Read : Json.Value → α → Prop} {values : List Json.Value}
    {results : List α} (each : Each Read values results) : values.length = results.length := by
  induction each with
  | nil => rfl
  | cons _ _ hold => rw [List.length_cons, List.length_cons, hold]

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

private def vector {α : Type} (size : Nat) (read : Json.Value → Option α) :
    Json.Value → Option (Vector α size)
  | .array values =>
    (collect read values).bind fun results =>
      if exact : results.length = size then some ⟨results.toArray, exact⟩ else none
  | _ => none

def Listed {α : Type} {size : Nat} (Read : Json.Value → α → Prop) (json : Json.Value)
    (results : Vector α size) : Prop :=
  ∃ values : List Json.Value, json = .array values ∧ Each Read values results.toList

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

private def within {α : Type} (name : String) (read : Json.Value → Option α) (json : Json.Value) :
    Option α :=
  (json.member name).bind read

def Within {α : Type} (name : String) (Read : Json.Value → α → Prop) (json : Json.Value)
    (result : α) : Prop :=
  ∃ inner : Json.Value, Json.Value.Member name json inner ∧ Read inner result

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

private def found {α : Type} (read : Json.Value → Option α) :
    Option Json.Value → Option (Option α)
  | none => some none
  | some .null => some none
  | some inner => (read inner).map some

private def lacking {α : Type} (name : String) (read : Json.Value → Option α) :
    Json.Value → Option (Option α)
  | .object fields => found read ((Json.Value.object fields).member name)
  | _ => none

def Lacking {α : Type} (name : String) (Read : Json.Value → α → Prop) (json : Json.Value)
    (result : Option α) : Prop :=
  (result = none ∧ (∃ fields, json = .object fields) ∧
      ∀ inner, Json.Value.Member name json inner → inner = .null) ∨
    ∃ inner value, Json.Value.Member name json inner ∧ inner ≠ .null ∧ Read inner value ∧
      result = some value

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

private def stamp (json : Json.Value) : Option Stamp :=
  (count json).map Stamp.mk

private theorem stamp_iff (json : Json.Value) (taken : Stamp) :
    stamp json = some taken ↔ Counted json taken.nanoseconds := by
  unfold stamp
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨natural, counted, rfl⟩
    exact (count_iff json natural).mp counted
  · intro counted
    exact ⟨taken.nanoseconds, (count_iff json _).mpr counted, rfl⟩

private def byte (json : Json.Value) : Option UInt8 :=
  (count json).bind fun natural => if natural < 256 then some natural.toUInt8 else none

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

private def register (json : Json.Value) : Option UInt16 :=
  (count json).bind fun natural => if natural < 65536 then some natural.toUInt16 else none

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

private def distance (json : Json.Value) : Option Declared.range.Word :=
  (count json).bind fun natural =>
    if inside : natural ≤ 32767 then
      some ⟨natural, Int.natCast_nonneg natural, Int.ofNat_le.mpr inside⟩
    else none

def Ranged (json : Json.Value) (distance : Declared.range.Word) : Prop :=
  ∃ natural : Nat, Counted json natural ∧ (natural : Int) = distance.val

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

private def integer (json : Json.Value) : Option Int :=
  match json.numeral with
  | some ⟨negative, whole, none, none⟩ =>
    some (if negative then -(spelled whole : Int) else spelled whole)
  | _ => none

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

private def flag : Json.Value → Option Bool
  | .bool value => some value
  | _ => none

def Flagged (json : Json.Value) (value : Bool) : Prop :=
  json = .bool value

private theorem flag_iff (json : Json.Value) (value : Bool) :
    flag json = some value ↔ Flagged json value := by
  cases json <;> simp [flag, Flagged]

private def text : Json.Value → Option String
  | .string value => some value
  | _ => none

def Said (json : Json.Value) (value : String) : Prop :=
  json = .string value

private theorem text_iff (json : Json.Value) (value : String) :
    text json = some value ↔ Said json value := by
  cases json <;> simp [text, Said]

private def texts : Json.Value → Option (List String)
  | .array values => collect text values
  | _ => none

def Texts (json : Json.Value) (names : List String) : Prop :=
  ∃ values : List Json.Value, json = .array values ∧ Each Said values names

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

inductive Policy.Labelled : String → Policy → Prop where
  | stand : Policy.Labelled "stand" .stand
  | walk : Policy.Labelled "walk" .walk
  | held : Policy.Labelled "held" .held
  | homing : Policy.Labelled "homing" .homing
  | sit : Policy.Labelled "sit" .sit
  | rise : Policy.Labelled "rise" .rise
  | kickLeft : Policy.Labelled "kick_left" .kickLeft
  | kickRight : Policy.Labelled "kick_right" .kickRight
  | groundPick : Policy.Labelled "ground_pick" .groundPick
  | roulade : Policy.Labelled "roulade" .roulade
  | other (label : String)
      (unknown : label ∉ ["stand", "walk", "held", "homing", "sit", "rise", "kick_left",
        "kick_right", "ground_pick", "roulade"]) : Policy.Labelled label .other

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

def Limits.named (names : List String) : Limits :=
  ⟨names.contains "deadman", names.contains "joint_range", names.contains "not_finite",
    names.any fun name => name != "deadman" && name != "joint_range" && name != "not_finite"⟩

def Limits.Named (names : List String) (limits : Limits) : Prop :=
  (limits.deadman = true ↔ "deadman" ∈ names) ∧
    (limits.range = true ↔ "joint_range" ∈ names) ∧
      (limits.finite = true ↔ "not_finite" ∈ names) ∧
        (limits.other = true ↔
          ∃ name ∈ names, name ≠ "deadman" ∧ name ≠ "joint_range" ∧ name ≠ "not_finite")

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

private def Policy.read (json : Json.Value) : Option Policy :=
  (text json).map Policy.named

def Driven (json : Json.Value) (policy : Policy) : Prop :=
  ∃ label : String, Said json label ∧ Policy.Labelled label policy

private theorem Policy.read_iff (json : Json.Value) (result : Policy) :
    Policy.read json = some result ↔ Driven json result := by
  unfold Policy.read Driven
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨label, read, named⟩
    exact ⟨label, (text_iff json label).mp read, (Policy.named_iff label result).mp named⟩
  · rintro ⟨label, same, labelled⟩
    exact ⟨label, (text_iff json label).mpr same, (Policy.named_iff label result).mpr labelled⟩

private def Limits.read (json : Json.Value) : Option Limits :=
  (lacking "limited_by" texts json).map fun names => Limits.named (names.getD [])

def Limited (json : Json.Value) (limits : Limits) : Prop :=
  ∃ names : Option (List String), Lacking "limited_by" Texts json names ∧
    Limits.Named (names.getD []) limits

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

structure State.Written (json : Json.Value) (state : State) : Prop where
  taken : Within "t_ns" (fun inner (taken : Stamp) => Counted inner taken.nanoseconds) json
    state.taken
  joints : Within "joints" (Listed Declared.milli.Kept) json state.joints
  speeds : Lacking "velocities" (Listed Declared.milli.Kept) json state.speeds
  gravity : Within "safety" (Within "gravity" (Listed Declared.milli.Kept)) json state.gravity
  gyro : Within "imu" (Within "gyro" (Listed Declared.milli.Kept)) json state.gyro
  height : ∃ position : Vector Declared.milli.Word 3,
    Within "odom" (Within "position" (Listed Declared.milli.Kept)) json position ∧
      position[2] = state.height
  policy : Within "policy" Driven json state.policy
  fallen : Within "safety" (Within "fallen" Flagged) json state.fallen
  limp : Within "safety" (Within "limp" Flagged) json state.limp
  gain : Within "safety"
    (Lacking "gain" fun inner (gain : UInt16) => Counted inner gain.toNat) json state.gain
  limits : Within "move" Limited json state.limits

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

private def zone (status : UInt8) (json : Json.Value) : Option Cell :=
  if status = 5 then (distance json).map (Cell.mk · status)
  else
    (integer json).bind fun value =>
      if -32768 ≤ value ∧ value ≤ 32767 then some ⟨⟨0, by decide, by decide⟩, status⟩
      else none

def Zoned (json : Json.Value) (cell : Cell) : Prop :=
  if cell.status = 5 then Ranged json cell.distance
  else (∃ integer : Int, Signed json integer ∧ -32768 ≤ integer ∧ integer ≤ 32767) ∧
    cell.distance.val = 0

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

private def zones : List UInt8 → List Json.Value → Option (List Cell)
  | [], [] => some []
  | [], _ :: _ => none
  | _ :: _, [] => none
  | status :: statuses, value :: values =>
    (zone status value).bind fun first => (zones statuses values).map (first :: ·)

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

private def grid (statuses : Vector UInt8 64) : Json.Value → Option (Vector Cell 64)
  | .array values =>
    (zones statuses.toList values).bind fun cells =>
      if exact : cells.length = 64 then some ⟨cells.toArray, exact⟩ else none
  | _ => none

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

structure Depth.Written (json : Json.Value) (depth : Depth) : Prop where
  rows : Within "rows" Counted json 8
  columns : Within "cols" Counted json 8
  taken : Within "t_ns" (fun inner (taken : Stamp) => Counted inner taken.nanoseconds) json
    depth.taken
  distances : Within "distance_mm" (Listed Zoned) json depth.cells
  statuses : Within "status" (Listed fun inner (status : UInt8) => Counted inner status.toNat)
    json (depth.cells.map (·.status))

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

inductive Stream where
  | state
  | depth
  deriving DecidableEq

structure Spelling where
  forward : Json.Numeral
  left : Json.Numeral
  turn : Json.Numeral

def nought : Json.Numeral := ⟨false, ['0'], some ['0'], none⟩

def Velocity.spelling : Velocity → Spelling
  | .zero => ⟨nought, nought, nought⟩
  | .forward => ⟨⟨false, ['0'], some ['3'], none⟩, nought, nought⟩
  | .left => ⟨nought, nought, ⟨false, ['1'], some ['5'], none⟩⟩
  | .right => ⟨nought, nought, ⟨true, ['1'], some ['5'], none⟩⟩

def Skill.name : Skill → String
  | .groundPick => "ground_pick"
  | .sitToggle => "sit_toggle"
  | .roulade => "roulade"
  | .kickLeft => "kick_left"
  | .kickRight => "kick_right"

def Command.method : Command → String
  | .enable => "robot.enable"
  | .move _ => "robot.move"
  | .perform _ => "robot.do"

theorem Velocity.spelling_formed (velocity : Velocity) :
    (velocity.spelling.forward.Formed ∧ velocity.spelling.forward.exponent = none) ∧
      (velocity.spelling.left.Formed ∧ velocity.spelling.left.exponent = none) ∧
      (velocity.spelling.turn.Formed ∧ velocity.spelling.turn.exponent = none) := by
  have formed : ∀ numeral : Json.Numeral,
      Json.Numeral.scan numeral.chars = some (numeral, []) → numeral.Formed :=
    fun _ scanned => (Json.Numeral.scan_formed scanned).1
  cases velocity <;>
    exact ⟨⟨formed _ (by decide), rfl⟩, ⟨formed _ (by decide), rfl⟩, ⟨formed _ (by decide), rfl⟩⟩

def Command.given : Command → Json.Part
  | .enable => .object [("on", .flag true)]
  | .move velocity =>
    .object [("vx", .number velocity.spelling.forward), ("vy", .number velocity.spelling.left),
      ("vyaw", .number velocity.spelling.turn)]
  | .perform skill => .object [("skill", .text skill.name)]

def Command.request (id : Nat) (command : Command) : Json.Request :=
  [("jsonrpc", .scalar (.text "2.0")), ("id", .scalar (.number (Json.Numeral.natural id))),
    ("method", .scalar (.text command.method)), ("params", command.given)]

def Command.line (id : Nat) (command : Command) : String :=
  String.ofList (command.request id).chars

def Stream.subscription : Stream → String
  | .state => "robot.subscribe"
  | .depth => "tof.stream"

def Stream.request (id : Nat) : Stream → Json.Request
  | .state =>
    [("jsonrpc", .scalar (.text "2.0")), ("id", .scalar (.number (Json.Numeral.natural id))),
      ("method", .scalar (.text "robot.subscribe")), ("params", .object [])]
  | .depth =>
    [("jsonrpc", .scalar (.text "2.0")), ("id", .scalar (.number (Json.Numeral.natural id))),
      ("method", .scalar (.text "tof.stream"))]

def Stream.line (id : Nat) (stream : Stream) : String :=
  String.ofList (stream.request id).chars

def Named (json : Json.Value) (members : List String) : Prop :=
  ∃ fields : List (String × Json.Value), json = .object fields ∧ fields.map (·.1) = members

def Numbered (json : Json.Value) (numeral : Json.Numeral) : Prop :=
  numeral.Formed ∧ json = .number (String.ofList numeral.chars)

def Command.parameters : Command → List String
  | .enable => ["on"]
  | .move _ => ["vx", "vy", "vyaw"]
  | .perform _ => ["skill"]

def Command.Given : Command → Json.Value → Prop
  | .enable, json => Within "params" (Within "on" Flagged) json true
  | .move velocity, json =>
    Within "params" (Within "vx" Numbered) json velocity.spelling.forward ∧
      Within "params" (Within "vy" Numbered) json velocity.spelling.left ∧
        Within "params" (Within "vyaw" Numbered) json velocity.spelling.turn
  | .perform skill, json => Within "params" (Within "skill" Said) json skill.name

structure Command.Asked (id : Nat) (command : Command) (json : Json.Value) : Prop where
  members : Named json ["jsonrpc", "id", "method", "params"]
  parameters : Within "params" Named json command.parameters
  version : Within "jsonrpc" Said json "2.0"
  id : Within "id" Counted json id
  method : Within "method" Said json command.method
  given : command.Given json

def Stream.members : Stream → List String
  | .state => ["jsonrpc", "id", "method", "params"]
  | .depth => ["jsonrpc", "id", "method"]

structure Stream.Asked (id : Nat) (stream : Stream) (json : Json.Value) : Prop where
  members : Named json stream.members
  version : Within "jsonrpc" Said json "2.0"
  id : Within "id" Counted json id
  method : Within "method" Said json stream.subscription
  bare : stream = .state → Within "params" Named json []

private theorem plain (written : String)
    (checked : (written.toList.all fun c => decide (Json.Plain c)) = true) :
    ∀ c ∈ written.toList, Json.Plain c :=
  fun c inside => of_decide_eq_true (List.all_eq_true.mp checked c inside)

private theorem Command.request_simple (id : Nat) (command : Command) :
    (command.request id).Simple := by
  refine ⟨fun pair inside => ?_, (by decide : ["jsonrpc", "id", "method", "params"].Nodup)⟩
  simp only [Command.request, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl
  · exact ⟨plain "jsonrpc" rfl, plain "2.0" rfl⟩
  · exact ⟨plain "id" rfl, Json.Numeral.natural_formed id, rfl⟩
  · refine ⟨plain "method" rfl, ?_⟩
    cases command with
    | enable => exact plain "robot.enable" rfl
    | move velocity => exact plain "robot.move" rfl
    | perform skill => exact plain "robot.do" rfl
  · refine ⟨plain "params" rfl, ?_⟩
    cases command with
    | enable =>
      exact ⟨fun pair inside => by
        cases List.mem_singleton.mp inside
        exact ⟨plain "on" rfl, trivial⟩, (by decide : ["on"].Nodup)⟩
    | move velocity =>
      obtain ⟨forward, left, turn⟩ := velocity.spelling_formed
      refine ⟨fun pair inside => ?_, (by decide : ["vx", "vy", "vyaw"].Nodup)⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact ⟨plain "vx" rfl, forward⟩
      · exact ⟨plain "vy" rfl, left⟩
      · exact ⟨plain "vyaw" rfl, turn⟩
    | perform skill =>
      exact ⟨fun pair inside => by
        cases List.mem_singleton.mp inside
        exact ⟨plain "skill" rfl, by
          cases skill
          · exact plain "ground_pick" rfl
          · exact plain "sit_toggle" rfl
          · exact plain "roulade" rfl
          · exact plain "kick_left" rfl
          · exact plain "kick_right" rfl⟩,
        (by decide : ["skill"].Nodup)⟩

private theorem Stream.request_simple (id : Nat) (stream : Stream) :
    (stream.request id).Simple := by
  cases stream with
  | state =>
    refine ⟨fun pair inside => ?_, (by decide : ["jsonrpc", "id", "method", "params"].Nodup)⟩
    simp only [Stream.request, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl
    · exact ⟨plain "jsonrpc" rfl, plain "2.0" rfl⟩
    · exact ⟨plain "id" rfl, Json.Numeral.natural_formed id, rfl⟩
    · exact ⟨plain "method" rfl, plain "robot.subscribe" rfl⟩
    · exact ⟨plain "params" rfl, fun _ wrong => (nomatch wrong), List.nodup_nil⟩
  | depth =>
    refine ⟨fun pair inside => ?_, (by decide : ["jsonrpc", "id", "method"].Nodup)⟩
    simp only [Stream.request, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl
    · exact ⟨plain "jsonrpc" rfl, plain "2.0" rfl⟩
    · exact ⟨plain "id" rfl, Json.Numeral.natural_formed id, rfl⟩
    · exact ⟨plain "method" rfl, plain "tof.stream" rfl⟩

private theorem held {name : String} {json inner : Json.Value}
    (looked : json.member name = some inner) : Json.Value.Member name json inner :=
  (Json.Value.member_iff name json inner).mp looked

theorem Command.line_asked (id : Nat) (command : Command) :
    ∃ json : Json.Value, Json.parse (command.line id) = .ok json ∧ command.Asked id json := by
  refine ⟨(command.request id).value,
    Json.parse_request (command.request id) (command.request_simple id), ?_⟩
  refine ⟨⟨_, rfl, rfl⟩, ?_, ⟨_, held rfl, rfl⟩, ⟨_, held rfl, counted_natural id⟩,
    ⟨_, held rfl, rfl⟩, ?_⟩
  · cases command <;> exact ⟨_, held rfl, _, rfl, rfl⟩
  · cases command with
    | enable => exact ⟨_, held rfl, _, held rfl, rfl⟩
    | move velocity =>
      obtain ⟨forward, left, turn⟩ := velocity.spelling_formed
      exact ⟨⟨_, held rfl, _, held rfl, forward.1, rfl⟩,
        ⟨_, held rfl, _, held rfl, left.1, rfl⟩, ⟨_, held rfl, _, held rfl, turn.1, rfl⟩⟩
    | perform skill => exact ⟨_, held rfl, _, held rfl, rfl⟩

theorem Stream.line_asked (id : Nat) (stream : Stream) :
    ∃ json : Json.Value, Json.parse (stream.line id) = .ok json ∧ stream.Asked id json := by
  refine ⟨(stream.request id).value,
    Json.parse_request (stream.request id) (stream.request_simple id), ?_⟩
  cases stream with
  | state =>
    exact ⟨⟨_, rfl, rfl⟩, ⟨_, held rfl, rfl⟩, ⟨_, held rfl, counted_natural id⟩,
      ⟨_, held rfl, rfl⟩, fun _ => ⟨_, held rfl, _, rfl, rfl⟩⟩
  | depth =>
    exact ⟨⟨_, rfl, rfl⟩, ⟨_, held rfl, rfl⟩, ⟨_, held rfl, counted_natural id⟩,
      ⟨_, held rfl, rfl⟩, fun wrong => nomatch wrong⟩

def Stream.method : Stream → String
  | .state => "robot.state"
  | .depth => "tof.frame"

def Stream.Unwritten : Stream → Json.Value → Prop
  | .state, json => ∀ frame, ¬Within "params" State.Written json frame
  | .depth, json => ∀ frame, ¬Within "params" Depth.Written json frame

inductive Line where
  | state (frame : State)
  | depth (frame : Depth)
  | unread (stream : Stream)
  | notice
  | result (id : Nat) (accepted : Option Bool)
  | fault (id : Option Nat)
  | invalid

def Lacks (name : String) (json : Json.Value) : Prop :=
  ∀ inner, ¬Json.Value.Member name json inner

private theorem lacks_iff (name : String) (json : Json.Value) :
    json.member name = none ↔ Lacks name json := by
  unfold Lacks
  rw [Option.eq_none_iff_forall_ne_some]
  exact ⟨fun none inner member => none inner ((Json.Value.member_iff name json inner).mpr member),
    fun none inner looked => none inner ((Json.Value.member_iff name json inner).mp looked)⟩

def Versioned (json : Json.Value) : Prop :=
  Within "jsonrpc" Said json "2.0"

def Notified (json : Json.Value) (method : String) : Prop :=
  Versioned json ∧ Lacks "id" json ∧ Within "method" Said json method

private def notified (json : Json.Value) : Option String :=
  if within "jsonrpc" text json = some "2.0" then
    match json.member "id" with
    | none => within "method" text json
    | some _ => none
  else none

private theorem notified_iff (json : Json.Value) (method : String) :
    notified json = some method ↔ Notified json method := by
  unfold notified Notified Versioned
  constructor
  · intro read
    split at read
    · rename_i versioned
      split at read
      · rename_i bare
        exact ⟨(within_iff text_iff _ json _).mp versioned, (lacks_iff "id" json).mp bare,
          (within_iff text_iff _ json _).mp read⟩
      · exact nomatch read
    · exact nomatch read
  · rintro ⟨versioned, bare, named⟩
    simp only [(within_iff text_iff _ json _).mpr versioned, ↓reduceIte,
      (lacks_iff "id" json).mpr bare]
    exact (within_iff text_iff _ json _).mpr named

def Accepting (result : Json.Value) (accepted : Option Bool) : Prop :=
  match accepted with
  | some value => Within "accepted" Flagged result value
  | none => ∀ value, ¬Within "accepted" Flagged result value

private def accepting (result : Json.Value) : Option (Option Bool) :=
  some (within "accepted" flag result)

private theorem accepting_iff (result : Json.Value) (accepted : Option Bool) :
    accepting result = some accepted ↔ Accepting result accepted := by
  unfold accepting Accepting
  rw [Option.some.injEq]
  cases accepted with
  | some value => exact within_iff flag_iff "accepted" result value
  | none =>
    rw [Option.eq_none_iff_forall_ne_some]
    exact ⟨fun none value read => none value ((within_iff flag_iff _ result value).mpr read),
      fun none value read => none value ((within_iff flag_iff _ result value).mp read)⟩

def Resulted (json : Json.Value) (id : Nat) (accepted : Option Bool) : Prop :=
  Versioned json ∧ Lacks "method" json ∧ Lacks "error" json ∧ Within "id" Counted json id ∧
    Within "result" Accepting json accepted

private def resulted (json : Json.Value) : Option (Nat × Option Bool) :=
  if within "jsonrpc" text json = some "2.0" then
    match json.member "method", json.member "error" with
    | none, none =>
      (within "id" count json).bind fun id =>
        (within "result" accepting json).map fun accepted => (id, accepted)
    | _, _ => none
  else none

private theorem resulted_iff (json : Json.Value) (id : Nat) (accepted : Option Bool) :
    resulted json = some (id, accepted) ↔ Resulted json id accepted := by
  unfold resulted Resulted Versioned
  constructor
  · intro read
    split at read
    · rename_i versioned
      split at read
      · rename_i unnamed sound
        obtain ⟨number, counted, rest⟩ := Option.bind_eq_some_iff.mp read
        obtain ⟨said, stated, same⟩ := Option.map_eq_some_iff.mp rest
        cases same
        exact ⟨(within_iff text_iff _ json _).mp versioned, (lacks_iff "method" json).mp unnamed,
          (lacks_iff "error" json).mp sound, (within_iff count_iff _ json _).mp counted,
          (within_iff accepting_iff _ json _).mp stated⟩
      · exact nomatch read
    · exact nomatch read
  · rintro ⟨versioned, unnamed, sound, counted, stated⟩
    simp only [(within_iff text_iff _ json _).mpr versioned, ↓reduceIte,
      (lacks_iff "method" json).mpr unnamed, (lacks_iff "error" json).mpr sound,
      (within_iff count_iff _ json _).mpr counted, Option.bind_some,
      (within_iff accepting_iff _ json _).mpr stated, Option.map_some]

def Integral (json : Json.Value) : Prop :=
  ∃ numeral : Json.Numeral, numeral.Formed ∧ numeral.fraction = none ∧
    numeral.exponent = none ∧ json = .number (String.ofList numeral.chars)

private def integral (json : Json.Value) : Bool :=
  match json.numeral with
  | some ⟨_, _, none, none⟩ => true
  | _ => false

private theorem integral_iff (json : Json.Value) : integral json = true ↔ Integral json := by
  unfold integral Integral
  constructor
  · intro whole
    cases scanned : json.numeral with
    | none =>
      rw [scanned] at whole
      exact nomatch whole
    | some numeral =>
      rw [scanned] at whole
      obtain ⟨negative, digits, fraction, exponent⟩ := numeral
      cases fraction <;> cases exponent <;>
        first
        | (simp at whole; done)
        | (obtain ⟨formed, same⟩ := (Json.Value.numeral_iff json _).mp scanned
           exact ⟨_, formed, rfl, rfl, same⟩)
  · rintro ⟨numeral, formed, pointless, bare, same⟩
    obtain ⟨negative, digits, fraction, exponent⟩ := numeral
    cases pointless
    cases bare
    rw [(Json.Value.numeral_iff json _).mpr ⟨formed, same⟩]

def Erring (error : Json.Value) : Prop :=
  (∃ code, Json.Value.Member "code" error code ∧ Integral code) ∧
    ∃ message, Within "message" Said error message

private def erring (error : Json.Value) : Bool :=
  (match error.member "code" with
    | some code => integral code
    | none => false) && (within "message" text error).isSome

private theorem erring_iff (error : Json.Value) : erring error = true ↔ Erring error := by
  unfold erring Erring
  rw [Bool.and_eq_true, Option.isSome_iff_exists]
  constructor
  · rintro ⟨coded, message, read⟩
    cases looked : error.member "code" with
    | none =>
      rw [looked] at coded
      exact nomatch coded
    | some code =>
      rw [looked] at coded
      exact ⟨⟨code, held looked, (integral_iff code).mp coded⟩, message,
        (within_iff text_iff _ error message).mp read⟩
  · rintro ⟨⟨code, member, whole⟩, message, said⟩
    rw [(Json.Value.member_iff "code" error code).mpr member]
    exact ⟨(integral_iff code).mpr whole, message, (within_iff text_iff _ error message).mpr said⟩

def Identified (json : Json.Value) (id : Option Nat) : Prop :=
  match id with
  | some number => Within "id" Counted json number
  | none => Json.Value.Member "id" json .null

private def identified (json : Json.Value) : Option (Option Nat) :=
  match json.member "id" with
  | none => none
  | some .null => some none
  | some inner => (count inner).map some

private theorem identified_iff (json : Json.Value) (id : Option Nat) :
    identified json = some id ↔ Identified json id := by
  have single : ∀ first second : Json.Value, json.member "id" = some first →
      Json.Value.Member "id" json second → second = first := fun first second looked other =>
    Option.some.inj (((Json.Value.member_iff "id" json second).mpr other).symm.trans looked)
  have nothing : ¬Counted .null 0 ∧ ∀ number, ¬Counted .null number :=
    ⟨fun ⟨_, _, wrong, _⟩ => (nomatch wrong), fun _ ⟨_, _, wrong, _⟩ => (nomatch wrong)⟩
  unfold identified Identified
  cases looked : json.member "id" with
  | none =>
    constructor
    · intro wrong
      exact nomatch wrong
    · intro held
      cases id with
      | some number =>
        obtain ⟨inner, member, _⟩ := held
        rw [(Json.Value.member_iff "id" json inner).mpr member] at looked
        exact nomatch looked
      | none =>
        rw [(Json.Value.member_iff "id" json .null).mpr held] at looked
        exact nomatch looked
  | some first =>
    have member := held looked
    by_cases empty : first = .null
    · subst empty
      constructor
      · intro read
        cases Option.some.inj read
        exact member
      · intro held
        cases id with
        | some number =>
          obtain ⟨inner, other, counted⟩ := held
          cases single _ inner looked other
          exact absurd counted (nothing.2 number)
        | none => rfl
    · have filled : (match some first with
          | none => none
          | some .null => some none
          | some inner => (count inner).map some) = (count first).map some := by
        cases first <;> first | rfl | exact absurd rfl empty
      rw [filled, Option.map_eq_some_iff]
      constructor
      · rintro ⟨number, counted, rfl⟩
        exact ⟨first, member, (count_iff first number).mp counted⟩
      · intro held
        cases id with
        | some number =>
          obtain ⟨inner, other, counted⟩ := held
          cases single _ inner looked other
          exact ⟨number, (count_iff first number).mpr counted, rfl⟩
        | none => exact absurd (single _ _ looked held).symm empty

def Faulted (json : Json.Value) (id : Option Nat) : Prop :=
  Versioned json ∧ Lacks "method" json ∧ Lacks "result" json ∧ Identified json id ∧
    ∃ error, Json.Value.Member "error" json error ∧ Erring error

private def faulted (json : Json.Value) : Option (Option Nat) :=
  if within "jsonrpc" text json = some "2.0" then
    match json.member "method", json.member "result", json.member "error" with
    | none, none, some error => if erring error then identified json else none
    | _, _, _ => none
  else none

private theorem faulted_iff (json : Json.Value) (id : Option Nat) :
    faulted json = some id ↔ Faulted json id := by
  unfold faulted Faulted Versioned
  constructor
  · intro read
    split at read
    · rename_i versioned
      split at read
      · rename_i error unnamed empty looked
        split at read
        · rename_i wrong
          exact ⟨(within_iff text_iff _ json _).mp versioned, (lacks_iff "method" json).mp unnamed,
            (lacks_iff "result" json).mp empty, (identified_iff json id).mp read, error,
            held looked, (erring_iff error).mp wrong⟩
        · exact nomatch read
      · exact nomatch read
    · exact nomatch read
  · rintro ⟨versioned, unnamed, empty, held, error, member, wrong⟩
    simp only [(within_iff text_iff _ json _).mpr versioned, ↓reduceIte,
      (lacks_iff "method" json).mpr unnamed, (lacks_iff "result" json).mpr empty,
      (Json.Value.member_iff "error" json error).mpr member, (erring_iff error).mpr wrong]
    exact (identified_iff json id).mpr held

private def framed (json : Json.Value) (method : String) : Line :=
  if method = "robot.state" then
    match within "params" State.read json with
    | some frame => .state frame
    | none => .unread .state
  else if method = "tof.frame" then
    match within "params" Depth.read json with
    | some frame => .depth frame
    | none => .unread .depth
  else .notice

def Line.read (json : Json.Value) : Line :=
  match notified json with
  | some method => framed json method
  | none =>
    match resulted json with
    | some (id, accepted) => .result id accepted
    | none =>
      match faulted json with
      | some id => .fault id
      | none => .invalid

private theorem notified_none (json : Json.Value) (unnamed : Lacks "method" json) :
    notified json = none := by
  rw [Option.eq_none_iff_forall_ne_some]
  intro method read
  obtain ⟨_, _, inner, member, _⟩ := (notified_iff json method).mp read
  exact unnamed inner member

private theorem resulted_none (json : Json.Value) (error : Json.Value)
    (member : Json.Value.Member "error" json error) : resulted json = none := by
  rw [Option.eq_none_iff_forall_ne_some]
  rintro ⟨id, accepted⟩ read
  exact ((resulted_iff json id accepted).mp read).2.2.1 error member

private theorem framed_cases (json : Json.Value) (method : String) :
    (∀ id accepted, framed json method ≠ .result id accepted) ∧
      (∀ id, framed json method ≠ .fault id) ∧ framed json method ≠ .invalid := by
  unfold framed
  refine ⟨fun id accepted same => ?_, fun id same => ?_, fun same => ?_⟩ <;>
    (split at same
     · split at same <;> exact nomatch same
     · split at same
       · split at same <;> exact nomatch same
       · exact nomatch same)

private theorem read_framed (json : Json.Value) (line : Line)
    (other : (∀ id accepted, line ≠ .result id accepted) ∧ (∀ id, line ≠ .fault id) ∧
      line ≠ .invalid) :
    Line.read json = line ↔ ∃ method, Notified json method ∧ framed json method = line := by
  unfold Line.read
  cases read : notified json with
  | some method =>
    constructor
    · intro same
      exact ⟨method, (notified_iff json method).mp read, same⟩
    · rintro ⟨other, noted, same⟩
      cases Option.some.inj (((notified_iff json other).mpr noted).symm.trans read)
      exact same
  | none =>
    constructor
    · intro same
      have same : (match resulted json with
        | some (id, accepted) => Line.result id accepted
        | none =>
          match faulted json with
          | some id => .fault id
          | none => .invalid) = line := same
      split at same
      · exact absurd same.symm (other.1 _ _)
      · split at same
        · exact absurd same.symm (other.2.1 _)
        · exact absurd same.symm other.2.2
    · rintro ⟨method, noted, _⟩
      rw [(notified_iff json method).mpr noted] at read
      exact nomatch read

theorem Line.read_state (json : Json.Value) (frame : State) :
    Line.read json = .state frame ↔
      Notified json "robot.state" ∧ Within "params" State.Written json frame := by
  have written := within_iff State.read_iff "params" json
  rw [read_framed json (.state frame) ⟨fun _ _ wrong => (nomatch wrong), fun _ wrong => (nomatch wrong),
    fun wrong => (nomatch wrong)⟩]
  constructor
  · rintro ⟨method, noted, same⟩
    unfold framed at same
    split at same
    · rename_i named
      subst named
      cases read : within "params" State.read json with
      | none =>
        rw [read] at same
        exact nomatch same
      | some held =>
        rw [read] at same
        cases same
        exact ⟨noted, (written _).mp read⟩
    · split at same
      · split at same <;> exact nomatch same
      · exact nomatch same
  · rintro ⟨noted, frames⟩
    refine ⟨_, noted, ?_⟩
    unfold framed
    simp only [↓reduceIte, (written frame).mpr frames]

theorem Line.read_depth (json : Json.Value) (frame : Depth) :
    Line.read json = .depth frame ↔
      Notified json "tof.frame" ∧ Within "params" Depth.Written json frame := by
  have written := within_iff Depth.read_iff "params" json
  rw [read_framed json (.depth frame) ⟨fun _ _ wrong => (nomatch wrong), fun _ wrong => (nomatch wrong),
    fun wrong => (nomatch wrong)⟩]
  constructor
  · rintro ⟨method, noted, same⟩
    unfold framed at same
    split at same
    · split at same <;> exact nomatch same
    · split at same
      · rename_i named
        subst named
        cases read : within "params" Depth.read json with
        | none =>
          rw [read] at same
          exact nomatch same
        | some held =>
          rw [read] at same
          cases same
          exact ⟨noted, (written _).mp read⟩
      · exact nomatch same
  · rintro ⟨noted, frames⟩
    refine ⟨_, noted, ?_⟩
    unfold framed
    simp only [String.reduceEq, ↓reduceIte, (written frame).mpr frames]

theorem Line.read_unread (json : Json.Value) (stream : Stream) :
    Line.read json = .unread stream ↔ Notified json stream.method ∧ stream.Unwritten json := by
  have states := within_iff State.read_iff "params" json
  have depths := within_iff Depth.read_iff "params" json
  rw [read_framed json (.unread stream) ⟨fun _ _ wrong => (nomatch wrong), fun _ wrong => (nomatch wrong),
    fun wrong => (nomatch wrong)⟩]
  constructor
  · rintro ⟨method, noted, same⟩
    unfold framed at same
    split at same
    · rename_i named
      subst named
      cases read : within "params" State.read json with
      | some held =>
        rw [read] at same
        exact nomatch same
      | none =>
        rw [read] at same
        cases same
        refine ⟨noted, fun frame written => ?_⟩
        rw [(states frame).mpr written] at read
        exact nomatch read
    · split at same
      · rename_i named
        subst named
        cases read : within "params" Depth.read json with
        | some held =>
          rw [read] at same
          exact nomatch same
        | none =>
          rw [read] at same
          cases same
          refine ⟨noted, fun frame written => ?_⟩
          rw [(depths frame).mpr written] at read
          exact nomatch read
      · exact nomatch same
  · rintro ⟨noted, unwritten⟩
    refine ⟨_, noted, ?_⟩
    unfold framed
    cases stream with
    | state =>
      have absent : within "params" State.read json = none :=
        Option.eq_none_iff_forall_ne_some.mpr fun frame read =>
          unwritten frame ((states frame).mp read)
      simp only [Stream.method, ↓reduceIte, absent]
    | depth =>
      have absent : within "params" Depth.read json = none :=
        Option.eq_none_iff_forall_ne_some.mpr fun frame read =>
          unwritten frame ((depths frame).mp read)
      simp only [Stream.method, String.reduceEq, ↓reduceIte, absent]

theorem Line.read_notice (json : Json.Value) :
    Line.read json = .notice ↔
      ∃ method, Notified json method ∧ method ≠ "robot.state" ∧ method ≠ "tof.frame" := by
  rw [read_framed json .notice ⟨fun _ _ wrong => (nomatch wrong), fun _ wrong => (nomatch wrong),
    fun wrong => (nomatch wrong)⟩]
  constructor
  · rintro ⟨method, noted, same⟩
    unfold framed at same
    split at same
    · split at same <;> exact nomatch same
    · rename_i state
      split at same
      · split at same <;> exact nomatch same
      · rename_i depth
        exact ⟨method, noted, state, depth⟩
  · rintro ⟨method, noted, state, depth⟩
    refine ⟨method, noted, ?_⟩
    unfold framed
    simp only [state, depth, ↓reduceIte]

theorem Line.read_result (json : Json.Value) (id : Nat) (accepted : Option Bool) :
    Line.read json = .result id accepted ↔ Resulted json id accepted := by
  unfold Line.read
  constructor
  · intro same
    cases noted : notified json with
    | some method =>
      rw [noted] at same
      exact absurd same ((framed_cases json method).1 id accepted)
    | none =>
      rw [noted] at same
      cases read : resulted json with
      | some pair =>
        rw [read] at same
        obtain ⟨number, stated⟩ := pair
        cases same
        exact (resulted_iff json id accepted).mp read
      | none =>
        rw [read] at same
        cases wrong : faulted json <;> rw [wrong] at same <;> exact nomatch same
  · intro held
    rw [notified_none json held.2.1, (resulted_iff json id accepted).mpr held]

theorem Line.read_fault (json : Json.Value) (id : Option Nat) :
    Line.read json = .fault id ↔ Faulted json id := by
  unfold Line.read
  constructor
  · intro same
    cases noted : notified json with
    | some method =>
      rw [noted] at same
      exact absurd same ((framed_cases json method).2.1 id)
    | none =>
      rw [noted] at same
      cases read : resulted json with
      | some pair =>
        rw [read] at same
        exact nomatch same
      | none =>
        rw [read] at same
        cases wrong : faulted json with
        | none =>
          rw [wrong] at same
          exact nomatch same
        | some other =>
          rw [wrong] at same
          cases same
          exact (faulted_iff json id).mp wrong
  · intro held
    obtain ⟨error, member, _⟩ := held.2.2.2.2
    rw [notified_none json held.2.1, resulted_none json error member,
      (faulted_iff json id).mpr held]

theorem Line.read_invalid (json : Json.Value) :
    Line.read json = .invalid ↔
      (∀ method, ¬Notified json method) ∧ (∀ id accepted, ¬Resulted json id accepted) ∧
        ∀ id, ¬Faulted json id := by
  unfold Line.read
  cases noted : notified json with
  | some method =>
    constructor
    · intro same
      exact absurd same (framed_cases json method).2.2
    · intro none
      exact absurd ((notified_iff json method).mp noted) (none.1 method)
  | none =>
    have unnoted : ∀ method, ¬Notified json method := fun method held => by
      rw [(notified_iff json method).mpr held] at noted
      exact nomatch noted
    cases read : resulted json with
    | some pair =>
      obtain ⟨id, accepted⟩ := pair
      constructor
      · intro same
        exact nomatch same
      · intro none
        exact absurd ((resulted_iff json id accepted).mp read) (none.2.1 id accepted)
    | none =>
      have unresulted : ∀ id accepted, ¬Resulted json id accepted := fun id accepted held => by
        rw [(resulted_iff json id accepted).mpr held] at read
        exact nomatch read
      cases wrong : faulted json with
      | some id =>
        constructor
        · intro same
          exact nomatch same
        · intro none
          exact absurd ((faulted_iff json id).mp wrong) (none.2.2 id)
      | none =>
        exact ⟨fun _ => ⟨unnoted, unresulted, fun id held => by
          rw [(faulted_iff json id).mpr held] at wrong
          exact nomatch wrong⟩, fun _ => rfl⟩

end Acorn.Host.Microduck
