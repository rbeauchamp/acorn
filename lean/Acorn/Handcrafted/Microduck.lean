import Acorn.Handcrafted.Signals
import Acorn.Host.Microduck.Bridge
import Acorn.Host.Microduck.Sensing

namespace Acorn.Handcrafted.Microduck
open Features
open Acorn.Host.Microduck (Reading State Depth Cell Policy Limits Outcome)

def channel (index : Fin 256) : UInt64 := 0x100 + index.val.toUInt64

def level (step : Nat) (word : Host.Microduck.Declared.milli.Word) : UInt64 :=
  ((word.val - Host.Microduck.Declared.milli.low).toNat / step).toUInt64

def Declared.angle : Nat := 100

def Declared.rate : Nat := 500

def Declared.share : Nat := 100

def Declared.turn : Nat := 250

def Declared.rise : Nat := 10

def Declared.stale : Nat := 20000000

def Declared.oldest : Nat := 25

def code : Policy → UInt64
  | .stand => 0
  | .walk => 1
  | .held => 2
  | .homing => 3
  | .sit => 4
  | .rise => 5
  | .kickLeft => 6
  | .kickRight => 7
  | .groundPick => 8
  | .roulade => 9
  | .other => 10

def flag (value : Bool) : UInt64 := if value then 1 else 0

def limited (limits : Limits) : UInt64 :=
  flag limits.deadman + 2 * flag limits.range + 4 * flag limits.finite + 8 * flag limits.other

def became : Option Outcome → UInt64
  | none => 0
  | some .executed => 1
  | some .unchanged => 2
  | some .refused => 3
  | some .unexecuted => 4
  | some .unanswered => 5

def Declared.upright : UInt64 := level Declared.share ⟨-950, by decide⟩

def upright (state : State) : Bool :=
  decide (level Declared.share (state.gravity.get 2) < Declared.upright)

def jointEntries (state : State) : List (Fin 256 × UInt64) :=
  (List.finRange 15).map fun joint =>
    (⟨joint.val, by omega⟩, level Declared.angle (state.joints.get joint))

def rateEntries : Option (Vector Host.Microduck.Declared.milli.Word 15) →
    List (Fin 256 × UInt64)
  | none => [(30, 0)]
  | some speeds => (30, 1) :: (List.finRange 15).map fun joint =>
      (⟨15 + joint.val, by omega⟩, level Declared.rate (speeds.get joint))

def trunkEntries (state : State) : List (Fin 256 × UInt64) :=
  ((List.finRange 3).map fun axis =>
      ((⟨31 + axis.val, by omega⟩ : Fin 256), level Declared.share (state.gravity.get axis))) ++
    ((List.finRange 3).map fun axis =>
      ((⟨34 + axis.val, by omega⟩ : Fin 256), level Declared.turn (state.gyro.get axis))) ++
    [(37, level Declared.rise state.height)]

def gainEntries : Option UInt16 → List (Fin 256 × UInt64)
  | none => [(41, 0)]
  | some gain => [(41, 1), (42, (gain.toNat / 8).toUInt64)]

def ageEntries : Option Nat → List (Fin 256 × UInt64)
  | none => [(44, 0)]
  | some age => [(44, 1), (45, (min (age / Declared.stale) Declared.oldest).toUInt64)]

def entries (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    List (Fin 256 × UInt64) :=
  jointEntries reading.state ++ rateEntries reading.state.speeds ++
    trunkEntries reading.state ++
    [(38, code reading.state.policy), (39, flag reading.state.fallen),
      (40, flag reading.state.limp)] ++
    gainEntries reading.state.gain ++ [(43, limited reading.state.limits)] ++
    ageEntries reading.age ++
    [(46, became outcome), (47, flag late)]

def words (reading : Reading) (outcome : Option Outcome) (late : Bool) : List SensorWord :=
  (entries reading outcome late).map fun entry => ⟨channel entry.1, entry.2⟩

def wordBound : Nat := 48

def shape : PatchShape := ⟨64, by decide, by decide⟩

def missing : UInt64 := 0xFFFF

def symbol (cell : Cell) : UInt64 :=
  if cell.status = 5 then 1 + (cell.distance.val.toNat / 100).toUInt64
  else 0x1000 + cell.status.toUInt64

def symbols : Option Depth → Patch shape
  | none => Vector.replicate 64 missing
  | some depth => depth.cells.map symbol

def Declared.near : Int := 300

def Declared.clear : Int := 400

def Declared.fresh : Nat := Declared.stale * Declared.oldest

def fresh (reading : Reading) : Bool :=
  reading.age.elim false fun age => decide (age < Declared.fresh)

def close (depth : Depth) : Bool :=
  (List.finRange 8).any fun row => (List.finRange 8).any fun column =>
    decide (row.val < 2) && (depth.zone row column).status == 5 &&
      decide ((depth.zone row column).distance.val < Declared.near)

def distant (depth : Depth) : Bool :=
  (List.finRange 8).all fun row => (List.finRange 8).all fun column =>
    !decide (row.val < 2) || (depth.zone row column).status == 255 ||
      ((depth.zone row column).status == 5 &&
        decide (Declared.clear ≤ (depth.zone row column).distance.val))

def near (reading : Reading) : Bool :=
  upright reading.state && fresh reading && reading.depth.elim false close

def clear (reading : Reading) : Bool :=
  upright reading.state && fresh reading && reading.depth.elim false distant

def achieved (armed : Bool) (reading : Reading) : Bool :=
  armed && near reading

def arm (armed : Bool) (reading : Reading) : Bool :=
  if near reading then false else armed || clear reading

abbrev signals : List Discount := [.g90, .g99, .g90, .g99]

def cumulants (reading : Reading) : Cumulants signals :=
  .cons (some .cumulants) (indicator (near reading)) <|
    .cons (some .cumulants) (indicator (near reading)) <|
      .cons (some .cumulants) (indicator reading.state.fallen) <|
        .cons (some .cumulants) (indicator reading.state.fallen) .nil

abbrev actions : Word.Count := ⟨10, by decide⟩

abbrev interface : Interface :=
  ⟨shape, signals, actions, wordBound, 0x50, .wallClock Host.Microduck.Declared.pace⟩

theorem channel_clear (index : Fin 256) : interface.reserved (channel index) = false := by
  have bound := index.isLt
  have apart : ¬(0x100 + index.val.toUInt64 - 0x50 : UInt64).toNat < 5 := by
    rw [UInt64.toNat_sub, UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    simp only [UInt64.toNat_ofNat]
    omega
  exact decide_eq_false apart

theorem words_length (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    (words reading outcome late).length ≤ wordBound := by
  have rates : (rateEntries reading.state.speeds).length ≤ 16 := by
    unfold rateEntries
    split <;> simp [List.length_finRange]
  have gain : (gainEntries reading.state.gain).length ≤ 2 := by
    unfold gainEntries
    split <;> simp
  have age : (ageEntries reading.age).length ≤ 2 := by
    unfold ageEntries
    split <;> simp
  simp only [words, entries, jointEntries, trunkEntries, wordBound, List.length_map,
    List.length_append, List.length_finRange, List.length_cons, List.length_nil]
  omega

theorem words_clear (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    ∀ word ∈ words reading outcome late, interface.reserved word.channel = false := by
  intro word member
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
  exact channel_clear entry.1

def frame (armed : Bool) (reading : Reading) (outcome : Option Outcome)
    (late : Bool) : Frame interface where
  words := words reading outcome late
  bounded := words_length reading outcome late
  clear := words_clear reading outcome late
  symbols := symbols reading.depth
  signals := cumulants reading
  potentials := Vector.replicate Acorn.FeatureConstants.skillCount false
  achieved := achieved armed reading

def percept (armed : Bool) (reading : Reading) (outcome : Option Outcome)
    (late : Bool) : Percept interface :=
  ⟨frame armed reading outcome late, indicator (achieved armed reading)⟩

theorem entries_distinct (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    ((entries reading outcome late).map Prod.fst).Nodup := by
  unfold entries
  cases reading.state.speeds <;> cases reading.state.gain <;> cases reading.age <;>
    simp only [jointEntries, rateEntries, trunkEntries, gainEntries, ageEntries,
      List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def] <;>
    decide

theorem symbol_valid (cell : Cell) : (symbol cell).toNat < 0x1000 ↔ cell.status = 5 := by
  have bounds : 0 ≤ cell.distance.val ∧ cell.distance.val ≤ 32767 := cell.distance.property
  have byte : cell.status.toNat < 256 := cell.status.toNat_lt
  unfold symbol
  split
  · rename_i valid
    refine ⟨fun _ => valid, fun _ => ?_⟩
    rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    simp only [UInt64.toNat_ofNat]
    omega
  · rename_i other
    refine ⟨fun small => ?_, fun valid => absurd valid other⟩
    rw [UInt64.toNat_add, UInt8.toNat_toUInt64] at small
    simp only [UInt64.toNat_ofNat] at small
    omega

theorem symbol_present (cell : Cell) : symbol cell ≠ missing := by
  have bounds : 0 ≤ cell.distance.val ∧ cell.distance.val ≤ 32767 := cell.distance.property
  have byte : cell.status.toNat < 256 := cell.status.toNat_lt
  intro same
  have value := congrArg UInt64.toNat same
  unfold symbol missing at value
  split at value
  · rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat'] at value
    simp only [UInt64.toNat_ofNat] at value
    omega
  · rw [UInt64.toNat_add, UInt8.toNat_toUInt64] at value
    simp only [UInt64.toNat_ofNat] at value
    omega

theorem symbols_missing (position : Fin shape.inputs) :
    (symbols none).get position = missing := by
  show (Vector.replicate 64 missing)[position.val]'position.isLt = missing
  exact Vector.getElem_replicate _

theorem symbols_zone (depth : Depth) (row column : Fin 8) :
    (symbols (some depth)).get ⟨row.val * 8 + column.val, by show _ < 64; omega⟩ =
      symbol (depth.zone row column) := by
  have inside : row.val * 8 + column.val < 64 := by omega
  show (depth.cells.map symbol)[row.val * 8 + column.val]'inside =
    symbol (depth.cells[row.val * 8 + column.val]'inside)
  exact Vector.getElem_map _ _

theorem symbol_close (cell : Cell) :
    (symbol cell).toNat ≤ 3 ↔ cell.status = 5 ∧ cell.distance.val < 300 := by
  have bounds : 0 ≤ cell.distance.val ∧ cell.distance.val ≤ 32767 := cell.distance.property
  have byte : cell.status.toNat < 256 := cell.status.toNat_lt
  unfold symbol
  split
  · rename_i valid
    rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    simp only [UInt64.toNat_ofNat]
    constructor
    · intro small
      exact ⟨valid, by omega⟩
    · rintro ⟨_, short⟩
      omega
  · rename_i other
    rw [UInt64.toNat_add, UInt8.toNat_toUInt64]
    simp only [UInt64.toNat_ofNat]
    constructor
    · intro small
      omega
    · rintro ⟨valid, _⟩
      exact absurd valid other

theorem symbol_distant (cell : Cell) :
    ((5 ≤ (symbol cell).toNat ∧ (symbol cell).toNat < 0x1000) ∨
        (symbol cell).toNat = 0x10FF) ↔
      (cell.status = 255 ∨ (cell.status = 5 ∧ 400 ≤ cell.distance.val)) := by
  have bounds : 0 ≤ cell.distance.val ∧ cell.distance.val ≤ 32767 := cell.distance.property
  have byte : cell.status.toNat < 256 := cell.status.toNat_lt
  unfold symbol
  split
  · rename_i valid
    have other : cell.status ≠ 255 := by rw [valid]; decide
    rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    simp only [UInt64.toNat_ofNat]
    constructor
    · intro wide
      exact Or.inr ⟨valid, by omega⟩
    · rintro (none | ⟨_, far⟩)
      · exact absurd none other
      · exact Or.inl (by omega)
  · rename_i other
    rw [UInt64.toNat_add, UInt8.toNat_toUInt64]
    simp only [UInt64.toNat_ofNat]
    constructor
    · intro wide
      exact Or.inl (UInt8.toNat_inj.mp (by show cell.status.toNat = 255; omega))
    · rintro (none | ⟨valid, _⟩)
      · exact Or.inr (by rw [none]; decide)
      · exact absurd valid other

theorem upright_iff (state : State) :
    upright state = true ↔ (state.gravity.get 2).val < -967 := by
  have bounds : -32767 ≤ (state.gravity.get 2).val ∧ (state.gravity.get 2).val ≤ 32767 :=
    (state.gravity.get 2).property
  unfold upright Declared.upright level
  rw [decide_eq_true_iff, UInt64.lt_iff_toNat_lt, Nat.toUInt64_eq, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  show ((state.gravity.get 2).val - -32767).toNat / 100 % 2 ^ 64 <
    ((-950 : Int) - -32767).toNat / 100 % 2 ^ 64 ↔ _
  omega

theorem fresh_level (reading : Reading) :
    fresh reading = true ↔
      ∃ age, reading.age = some age ∧
        min (age / Declared.stale) Declared.oldest < Declared.oldest := by
  unfold fresh
  cases reading.age with
  | none =>
    exact ⟨fun young => absurd young (by decide), fun ⟨_, absent, _⟩ => nomatch absent⟩
  | some age =>
    have cap : age < Declared.fresh ↔
        min (age / Declared.stale) Declared.oldest < Declared.oldest := by
      unfold Declared.fresh Declared.stale Declared.oldest
      omega
    show decide (age < Declared.fresh) = true ↔ _
    rw [decide_eq_true_iff, cap]
    constructor
    · intro capped
      exact ⟨age, rfl, capped⟩
    · rintro ⟨other, same, capped⟩
      rw [Option.some.inj same]
      exact capped

theorem near_iff (reading : Reading) :
    near reading = true ↔
      (reading.state.gravity.get 2).val < -967 ∧
        (∃ age, reading.age = some age ∧ age < Declared.fresh) ∧
          ∃ depth, reading.depth = some depth ∧ ∃ row column : Fin 8, row.val < 2 ∧
            (depth.zone row column).status = 5 ∧
              (depth.zone row column).distance.val < Declared.near := by
  rw [← upright_iff]
  unfold near fresh close
  cases reading.age <;> cases reading.depth <;>
    simp [and_assoc]

theorem clear_iff (reading : Reading) :
    clear reading = true ↔
      (reading.state.gravity.get 2).val < -967 ∧
        (∃ age, reading.age = some age ∧ age < Declared.fresh) ∧
          ∃ depth, reading.depth = some depth ∧ ∀ row column : Fin 8, row.val < 2 →
            (depth.zone row column).status = 255 ∨
              ((depth.zone row column).status = 5 ∧
                Declared.clear ≤ (depth.zone row column).distance.val) := by
  rw [← upright_iff]
  unfold clear fresh distant
  cases reading.age with
  | none => cases reading.depth <;> simp
  | some age =>
    cases reading.depth with
    | none => simp
    | some depth =>
      simp [or_assoc]
      constructor
      · rintro ⟨⟨tilt, young⟩, wide⟩
        exact ⟨tilt, young, fun row column top =>
          (wide row column).resolve_left (by omega)⟩
      · rintro ⟨tilt, young, wide⟩
        refine ⟨⟨tilt, young⟩, fun row column => ?_⟩
        rcases Nat.lt_or_ge row.val 2 with top | low
        · exact Or.inr (wide row column top)
        · exact Or.inl low

theorem near_symbols (reading : Reading) :
    near reading = true ↔
      (reading.state.gravity.get 2).val < -967 ∧
        (∃ age, reading.age = some age ∧ age < Declared.fresh) ∧
          ∃ position : Fin shape.inputs, position.val < 16 ∧
            ((symbols reading.depth).get position).toNat ≤ 3 := by
  rw [near_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨depth, paired, row, column, top, valid, short⟩
    refine ⟨⟨row.val * 8 + column.val, by show _ < 64; omega⟩,
      by show row.val * 8 + column.val < 16; omega, ?_⟩
    rw [paired, symbols_zone]
    exact (symbol_close _).mpr ⟨valid, short⟩
  · rintro ⟨position, top, small⟩
    have inside : position.val < 64 := position.isLt
    cases paired : reading.depth with
    | none =>
      rw [paired, symbols_missing] at small
      exact absurd small (by decide)
    | some depth =>
      have same : position = ⟨(position.val / 8) * 8 + position.val % 8,
          by show _ < 64; omega⟩ :=
        Fin.ext (by show position.val = position.val / 8 * 8 + position.val % 8; omega)
      rw [paired, same,
        symbols_zone depth ⟨position.val / 8, by omega⟩ ⟨position.val % 8, by omega⟩] at small
      exact ⟨depth, rfl, ⟨position.val / 8, by omega⟩, ⟨position.val % 8, by omega⟩,
        by show position.val / 8 < 2; omega, (symbol_close _).mp small⟩

theorem clear_symbols (reading : Reading) :
    clear reading = true ↔
      (reading.state.gravity.get 2).val < -967 ∧
        (∃ age, reading.age = some age ∧ age < Declared.fresh) ∧
          ∀ position : Fin shape.inputs, position.val < 16 →
            (5 ≤ ((symbols reading.depth).get position).toNat ∧
                ((symbols reading.depth).get position).toNat < 0x1000) ∨
              ((symbols reading.depth).get position).toNat = 0x10FF := by
  rw [clear_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨depth, paired, wide⟩ position top
    have inside : position.val < 64 := position.isLt
    have same : position = ⟨(position.val / 8) * 8 + position.val % 8,
        by show _ < 64; omega⟩ :=
      Fin.ext (by show position.val = position.val / 8 * 8 + position.val % 8; omega)
    rw [paired, same,
      symbols_zone depth ⟨position.val / 8, by omega⟩ ⟨position.val % 8, by omega⟩]
    exact (symbol_distant _).mpr
      (wide ⟨position.val / 8, by omega⟩ ⟨position.val % 8, by omega⟩
        (by show position.val / 8 < 2; omega))
  · intro wide
    cases paired : reading.depth with
    | none =>
      have first := wide ⟨0, by decide⟩ (by decide)
      rw [paired, symbols_missing] at first
      exact absurd first (by decide)
    | some depth =>
      refine ⟨depth, rfl, fun row column top => ?_⟩
      have zone := wide ⟨row.val * 8 + column.val, by show _ < 64; omega⟩
        (by show row.val * 8 + column.val < 16; omega)
      rw [paired, symbols_zone] at zone
      exact (symbol_distant _).mp zone

theorem near_clear (reading : Reading) (close : near reading = true) :
    clear reading = false := by
  obtain ⟨_, _, depth, paired, row, column, top, valid, short⟩ := (near_iff reading).mp close
  cases wide : clear reading with
  | false => rfl
  | true =>
    obtain ⟨_, _, other, same, far⟩ := (clear_iff reading).mp wide
    have equal : other = depth := Option.some.inj (same.symm.trans paired)
    rw [equal] at far
    rcases far row column top with none | ⟨_, long⟩
    · rw [valid] at none
      exact absurd none (by decide)
    · have short : (depth.zone row column).distance.val < 300 := short
      have long : (400 : Int) ≤ (depth.zone row column).distance.val := long
      omega

theorem achieved_iff (armed : Bool) (reading : Reading) :
    achieved armed reading = true ↔ armed = true ∧ near reading = true := by
  simp only [achieved, Bool.and_eq_true]

theorem arm_near (armed : Bool) (reading : Reading) (close : near reading = true) :
    arm armed reading = false := by
  unfold arm
  simp only [close, ↓reduceIte]

theorem arm_clear (armed : Bool) (reading : Reading) (wide : clear reading = true) :
    arm armed reading = true := by
  have apart : near reading = false := by
    cases close : near reading with
    | false => rfl
    | true => rw [near_clear reading close] at wide; exact absurd wide (by decide)
  unfold arm
  simp only [apart, wide, Bool.false_eq_true, ↓reduceIte, Bool.or_true]

theorem arm_keeps (armed : Bool) (reading : Reading) (apart : near reading = false)
    (narrow : clear reading = false) : arm armed reading = armed := by
  unfold arm
  simp only [apart, narrow, Bool.false_eq_true, ↓reduceIte, Bool.or_false]

theorem arm_held (armed : Bool) (first : Reading) (later : List Reading) (next : Reading)
    (close : near first = true) (narrow : ∀ reading ∈ later, clear reading = false) :
    achieved (later.foldl arm (arm armed first)) next = false := by
  have disarmed : later.foldl arm (arm armed first) = false := by
    rw [arm_near armed first close]
    clear close
    induction later with
    | nil => rfl
    | cons reading rest hold =>
      have stays : arm false reading = false := by
        unfold arm
        split
        · rfl
        · simp only [narrow reading List.mem_cons_self, Bool.or_false]
      rw [List.foldl_cons, stays]
      exact hold fun other member => narrow other (List.mem_cons_of_mem _ member)
  unfold achieved
  rw [disarmed]
  rfl

theorem entries_gravity (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    ((33 : Fin 256), level Declared.share (reading.state.gravity.get 2)) ∈
      entries reading outcome late := by
  have trunk : ((33 : Fin 256), level Declared.share (reading.state.gravity.get 2)) ∈
      trunkEntries reading.state := by
    unfold trunkEntries
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨2, List.mem_finRange 2, rfl⟩))
  unfold entries
  simp only [List.mem_append, trunk, or_true, true_or]

theorem entries_presence (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    ((30 : Fin 256), flag reading.state.speeds.isSome) ∈ entries reading outcome late ∧
      ((41 : Fin 256), flag reading.state.gain.isSome) ∈ entries reading outcome late ∧
        ((44 : Fin 256), flag reading.depth.isSome) ∈ entries reading outcome late := by
  rw [← Reading.age_present]
  unfold entries
  cases reading.state.speeds <;> cases reading.state.gain <;> cases reading.age <;>
    simp [rateEntries, gainEntries, ageEntries, flag]

private theorem entries_pos_cases (reading : Reading) (outcome : Option Outcome) (late : Bool)
    (position : Fin 256) (member : position ∈ (entries reading outcome late).map Prod.fst) :
    position.val < 15 ∨
      (reading.state.speeds.isSome = true ∧ 15 ≤ position.val ∧ position.val ≤ 29) ∨
      (30 ≤ position.val ∧ position.val ≤ 41) ∨
      (reading.state.gain.isSome = true ∧ position.val = 42) ∨
      position.val = 43 ∨ position.val = 44 ∨
      (reading.age.isSome = true ∧ position.val = 45) ∨
      position.val = 46 ∨ position.val = 47 := by
  unfold entries at member
  simp only [List.map_append, List.mem_append] at member
  rcases member with (((((((h | h) | h) | h) | h) | h) | h) | h)
  · unfold jointEntries at h
    simp only [List.map_map, List.mem_map] at h
    obtain ⟨j, -, rfl⟩ := h
    left; exact j.isLt
  · cases hs : reading.state.speeds with
    | none =>
      rw [hs] at h; unfold rateEntries at h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; right; right; left; decide
    | some speeds =>
      rw [hs] at h; unfold rateEntries at h
      simp only [List.map_cons, List.map_map, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨j, -, rfl⟩
      · right; right; left; decide
      · right; left; exact ⟨rfl, by show 15 ≤ 15 + j.val; omega,
          by show 15 + j.val ≤ 29; have := j.isLt; omega⟩
  · unfold trunkEntries at h
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, List.mem_append,
      List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at h
    right; right; left
    rcases h with (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩) | rfl
    · have := a.isLt; exact ⟨by show 30 ≤ 31 + a.val; omega, by show 31 + a.val ≤ 41; omega⟩
    · have := a.isLt; exact ⟨by show 30 ≤ 34 + a.val; omega, by show 34 + a.val ≤ 41; omega⟩
    · decide
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    right; right; left
    rcases h with rfl | rfl | rfl <;> decide
  · cases hg : reading.state.gain with
    | none =>
      rw [hg] at h; unfold gainEntries at h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; right; right; left; decide
    | some gain =>
      rw [hg] at h; unfold gainEntries at h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · right; right; left; decide
      · right; right; right; left; exact ⟨rfl, rfl⟩
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h; right; right; right; right; left; rfl
  · cases ha : reading.age with
    | none =>
      rw [ha] at h; unfold ageEntries at h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; right; right; right; right; right; left; rfl
    | some age =>
      rw [ha] at h; unfold ageEntries at h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · right; right; right; right; right; left; rfl
      · right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · right; right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; right; rfl

theorem entries_rates (reading : Reading) (outcome : Option Outcome) (late : Bool)
    (absent : reading.state.speeds = none) :
    ∀ position ∈ (entries reading outcome late).map Prod.fst,
      ¬(15 ≤ position.val ∧ position.val ≤ 29) := fun position member => by
  have h := entries_pos_cases reading outcome late position member
  rw [absent] at h
  simp only [Option.isSome_none, Bool.false_eq_true, false_and, false_or] at h
  omega

theorem entries_gain (reading : Reading) (outcome : Option Outcome) (late : Bool)
    (absent : reading.state.gain = none) :
    ∀ position ∈ (entries reading outcome late).map Prod.fst, position.val ≠ 42 := fun position member => by
  have h := entries_pos_cases reading outcome late position member
  rw [absent] at h
  simp only [Option.isSome_none, Bool.false_eq_true, false_and, false_or] at h
  omega

theorem entries_depth (reading : Reading) (outcome : Option Outcome) (late : Bool)
    (absent : reading.depth = none) :
    ∀ position ∈ (entries reading outcome late).map Prod.fst, position.val ≠ 45 := fun position member => by
  have ageless : reading.age = none := by
    unfold Reading.age
    rw [absent]
    rfl
  have h := entries_pos_cases reading outcome late position member
  rw [ageless] at h
  simp only [Option.isSome_none, Bool.false_eq_true, false_and, false_or] at h
  omega

theorem channel_injective (first second : Fin 256) (same : channel first = channel second) :
    first = second := by
  have left := first.isLt
  have right := second.isLt
  have value := congrArg UInt64.toNat same
  unfold channel at value
  rw [UInt64.toNat_add, UInt64.toNat_add, Nat.toUInt64_eq, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat'] at value
  simp only [UInt64.toNat_ofNat] at value
  exact Fin.ext (by omega)

theorem became_injective (first second : Option Outcome) (same : became first = became second) :
    first = second := by
  cases first with
  | none => cases second with
    | none => rfl
    | some other => cases other <;> exact absurd same (by decide)
  | some outcome => cases second with
    | none => cases outcome <;> exact absurd same (by decide)
    | some other => cases outcome <;> cases other <;> first | rfl | exact absurd same (by decide)

theorem interface_actions : interface.actions.word.toNat = 10 := rfl

theorem interface_timing : interface.timing = .wallClock Host.Microduck.Declared.pace := rfl

end Acorn.Handcrafted.Microduck
