import Acorn.Handcrafted.Microduck
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Logic.Equiv.Defs

noncomputable section

namespace AcornVerif.StateEntry
open Acorn Acorn.Handcrafted

inductive Letter where
  | near
  | clear
  | neither
  deriving DecidableEq

def latchStep (armed : Bool) : Letter → Bool
  | .near => false
  | .clear => true
  | .neither => armed

def latch (word : List Letter) : Bool := word.foldl latchStep false

def letterOf (reading : Acorn.Host.Microduck.Reading) : Letter :=
  if Microduck.near reading then .near else if Microduck.clear reading then .clear else .neither

def topZones : List (Fin Microduck.shape.inputs) :=
  (List.finRange Microduck.shape.inputs).filter (·.val < 16)

def closeCount (reading : Acorn.Host.Microduck.Reading) : ℕ :=
  topZones.countP fun position =>
    decide (((Microduck.symbols reading.depth).get position).toNat ≤ 3)

def distantCount (reading : Acorn.Host.Microduck.Reading) : ℕ :=
  topZones.countP fun position =>
    let symbol := ((Microduck.symbols reading.depth).get position).toNat
    decide ((5 ≤ symbol ∧ symbol < 0x1000) ∨ symbol = 0x10FF)

def steady (reading : Acorn.Host.Microduck.Reading) : ℕ :=
  (if (reading.state.gravity.get 2).val < -967 then 1 else 0) +
    (if Microduck.fresh reading then 1 else 0)

structure Mechanism (σ : Type) where
  start : σ
  step : σ → Letter → σ
  read : σ → ℝ

def Mechanism.run {σ : Type} (m : Mechanism σ) (word : List Letter) : σ :=
  word.foldl m.step m.start

def HoldsWithin (hold : ℕ) (word : List Letter) : Prop :=
  ¬ List.replicate (hold + 1) Letter.neither <:+: word

structure Latches {σ : Type} [SeminormedAddCommGroup σ] (m : Mechanism σ)
    (hold : ℕ) (edge margin bound lip : ℝ) : Prop where
  positive : 0 < margin
  lipschitz : ∀ s t, ‖s‖ ≤ bound → ‖t‖ ≤ bound → |m.read s - m.read t| ≤ lip * ‖s - t‖
  decides : ∀ word, HoldsWithin hold word →
    ‖m.run word‖ ≤ bound ∧
      (latch word = true → edge + margin ≤ m.read (m.run word)) ∧
      (latch word = false → m.read (m.run word) ≤ edge - margin)

structure Family (Θ σ : Type) where
  start : Θ → σ
  update : Θ → σ → Letter → σ
  read : Θ → σ → ℝ

def Family.labelled {Θ σ : Type} (family : Family Θ σ) (θ : Θ) (labels : Equiv.Perm Letter) :
    Mechanism σ where
  start := family.start θ
  step state letter := family.update θ state (labels letter)
  read := family.read θ

def Family.Accepts {Θ σ : Type} [SeminormedAddCommGroup σ] (family : Family Θ σ)
    (hold : ℕ) (margin bound lip : ℝ) : Prop :=
  ∀ labels : Equiv.Perm Letter, ∃ θ edge,
    Latches (family.labelled θ labels) hold edge margin bound lip

def Family.AcceptsUniformly {Θ σ : Type} [SeminormedAddCommGroup σ] (family : Family Θ σ)
    (margin bound lip : ℝ) : Prop :=
  ∀ labels : Equiv.Perm Letter, ∃ θ edge, ∀ hold,
    Latches (family.labelled θ labels) hold edge margin bound lip

def rows : Family (Letter → ℝ × ℝ) (ℝ × ℝ) where
  start _ := (1, 1)
  update θ state letter := ((θ letter).1 * state.1 + 1, (θ letter).2 * state.2 + 1)
  read _ state := state.1 - state.2

def rowGates (ρ ε : ℝ) : Letter → ℝ × ℝ
  | .near => (ε, ρ)
  | .clear => (ρ, ε)
  | .neither => (ρ, ρ)

def linearTrace (ζ : ℂ) : Family ((Letter → ℂ) × ℂ) ℂ where
  start _ := 0
  update θ state letter := ζ * state + θ.1 letter
  read θ state := (θ.2 * state).re

structure ColumnGates where
  forget : ℝ
  input : ℝ
  offset : ℝ

def column (output : ℝ) : Family ((Letter → ColumnGates) × ℝ × ℝ) ℝ where
  start _ := -1 / 2
  update θ c letter :=
    (θ.1 letter).forget * c +
      (θ.1 letter).input * Real.tanh ((θ.1 letter).offset + 3 * (output * Real.tanh c))
  read θ c := θ.2.1 * (output * Real.tanh c) + θ.2.2

def columnGates : Letter → ColumnGates
  | .neither => ⟨1 / 2, 1 / 2, 0⟩
  | .clear => ⟨1 / 10, 9 / 10, 5⟩
  | .near => ⟨1 / 10, 9 / 10, -5⟩

def Tracks {σ : Type} (m : Mechanism σ) (hold : ℕ) (armed disarmed err : ℝ) : Prop :=
  ∀ word, HoldsWithin hold word →
    |m.read (m.run word) - if latch word then armed else disarmed| ≤ err

def Carried {σ α : Type} (code : ℝ → α) (m : Mechanism σ) (hold : ℕ) : Prop :=
  ∃ table : α → ℝ, ∀ word, HoldsWithin hold word →
    table (code (m.read (m.run word))) = if latch word then 1 else 0

def bucket (horizon value : ℝ) : ℕ :=
  min 8 ⌊max 0 (min 1 (value / horizon)) * 9⌋₊

def level (mean scale width : ℝ) (top : ℤ) (value : ℝ) : ℤ :=
  max (-top) (min top ⌊(value - mean) / (scale * width)⌋)

def armedValue (pNear pClear pNeither γ : ℝ) : ℝ :=
  pNear * (1 - γ + γ * pClear) / ((1 - γ) * (1 - γ * pNeither))

def disarmedValue (pNear pClear pNeither γ : ℝ) : ℝ :=
  pNear * (γ * pClear) / ((1 - γ) * (1 - γ * pNeither))

end AcornVerif.StateEntry

namespace AcornVerif.Targets.StateEntry
open Acorn Acorn.Handcrafted AcornVerif.StateEntry

def arm_letter : Prop :=
  (armed : Bool) → (reading : Acorn.Host.Microduck.Reading) →
    Microduck.arm armed reading = latchStep armed (letterOf reading)

def fold_arm : Prop :=
  (readings : List Acorn.Host.Microduck.Reading) →
    readings.foldl Microduck.arm false = latch (readings.map letterOf)

def near_threshold : Prop :=
  (reading : Acorn.Host.Microduck.Reading) →
    Microduck.near reading = true ↔ 35 ≤ closeCount reading + 17 * steady reading

def clear_threshold : Prop :=
  (reading : Acorn.Host.Microduck.Reading) →
    Microduck.clear reading = true ↔ 50 ≤ distantCount reading + 17 * steady reading

def latches_mono : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → {m : Mechanism σ} → {hold : ℕ} →
    {edge margin bound lip : ℝ} → (held : Latches m (hold + 1) edge margin bound lip) →
    Latches m hold edge margin bound lip

def memoryless_refused : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (m : Mechanism σ) →
    (ignores : ∀ s t letter, m.step s letter = m.step t letter) → {hold : ℕ} →
    (positive : 1 ≤ hold) →
    (edge margin bound lip : ℝ) →
    ¬ Latches m hold edge margin bound lip

def frozen_refused : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (family : Family Unit σ) → {hold : ℕ} →
    (positive : 1 ≤ hold) → (margin bound lip : ℝ) →
    ¬ family.Accepts hold margin bound lip

def fading_margin : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (m : Mechanism σ) → {ρ : ℝ} →
    (nonnegative : 0 ≤ ρ) →
    (contracts : ∀ s t, ‖m.step s .neither - m.step t .neither‖ ≤ ρ * ‖s - t‖) →
    {hold : ℕ} → {edge margin bound lip : ℝ} → (held : Latches m hold edge margin bound lip) →
    margin ≤ lip * bound * ρ ^ hold

def fading_no_uniform : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (m : Mechanism σ) → {ρ : ℝ} →
    (nonnegative : 0 ≤ ρ) → (below : ρ < 1) →
    (contracts : ∀ s t, ‖m.step s .neither - m.step t .neither‖ ≤ ρ * ‖s - t‖) →
    (edge margin bound lip : ℝ) →
    ¬ ∀ hold, Latches m hold edge margin bound lip

def additive_margin : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (m : Mechanism σ) →
    (offset : ℕ → ℝ) → (term : Letter → ℕ → ℝ) →
    (additive : ∀ word, m.read (m.run word) = offset word.length +
      (word.reverse.zipIdx.map fun entry => term entry.1 entry.2).sum) →
    {hold : ℕ} → {edge margin bound lip : ℝ} → (held : Latches m hold edge margin bound lip) →
    margin ≤ |term .clear 0 - term .near 0| / 2 ^ (hold + 1)

def rows_accept : Prop :=
  {ρ ε : ℝ} → (positive : 0 < ε) → (below : ρ < 1) → (apart : ε / (1 - ρ) < ρ) →
    (hold : ℕ) →
    rows.Accepts hold (ρ ^ hold * (ρ - ε / (1 - ρ)) / 2) (1 / (1 - ρ)) 2

def rows_clamped : Prop :=
  {ρ : ℝ} → (nonnegative : 0 ≤ ρ) → (below : ρ < 1) → (margin bound lip : ℝ) →
    ¬ ∀ hold, ∃ θ : Letter → ℝ × ℝ, ∃ edge,
      (∀ letter, |(θ letter).1| ≤ ρ ∧ |(θ letter).2| ≤ ρ) ∧
        Latches (rows.labelled θ (Equiv.refl Letter)) hold edge margin bound lip

def linearTrace_additive : Prop :=
  (ζ : ℂ) → (θ : (Letter → ℂ) × ℂ) → (labels : Equiv.Perm Letter) →
    (word : List Letter) →
    ((linearTrace ζ).labelled θ labels).read (((linearTrace ζ).labelled θ labels).run word) =
      (word.reverse.zipIdx.map fun entry =>
        (θ.2 * (ζ ^ entry.2 * θ.1 (labels entry.1))).re).sum

def linearTrace_margin : Prop :=
  (ζ : ℂ) → (θ : (Letter → ℂ) × ℂ) → (labels : Equiv.Perm Letter) →
    {hold : ℕ} → {edge margin bound lip : ℝ} →
    (held : Latches ((linearTrace ζ).labelled θ labels) hold edge margin bound lip) →
    margin ≤ lip * bound / 2 ^ hold

def linearTrace_refused : Prop :=
  (ζ : ℂ) → (labels : Equiv.Perm Letter) → (margin bound lip : ℝ) →
    ¬ ∀ hold, ∃ θ edge, Latches ((linearTrace ζ).labelled θ labels) hold edge margin bound lip

def column_accepts : Prop :=
  {output : ℝ} → (large : 1 / 2 ≤ output) → (below : output < 1) →
    (column output).AcceptsUniformly (1 / 5) 1 1

def tracks_decide : Prop :=
  {σ : Type} → {m : Mechanism σ} → {hold : ℕ} → {armed disarmed err : ℝ} →
    (tracks : Tracks m hold armed disarmed err) → (close : 2 * err < armed - disarmed) →
    ∀ word, HoldsWithin hold word →
      (latch word = true →
        (armed + disarmed) / 2 + ((armed - disarmed) / 2 - err) ≤ m.read (m.run word)) ∧
      (latch word = false →
        m.read (m.run word) ≤ (armed + disarmed) / 2 - ((armed - disarmed) / 2 - err))

def column_tracks : Prop :=
  {output armed disarmed : ℝ} → (large : 1 / 2 ≤ output) → (below : output < 1) →
    (gap : disarmed < armed) → (labels : Equiv.Perm Letter) →
    ∃ θ, ∀ hold, Tracks ((column output).labelled θ labels) hold armed disarmed
      ((armed - disarmed) / 4)

def bucket_refuses : Prop :=
  {σ : Type} → (m : Mechanism σ) → (hold : ℕ) → {horizon armed disarmed err : ℝ} →
    (positive : 0 < horizon) → (tracks : Tracks m hold armed disarmed err) →
    (low : armed + err < horizon / 9) → (lowOther : disarmed + err < horizon / 9) →
    ¬ Carried (bucket horizon) m hold

def level_carries : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → {m : Mechanism σ} → {hold : ℕ} →
    {edge margin bound lip mean scale width : ℝ} → {top : ℤ} →
    (held : Latches m hold edge margin bound lip) → (positive : 0 < scale * width) →
    (spans : scale * width ≤ 2 * margin) → (range : 1 ≤ top) →
    (inside : (edge - margin - mean) / (scale * width) < top ∧
      (-top + 1 : ℝ) ≤ (edge + margin - mean) / (scale * width)) →
    Carried (level mean scale width top) m hold

def two_values_levels : Prop :=
  {a b p scale width : ℝ} → {top : ℤ} → (ordered : a < b) → (above : 0 < p) →
    (under : p < 1) → (positive : 0 < scale * width) → (range : 1 ≤ top) →
    level (p * b + (1 - p) * a) scale width top a < level (p * b + (1 - p) * a) scale width top b

def values_bellman : Prop :=
  {pNear pClear pNeither γ : ℝ} → (total : pNear + pClear + pNeither = 1) →
    (near : 0 ≤ pNear) → (clear : 0 ≤ pClear) → (neither : 0 ≤ pNeither) → (discount : 0 ≤ γ) →
    (below : γ < 1) →
    armedValue pNear pClear pNeither γ =
        pNear * (1 + γ * disarmedValue pNear pClear pNeither γ) +
          (pClear + pNeither) * (γ * armedValue pNear pClear pNeither γ) ∧
      disarmedValue pNear pClear pNeither γ =
        (pNear + pNeither) * (γ * disarmedValue pNear pClear pNeither γ) +
          pClear * (γ * armedValue pNear pClear pNeither γ) ∧
      armedValue pNear pClear pNeither γ - disarmedValue pNear pClear pNeither γ =
        pNear / (1 - γ * pNeither)

def values_first_bucket : Prop :=
  armedValue (1 / 10) (1 / 10) (8 / 10) (99 / 100) < 100 / 9 ∧
    disarmedValue (1 / 10) (1 / 10) (8 / 10) (99 / 100) < 100 / 9

end AcornVerif.Targets.StateEntry
