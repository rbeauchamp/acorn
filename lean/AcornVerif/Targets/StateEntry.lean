/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Microduck
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Logic.Equiv.Defs

/-! # Targets of mission #200: how learned recurrent state enters the linear learners

A *target* is a statement that a mission is to prove, held as a definition of type `Prop`. This
module holds the contract of mission [#200](https://github.com/rbeauchamp/acorn/issues/200): its
definitions, in `AcornVerif.StateEntry`, and one target for each of its theorems, in
`AcornVerif.Targets.StateEntry`. A target is the theorem's statement with each binder written as
a leading arrow, `(name : type) →`, in the same order and of the same kind. Such an arrow means
what `∀` means; under `∀` Lean's unused-variable linter rejects a hypothesis whose name the
statement does not mention. Nothing here is proved; the mission is to prove each target.
`AcornVerif.Targets.registry` lists the targets.

The definitions are models over the reals except where they name an executed definition of
`Acorn.Handcrafted.Microduck`: `letterOf`, `closeCount`, `distantCount` and `steady` read an
executed reading, `topZones` takes its zones from the executed patch shape, and the targets
`arm_letter`, `fold_arm`, `near_threshold` and `clear_threshold` concern executed definitions.
Nothing here concerns Binary32 or a run of the agent.

The docstrings name the works a definition models. They are the sources the contract lists, with
the contract's equation numbers: Elsayed, Pham and Mahmood, *Streaming Recurrent Memory*,
arXiv:2610.34833v1 (2026), Eq. 6 (`rows`, a proxy that is not an instance of it); Elelimy, White,
Bowling and White, *Real-Time Recurrent Learning using Trace Units in Reinforcement Learning*,
NeurIPS 2024, arXiv:2409.01449, eq. (2) (`linearTrace`); Javed, Shah, Sutton and White, *Scalable
Real-Time Recurrent Learning Using Columnar-Constructive Networks*, JMLR 24 (2023), eqs. (11) to
(16) (`ColumnGates`, `column`). The prior-art review assesses the first in its entry INC-1 and the
third in INC-2. The contract requires the mission's own module to cite each with the equation it
reproduces.
-/

noncomputable section

namespace AcornVerif.StateEntry
open Acorn Acorn.Handcrafted

/-! ## The latch on letters, and the executed goal -/

/-- What a reading is to the goal's latch. -/
inductive Letter where
  /-- The reading meets the near test, which disarms. -/
  | near
  /-- The reading meets the clear test, which arms. -/
  | clear
  /-- The reading meets neither test, which holds. -/
  | neither
  deriving DecidableEq

/-- The set-reset step: near resets, clear sets, neither holds. -/
def latchStep (armed : Bool) : Letter → Bool
  | .near => false
  | .clear => true
  | .neither => armed

/-- The latch after a word, from a disarmed start. -/
def latch (word : List Letter) : Bool := word.foldl latchStep false

/-- The letter of a Microduck reading. -/
def letterOf (reading : Acorn.Host.Microduck.Reading) : Letter :=
  if Microduck.near reading then .near else if Microduck.clear reading then .clear else .neither

/-- The zones of the two top rows. -/
def topZones : List (Fin Microduck.shape.inputs) :=
  (List.finRange Microduck.shape.inputs).filter (·.val < 16)

/-- How many top zones hold a valid return under the near distance. -/
def closeCount (reading : Acorn.Host.Microduck.Reading) : ℕ :=
  topZones.countP fun position =>
    decide (((Microduck.symbols reading.depth).get position).toNat ≤ 3)

/-- How many top zones hold nothing in range or a valid return at the clear distance. -/
def distantCount (reading : Acorn.Host.Microduck.Reading) : ℕ :=
  topZones.countP fun position =>
    let symbol := ((Microduck.symbols reading.depth).get position).toNat
    decide ((5 ≤ symbol ∧ symbol < 0x1000) ∨ symbol = 0x10FF)

/-- One each for an upright trunk and a fresh depth frame. -/
def steady (reading : Acorn.Host.Microduck.Reading) : ℕ :=
  (if (reading.state.gravity.get 2).val < -967 then 1 else 0) +
    (if Microduck.fresh reading then 1 else 0)

/-! ## The acceptance predicate -/

/-- A recurrent mechanism over letters, with the real read an entry codes. -/
structure Mechanism (σ : Type) where
  /-- The state before any letter. -/
  start : σ
  /-- The write. -/
  step : σ → Letter → σ
  /-- The read. -/
  read : σ → ℝ

/-- The state after a word. -/
def Mechanism.run {σ : Type} (m : Mechanism σ) (word : List Letter) : σ :=
  word.foldl m.step m.start

/-- The word has no run of more than `hold` neither letters. -/
def HoldsWithin (hold : ℕ) (word : List Letter) : Prop :=
  ¬ List.replicate (hold + 1) Letter.neither <:+: word

/-- The read decides the latch across `edge` with `margin`, on every word whose holds are at
most `hold`, with the state within `bound` and the read `lip`-Lipschitz on that ball. Under the
family's norm, states with different latches are therefore at least `2 * margin / lip` apart. -/
structure Latches {σ : Type} [SeminormedAddCommGroup σ] (m : Mechanism σ)
    (hold : ℕ) (edge margin bound lip : ℝ) : Prop where
  /-- The margin is positive. -/
  positive : 0 < margin
  /-- The read is `lip`-Lipschitz on the ball of radius `bound`. -/
  lipschitz : ∀ s t, ‖s‖ ≤ bound → ‖t‖ ≤ bound → |m.read s - m.read t| ≤ lip * ‖s - t‖
  /-- On every word within the hold, the state is within `bound` and the read is on the latch's
  side of `edge` by `margin`. -/
  decides : ∀ word, HoldsWithin hold word →
    ‖m.run word‖ ≤ bound ∧
      (latch word = true → edge + margin ≤ m.read (m.run word)) ∧
      (latch word = false → m.read (m.run word) ≤ edge - margin)

/-- A family of mechanisms over trained parameters. -/
structure Family (Θ σ : Type) where
  /-- The state before any letter. -/
  start : Θ → σ
  /-- The write, under trained parameters. -/
  update : Θ → σ → Letter → σ
  /-- The read, under trained parameters. -/
  read : Θ → σ → ℝ

/-- The mechanism of trained parameters under one labelling of the letters. -/
def Family.labelled {Θ σ : Type} (family : Family Θ σ) (θ : Θ) (labels : Equiv.Perm Letter) :
    Mechanism σ where
  start := family.start θ
  step state letter := family.update θ state (labels letter)
  read := family.read θ

/-- **Acceptance at one hold.** Under every labelling of the three letters, some trained
parameters latch. The labelling is universal because nothing frozen may depend on which input
plays which part; only what is trained may. The parameters may depend on the hold. -/
def Family.Accepts {Θ σ : Type} [SeminormedAddCommGroup σ] (family : Family Θ σ)
    (hold : ℕ) (margin bound lip : ℝ) : Prop :=
  ∀ labels : Equiv.Perm Letter, ∃ θ edge,
    Latches (family.labelled θ labels) hold edge margin bound lip

/-- **Uniform acceptance.** Under every labelling, one setting of the trained parameters latches
at every hold, with one margin. -/
def Family.AcceptsUniformly {Θ σ : Type} [SeminormedAddCommGroup σ] (family : Family Θ σ)
    (margin bound lip : ℝ) : Prop :=
  ∀ labels : Equiv.Perm Letter, ∃ θ edge, ∀ hold,
    Latches (family.labelled θ labels) hold edge margin bound lip

/-! ## Three candidates -/

/-- A two-row proxy for the memory channel of Elsayed, Pham and Mahmood (2026), Eq. 6: trained
letter-dependent retention, a constant write and a read by difference. It is not an instance of
Eq. 6, whose write is a fixed random function of the input and whose memory starts at zero; it
isolates what retention alone can do. -/
def rows : Family (Letter → ℝ × ℝ) (ℝ × ℝ) where
  start _ := (1, 1)
  update θ state letter := ((θ letter).1 * state.1 + 1, (θ letter).2 * state.2 + 1)
  read _ state := state.1 - state.2

/-- Retention that erases the first row at near and the second at clear. -/
def rowGates (ρ ε : ℝ) : Letter → ℝ × ℝ
  | .near => (ε, ρ)
  | .clear => (ρ, ε)
  | .neither => (ρ, ρ)

/-- The linear recurrent trace unit of Elelimy, White, Bowling and White (2024), eq. (2) with the
identity for its output nonlinearity, as one complex state with rotation and decay `ζ`, written
from the current letter and read linearly. -/
def linearTrace (ζ : ℂ) : Family ((Letter → ℂ) × ℂ) ℂ where
  start _ := 0
  update θ state letter := ζ * state + θ.1 letter
  read θ state := (θ.2 * state).re

/-- The gates of a state-feedback column at one letter. -/
structure ColumnGates where
  /-- The forget gate, eq. (12) of Javed, Shah, Sutton and White (2023). -/
  forget : ℝ
  /-- The input gate, eq. (11). -/
  input : ℝ
  /-- The non-feedback part of the argument of eq. (14). -/
  offset : ℝ

/-- One column with a constant output gate `output` and a feedback weight of three: eqs. (14) to
(16) of Javed, Shah, Sutton and White (2023) with `h(t - 1) = output * tanh (c (t - 1))`, read
by a trained gain and bias. -/
def column (output : ℝ) : Family ((Letter → ColumnGates) × ℝ × ℝ) ℝ where
  start _ := -1 / 2
  update θ c letter :=
    (θ.1 letter).forget * c +
      (θ.1 letter).input * Real.tanh ((θ.1 letter).offset + 3 * (output * Real.tanh c))
  read θ c := θ.2.1 * (output * Real.tanh c) + θ.2.2

/-- Gates strictly inside the unit interval that hold, set and reset. -/
def columnGates : Letter → ColumnGates
  | .neither => ⟨1 / 2, 1 / 2, 0⟩
  | .clear => ⟨1 / 10, 9 / 10, 5⟩
  | .near => ⟨1 / 10, 9 / 10, -5⟩

/-! ## The read's own question -/

/-- The read is within `err` of its question's value at the latch, on every word within the hold. -/
def Tracks {σ : Type} (m : Mechanism σ) (hold : ℕ) (armed disarmed err : ℝ) : Prop :=
  ∀ word, HoldsWithin hold word →
    |m.read (m.run word) - if latch word then armed else disarmed| ≤ err

/-! ## The entry -/

/-- What a table can decode from a memoryless code: weights on the code's values that return the
latch, on every word within the hold. How a learner reaches such a table through hashed slots is
not modelled. -/
def Carried {σ α : Type} (code : ℝ → α) (m : Mechanism σ) (hold : ℕ) : Prop :=
  ∃ table : α → ℝ, ∀ word, HoldsWithin hold word →
    table (code (m.read (m.run word))) = if latch word then 1 else 0

/-- The existing feedback bucket, over the reals: `Acorn.Handcrafted.predictionBucket`. -/
def bucket (horizon value : ℝ) : ℕ :=
  min 8 ⌊max 0 (min 1 (value / horizon)) * 9⌋₊

/-- A level of the read at a constant mean and scale, cut at a width, within a closed range. A
running mean and scale are not modelled: a level taken at them fades across a hold. -/
def level (mean scale width : ℝ) (top : ℤ) (value : ℝ) : ℤ :=
  max (-top) (min top ⌊(value - mean) / (scale * width)⌋)

/-! ## The question whose value carries the latch -/

/-- The value of the reward question at an armed latch, on independent letters. -/
def armedValue (pNear pClear pNeither γ : ℝ) : ℝ :=
  pNear * (1 - γ + γ * pClear) / ((1 - γ) * (1 - γ * pNeither))

/-- The value of the reward question at a disarmed latch, on independent letters. -/
def disarmedValue (pNear pClear pNeither γ : ℝ) : ℝ :=
  pNear * (γ * pClear) / ((1 - γ) * (1 - γ * pNeither))

end AcornVerif.StateEntry

namespace AcornVerif.Targets.StateEntry
open Acorn Acorn.Handcrafted AcornVerif.StateEntry

/-! ## The latch on letters, and the executed goal -/

/-- The executed latch step is the set-reset step on the reading's letter. -/
def arm_letter : Prop :=
  (armed : Bool) → (reading : Acorn.Host.Microduck.Reading) →
    Microduck.arm armed reading = latchStep armed (letterOf reading)

/-- The executed latch over readings is the latch over their letters. -/
def fold_arm : Prop :=
  (readings : List Acorn.Host.Microduck.Reading) →
    readings.foldl Microduck.arm false = latch (readings.map letterOf)

/-- Near is a linear threshold of per-zone indicators, the upright test and the fresh test. -/
def near_threshold : Prop :=
  (reading : Acorn.Host.Microduck.Reading) →
    Microduck.near reading = true ↔ 35 ≤ closeCount reading + 17 * steady reading

/-- Clear is a linear threshold of per-zone indicators, the upright test and the fresh test. -/
def clear_threshold : Prop :=
  (reading : Acorn.Host.Microduck.Reading) →
    Microduck.clear reading = true ↔ 50 ≤ distantCount reading + 17 * steady reading

/-! ## The acceptance predicate -/

/-- A longer hold bound implies every shorter one, so no mechanism meets one hold length only. -/
def latches_mono : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → {m : Mechanism σ} → {hold : ℕ} →
    {edge margin bound lip : ℝ} → (held : Latches m (hold + 1) edge margin bound lip) →
    Latches m hold edge margin bound lip

/-- A mechanism whose next state ignores its state holds nothing. -/
def memoryless_refused : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (m : Mechanism σ) →
    (ignores : ∀ s t letter, m.step s letter = m.step t letter) → {hold : ℕ} →
    (positive : 1 ≤ hold) →
    (edge margin bound lip : ℝ) →
    ¬ Latches m hold edge margin bound lip

/-- A family with nothing trained at all is refused at every positive hold: exchanging near and
clear forces the two edges to contradict. -/
def frozen_refused : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (family : Family Unit σ) → {hold : ℕ} →
    (positive : 1 ≤ hold) → (margin bound lip : ℝ) →
    ¬ family.Accepts hold margin bound lip

/-! ## Fading state -/

/-- If the write contracts on the hold letter, the margin at a hold fades at the same rate. -/
def fading_margin : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (m : Mechanism σ) → {ρ : ℝ} →
    (nonnegative : 0 ≤ ρ) →
    (contracts : ∀ s t, ‖m.step s .neither - m.step t .neither‖ ≤ ρ * ‖s - t‖) →
    {hold : ℕ} → {edge margin bound lip : ℝ} → (held : Latches m hold edge margin bound lip) →
    margin ≤ lip * bound * ρ ^ hold

/-- A strict contraction on the hold letter has no margin that serves every hold. -/
def fading_no_uniform : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (m : Mechanism σ) → {ρ : ℝ} →
    (nonnegative : 0 ≤ ρ) → (below : ρ < 1) →
    (contracts : ∀ s t, ‖m.step s .neither - m.step t .neither‖ ≤ ρ * ‖s - t‖) →
    (edge margin bound lip : ℝ) →
    ¬ ∀ hold, Latches m hold edge margin bound lip

/-- A read additive over lags has its margin halved at each step of the hold, measured from the
difference the two event letters make at lag zero. -/
def additive_margin : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → (m : Mechanism σ) →
    (offset : ℕ → ℝ) → (term : Letter → ℕ → ℝ) →
    (additive : ∀ word, m.read (m.run word) = offset word.length +
      (word.reverse.zipIdx.map fun entry => term entry.1 entry.2).sum) →
    {hold : ℕ} → {edge margin bound lip : ℝ} → (held : Latches m hold edge margin bound lip) →
    margin ≤ |term .clear 0 - term .near 0| / 2 ^ (hold + 1)

/-! ## Three candidates -/

/-- The proxy holds every bounded hold, with a margin that fades with it, under every labelling. -/
def rows_accept : Prop :=
  {ρ ε : ℝ} → (positive : 0 < ε) → (below : ρ < 1) → (apart : ε / (1 - ρ) < ρ) →
    (hold : ℕ) →
    rows.Accepts hold (ρ ^ hold * (ρ - ε / (1 - ρ)) / 2) (1 / (1 - ρ)) 2

/-- Under a retention clamp no margin serves every hold, even when the trained parameters may
change with the hold. -/
def rows_clamped : Prop :=
  {ρ : ℝ} → (nonnegative : 0 ≤ ρ) → (below : ρ < 1) → (margin bound lip : ℝ) →
    ¬ ∀ hold, ∃ θ : Letter → ℝ × ℝ, ∃ edge,
      (∀ letter, |(θ letter).1| ≤ ρ ∧ |(θ letter).2| ≤ ρ) ∧
        Latches (rows.labelled θ (Equiv.refl Letter)) hold edge margin bound lip

/-- The unit's read is additive over lags. -/
def linearTrace_additive : Prop :=
  (ζ : ℂ) → (θ : (Letter → ℂ) × ℂ) → (labels : Equiv.Perm Letter) →
    (word : List Letter) →
    ((linearTrace ζ).labelled θ labels).read (((linearTrace ζ).labelled θ labels).run word) =
      (word.reverse.zipIdx.map fun entry =>
        (θ.2 * (ζ ^ entry.2 * θ.1 (labels entry.1))).re).sum

/-- The unit's margin at a hold is at most its scale over `2 ^ hold`, for every `ζ`, whatever the
decay and rotation. -/
def linearTrace_margin : Prop :=
  (ζ : ℂ) → (θ : (Letter → ℂ) × ℂ) → (labels : Equiv.Perm Letter) →
    {hold : ℕ} → {edge margin bound lip : ℝ} →
    (held : Latches ((linearTrace ζ).labelled θ labels) hold edge margin bound lip) →
    margin ≤ lip * bound / 2 ^ hold

/-- So no margin serves every hold, even when the trained parameters may change with the hold. -/
def linearTrace_refused : Prop :=
  (ζ : ℂ) → (labels : Equiv.Perm Letter) → (margin bound lip : ℝ) →
    ¬ ∀ hold, ∃ θ edge, Latches ((linearTrace ζ).labelled θ labels) hold edge margin bound lip

/-- At letters given exactly, one setting of the column holds every hold with one margin, under
every labelling. -/
def column_accepts : Prop :=
  {output : ℝ} → (large : 1 / 2 ≤ output) → (below : output < 1) →
    (column output).AcceptsUniformly (1 / 5) 1 1

/-! ## The read's own question -/

/-- A read that tracks two values more closely than half their gap decides the latch, with its
edge midway. -/
def tracks_decide : Prop :=
  {σ : Type} → {m : Mechanism σ} → {hold : ℕ} → {armed disarmed err : ℝ} →
    (tracks : Tracks m hold armed disarmed err) → (close : 2 * err < armed - disarmed) →
    ∀ word, HoldsWithin hold word →
      (latch word = true →
        (armed + disarmed) / 2 + ((armed - disarmed) / 2 - err) ≤ m.read (m.run word)) ∧
      (latch word = false →
        m.read (m.run word) ≤ (armed + disarmed) / 2 - ((armed - disarmed) / 2 - err))

/-- The column's trained read tracks any two values at every hold, under every labelling. -/
def column_tracks : Prop :=
  {output armed disarmed : ℝ} → (large : 1 / 2 ≤ output) → (below : output < 1) →
    (gap : disarmed < armed) → (labels : Equiv.Perm Letter) →
    ∃ θ, ∀ hold, Tracks ((column output).labelled θ labels) hold armed disarmed
      ((armed - disarmed) / 4)

/-! ## The entry -/

/-- A read that tracks a question's two values, both inside the first bucket, carries nothing
through the bucket. -/
def bucket_refuses : Prop :=
  {σ : Type} → (m : Mechanism σ) → (hold : ℕ) → {horizon armed disarmed err : ℝ} →
    (positive : 0 < horizon) → (tracks : Tracks m hold armed disarmed err) →
    (low : armed + err < horizon / 9) → (lowOther : disarmed + err < horizon / 9) →
    ¬ Carried (bucket horizon) m hold

/-- A latch whose margin spans one cell, with its edge inside the range, is carried by the level,
at every constant scale of the read. -/
def level_carries : Prop :=
  {σ : Type} → [SeminormedAddCommGroup σ] → {m : Mechanism σ} → {hold : ℕ} →
    {edge margin bound lip mean scale width : ℝ} → {top : ℤ} →
    (held : Latches m hold edge margin bound lip) → (positive : 0 < scale * width) →
    (spans : scale * width ≤ 2 * margin) → (range : 1 ≤ top) →
    (inside : (edge - margin - mean) / (scale * width) < top ∧
      (-top + 1 : ℝ) ≤ (edge + margin - mean) / (scale * width)) →
    Carried (level mean scale width top) m hold

/-- For a read with two values the mean always separates them, whatever their scale. -/
def two_values_levels : Prop :=
  {a b p scale width : ℝ} → {top : ℤ} → (ordered : a < b) → (above : 0 < p) →
    (under : p < 1) → (positive : 0 < scale * width) → (range : 1 ≤ top) →
    level (p * b + (1 - p) * a) scale width top a < level (p * b + (1 - p) * a) scale width top b

/-! ## The question whose value carries the latch -/

/-- Both values solve the question's Bellman equations, and they differ by the discounted chance
that the next event is near. -/
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

/-- At the reward question's horizon, events at a tenth of the steps each way leave both values
inside the first feedback bucket. -/
def values_first_bucket : Prop :=
  armedValue (1 / 10) (1 / 10) (8 / 10) (99 / 100) < 100 / 9 ∧
    disarmedValue (1 / 10) (1 / 10) (8 / 10) (99 / 100) < 100 / 9

end AcornVerif.Targets.StateEntry
