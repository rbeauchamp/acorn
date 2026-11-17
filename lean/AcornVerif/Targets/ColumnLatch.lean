/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Targets of mission #201: what a gated column holds from threshold letters

A *target* is an open statement held as a definition of type `Prop`. This module holds the
contract of mission [#201](https://github.com/rbeauchamp/acorn/issues/201): its definitions, in
`AcornVerif.ColumnLatch`, and one target for each of its theorems, in
`AcornVerif.Targets.ColumnLatch`. A target is the theorem's statement with its binders as leading
universal quantifiers, in the same order and of the same kind; a theorem that used the contract's
variables `F` and `m` binds them first. Nothing here is proved; the mission is to prove each
target. `AcornVerif.Targets.registry` lists the targets.

The definitions are models over the reals. Nothing here concerns Binary32, an update of any
parameter, or a run of the agent.

The docstrings name the work the definitions model, as the contract wrote them: Javed, Shah,
Sutton and White, *Scalable Real-Time Recurrent Learning Using Columnar-Constructive Networks*,
JMLR 24 (2023), eqs. (7), (10) and (11) to (16), with equation numbers of the JMLR paper. The
mission's own module cites each with the equation it reproduces.
-/

noncomputable section

namespace AcornVerif.ColumnLatch
open scoped BigOperators

variable {F : Type} {m : ℕ}

/-! ## The latch over frames whose letters are thresholds -/

/-- The logistic function of eqs. (11) to (13). -/
def sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- A weight vector and a bias applied to an input vector. -/
def score (input : F → Fin m → ℝ) (weights : Fin m → ℝ) (bias : ℝ) (frame : F) : ℝ :=
  (∑ j, weights j * input frame j) + bias

/-- The set-reset step over frames: a reset frame resets, a set frame sets, any other holds. -/
def latchStep (isSet isReset : F → Prop) (armed : Prop) (frame : F) : Prop :=
  ¬ isReset frame ∧ (armed ∨ isSet frame)

/-- The latch after a word of frames, from a disarmed start. -/
def latch (isSet isReset : F → Prop) (word : List F) : Prop :=
  word.foldl (latchStep isSet isReset) False

/-- The set and reset letters are exclusive thresholds of the input with a gap of one, and the
set score is bounded below by `range`. No frame needs to meet the set or reset letter exactly: an
additive score need not be small on the frames of neither letter. -/
structure Separable (input : F → Fin m → ℝ) (isSet isReset : F → Prop) (range : ℝ) : Prop where
  /-- No frame is both a set frame and a reset frame. -/
  exclusive : ∀ frame, ¬ (isSet frame ∧ isReset frame)
  /-- Weights and biases whose scores separate each letter from its complement with a gap of
  one, with the set score at least `-range`. -/
  witness : ∃ (setWeights resetWeights : Fin m → ℝ) (setBias resetBias : ℝ), ∀ frame,
    (isSet frame → 0 ≤ score input setWeights setBias frame) ∧
      (¬ isSet frame → score input setWeights setBias frame ≤ -1) ∧
      -range ≤ score input setWeights setBias frame ∧
      (isReset frame → 0 ≤ score input resetWeights resetBias frame) ∧
      (¬ isReset frame → score input resetWeights resetBias frame ≤ -1)

/-! ## The published cell -/

/-- The parameters of one gate of one column: the input weights, the feedback weight and the bias
of eqs. (11) to (14) of Javed, Shah, Sutton and White (2023). -/
structure Gate (m : ℕ) where
  /-- The weights on the input vector. -/
  weights : Fin m → ℝ
  /-- The weight on the column's previous output `h`. -/
  feedback : ℝ
  /-- The bias. -/
  bias : ℝ

/-- The argument of a gate. -/
def Gate.arg (gate : Gate m) (input : Fin m → ℝ) (h : ℝ) : ℝ :=
  (∑ j, gate.weights j * input j) + gate.feedback * h + gate.bias

/-- The four gates of one column. -/
structure Cell (m : ℕ) where
  /-- The input gate, eq. (11). -/
  input : Gate m
  /-- The forget gate, eq. (12). -/
  forget : Gate m
  /-- The output gate, eq. (13). -/
  output : Gate m
  /-- The write, eq. (14). -/
  write : Gate m

/-- One step of eqs. (11) to (16), on the state `(c, h)`. -/
def Cell.step (θ : Cell m) (state : ℝ × ℝ) (x : Fin m → ℝ) : ℝ × ℝ :=
  let i := sigmoid (θ.input.arg x state.2)
  let f := sigmoid (θ.forget.arg x state.2)
  let o := sigmoid (θ.output.arg x state.2)
  let g := Real.tanh (θ.write.arg x state.2)
  let c := f * state.1 + i * g
  (c, o * Real.tanh c)

/-- The state after a word of frames, from `c = h = 0`. -/
def Cell.run (θ : Cell m) (input : F → Fin m → ℝ) (word : List F) : ℝ × ℝ :=
  word.foldl (fun state frame => θ.step state (input frame)) (0, 0)

/-! ## The front layer -/

/-- A column with a saturating unit in front of its write, for each letter, inside one column: a
deep column of eq. (7), with constant gates and a constant output gate of three quarters. -/
def frontStep (input : F → Fin m → ℝ) (setWeights resetWeights : Fin m → ℝ)
    (setBias resetBias gain : ℝ) (c : ℝ) (frame : F) : ℝ :=
  let a := sigmoid (gain * (score input setWeights setBias frame + 1 / 2))
  let b := sigmoid (gain * (score input resetWeights resetBias frame + 1 / 2))
  (1 / 10) * c + (9 / 10) * Real.tanh (6 * a - 6 * b + 3 * ((3 / 4) * Real.tanh c))

/-! ## Tied gates -/

/-- The step of tied gates, `f = 1 - i` (eqs. (11), (12), (15)). -/
def tiedStep (i g c : ℝ) : ℝ := (1 - i) * c + i * g

/-- The word has no run of more than `hold` frames of neither letter. -/
def HoldsWithin (isEvent : F → Prop) (hold : ℕ) (word : List F) : Prop :=
  ¬ ∃ run : List F, run.length = hold + 1 ∧ run <:+: word ∧ ∀ frame ∈ run, ¬ isEvent frame

/-- A tied column whose input gate saturates on an event score, with a write that reads the reset
score, from a start at `-1`. -/
def tiedFrame (input : F → Fin m → ℝ) (eventWeights resetWeights : Fin m → ℝ)
    (eventBias resetBias gain : ℝ) (c : ℝ) (frame : F) : ℝ :=
  tiedStep (sigmoid (gain * (score input eventWeights eventBias frame + 1 / 2)))
    (Real.tanh (-gain * (2 * score input resetWeights resetBias frame + 1))) c

/-! ## What reaches the learners -/

/-- A running mean and variance of eq. (10) of Javed, Shah, Sutton and White (2023), one step at the
feature's value `h`. -/
def meanStep (β h μ : ℝ) : ℝ := β * μ + (1 - β) * h

/-- The variance step of eq. (10). -/
def varianceStep (β h μ v : ℝ) : ℝ := β * v + (1 - β) * (meanStep β h μ - h) * (μ - h)

/-- The level of a feature on a fixed grid of `cells` to the unit: no mean, no scale, no state. -/
def gridLevel (cells : ℕ) (h : ℝ) : ℤ := ⌊h * cells⌋

/-- One step of a range that follows a feature: it widens at once to hold the value, and otherwise
narrows at rate `κ`, never below the floor `ε`. -/
def envelopeStep (κ ε : ℝ) (range : ℝ × ℝ) (h : ℝ) : ℝ × ℝ :=
  let shrink := κ * max 0 (range.1 - range.2 - ε)
  (max h (range.1 - shrink), min h (range.2 + shrink))

/-- Where a value lies in a range. -/
def position (range : ℝ × ℝ) (h : ℝ) : ℝ := (h - range.2) / (range.1 - range.2)

end AcornVerif.ColumnLatch

namespace AcornVerif.Targets.ColumnLatch
open scoped BigOperators
open AcornVerif.ColumnLatch

/-! ## The published cell -/

/-- **One published cell holds the latch at every hold, from threshold letters.** One setting of
the parameters and one margin serve every word, with no restriction on its holds, from the zero
state, with the restoring force in the input gate's own feedback. -/
def cell_accepts : Prop :=
  {F : Type} → {m : ℕ} →
    {input : F → Fin m → ℝ} → {isSet isReset : F → Prop} → {range : ℝ} →
    (positive : 0 ≤ range) → (separable : Separable input isSet isReset range) →
    ∃ (θ : Cell m) (edge : ℝ), ∀ word : List F,
      ‖θ.run input word‖ ≤ 2 ∧
        (latch isSet isReset word → edge + 1 / 3 ≤ (θ.run input word).2) ∧
        (¬ latch isSet isReset word → (θ.run input word).2 ≤ edge - 1 / 3)

/-- The same setting keeps `h` in two narrow bands, which is what the word needs. -/
def cell_bands : Prop :=
  {F : Type} → {m : ℕ} →
    {input : F → Fin m → ℝ} → {isSet isReset : F → Prop} → {range : ℝ} →
    (positive : 0 ≤ range) → (separable : Separable input isSet isReset range) →
    ∃ (θ : Cell m) (high : ℝ), 7 / 10 ≤ high ∧ ∀ word : List F,
      (latch isSet isReset word → |(θ.run input word).2 - high| ≤ 1 / 100) ∧
        (¬ latch isSet isReset word → |(θ.run input word).2| ≤ 1 / 100)

/-- The read of `cell_accepts` is `h`, which is 1-Lipschitz in the state under the product norm. -/
def read_lipschitz : Prop :=
  (s t : ℝ × ℝ) →
    |s.2 - t.2| ≤ ‖s - t‖

/-! ## What additive input cannot do -/

/-- **The trap.** An additive function of sixteen zones that is at least `K` when every zone is in
its distant class and within `tau` of zero when any nonempty set of zones has left it has `K` at
most `3 * tau`. So input weights that set a write from a threshold letter move its argument by at
least a third as much on frames of neither letter: its feedback must dominate that, or something
must saturate in front of it. -/
def threshold_trap : Prop :=
  (base : ℝ) → (shift : Fin 16 → ℝ) → {K tau : ℝ} →
    (clear : K ≤ base) →
    (others : ∀ S : Finset (Fin 16), S.Nonempty → |base + ∑ z ∈ S, shift z| ≤ tau) →
    K ≤ 3 * tau

/-! ## The front layer -/

/-- The front layer holds every word at one margin, from a start in the disarmed basin. -/
def front_accepts : Prop :=
  {F : Type} → {m : ℕ} →
    {input : F → Fin m → ℝ} → {isSet isReset : F → Prop} →
    {setWeights resetWeights : Fin m → ℝ} → {setBias resetBias gain : ℝ} →
    (exclusive : ∀ frame, ¬ (isSet frame ∧ isReset frame)) →
    (separated : ∀ frame,
      (isSet frame → 0 ≤ score input setWeights setBias frame) ∧
        (¬ isSet frame → score input setWeights setBias frame ≤ -1) ∧
        (isReset frame → 0 ≤ score input resetWeights resetBias frame) ∧
        (¬ isReset frame → score input resetWeights resetBias frame ≤ -1)) →
    (large : 5 ≤ gain) → (word : List F) →
    let c := word.foldl (frontStep input setWeights resetWeights setBias resetBias gain) (-1 / 2)
    |c| ≤ 1 ∧ (latch isSet isReset word → 1 / 2 ≤ c) ∧ (¬ latch isSet isReset word → c ≤ -1 / 2)

/-! ## Tied gates -/

/-- Tied gates bound the state at every parameter: the step is a convex combination. -/
def tied_bounded : Prop :=
  {i g c : ℝ} → (low : 0 ≤ i) → (high : i ≤ 1) → (write : |g| ≤ 1) → (state : |c| ≤ 1) →
    |tiedStep i g c| ≤ 1

/-- A fixed point of the tied step with an open gate is its write. So the tied step restores only
through feedback in `g`. -/
def tied_fixed : Prop :=
  {i g c : ℝ} → (open_ : 0 < i) → (fixed : tiedStep i g c = c) →
    c = g

/-- A tied step with a closed gate moves the state by at most twice the gate, so a hold of `n` costs
at most `2 * n * e`. -/
def tied_drift : Prop :=
  {e : ℝ} → (n : ℕ) → (gates : ℕ → ℝ) → (writes : ℕ → ℝ) → {c : ℝ} →
    (small : e ≤ 1) → (closed : ∀ t, 0 ≤ gates t ∧ gates t ≤ e) →
    (bounded : ∀ t, |writes t| ≤ 1) → (state : |c| ≤ 1) →
    |(List.range n).foldl (fun s t => tiedStep (gates t) (writes t) s) c - c| ≤ 2 * n * e

/-- With the same gate and a write that ignores the state at every step of a hold, two runs of the
tied step approach each other at the gate's rate, so no margin serves every hold. -/
def tied_fades : Prop :=
  {i g : ℝ} → (n : ℕ) → (a b : ℝ) →
    (tiedStep i g)^[n] a - (tiedStep i g)^[n] b = (1 - i) ^ n * (a - b)

/-- Tied gates hold every word within a hold at one margin, when the gain has grown with the hold:
`(2 * hold + 4) * sigmoid (-gain / 2) ≤ 1 / 2`, so the gain grows as `2 * log hold`. -/
def tied_accepts : Prop :=
  {F : Type} → {m : ℕ} →
    {input : F → Fin m → ℝ} → {isSet isReset : F → Prop} →
    {eventWeights resetWeights : Fin m → ℝ} → {eventBias resetBias gain : ℝ} → {hold : ℕ} →
    (exclusive : ∀ frame, ¬ (isSet frame ∧ isReset frame)) →
    (separated : ∀ frame,
      ((isSet frame ∨ isReset frame) → 0 ≤ score input eventWeights eventBias frame) ∧
        (¬ (isSet frame ∨ isReset frame) → score input eventWeights eventBias frame ≤ -1) ∧
        (isReset frame → 0 ≤ score input resetWeights resetBias frame) ∧
        (¬ isReset frame → score input resetWeights resetBias frame ≤ -1)) →
    (large : (2 * (hold : ℝ) + 4) * sigmoid (-gain / 2) ≤ 1 / 2) → (word : List F) →
    (holds : HoldsWithin (fun frame => isSet frame ∨ isReset frame) hold word) →
    let c := word.foldl (tiedFrame input eventWeights resetWeights eventBias resetBias gain) (-1)
    |c| ≤ 1 ∧ (latch isSet isReset word → 1 / 2 ≤ c) ∧ (¬ latch isSet isReset word → c ≤ -1 / 2)

/-- **Tied gates with a front layer: one margin at every hold, and the state bounded at every
parameter.** On a frame of neither letter the write maps each basin into itself, so the step keeps
each basin for every value of the gate, however nearly closed. So the gate may stay nearly closed,
and the state's sensitivity across a hold then decays only at the gate's own rate. -/
def tiedFront_accepts : Prop :=
  {F : Type} → {m : ℕ} →
    {input : F → Fin m → ℝ} → {isSet isReset : F → Prop} →
    {setWeights resetWeights eventWeights : Fin m → ℝ} →
    {setBias resetBias eventBias frontGain eventGain : ℝ} →
    (exclusive : ∀ frame, ¬ (isSet frame ∧ isReset frame)) →
    (separated : ∀ frame,
      (isSet frame → 0 ≤ score input setWeights setBias frame) ∧
        (¬ isSet frame → score input setWeights setBias frame ≤ -1) ∧
        (isReset frame → 0 ≤ score input resetWeights resetBias frame) ∧
        (¬ isReset frame → score input resetWeights resetBias frame ≤ -1) ∧
        ((isSet frame ∨ isReset frame) → 0 ≤ score input eventWeights eventBias frame) ∧
        (¬ (isSet frame ∨ isReset frame) → score input eventWeights eventBias frame ≤ -1)) →
    (front : 10 ≤ frontGain) → (event : 4 ≤ eventGain) → (word : List F) →
    let step := fun (c : ℝ) (frame : F) =>
      tiedStep (sigmoid (eventGain * (score input eventWeights eventBias frame + 1 / 2)))
        (Real.tanh (6 * sigmoid (frontGain * (score input setWeights setBias frame + 1 / 2)) -
          6 * sigmoid (frontGain * (score input resetWeights resetBias frame + 1 / 2)) +
          (9 / 4) * Real.tanh c)) c
    let c := word.foldl step (-1 / 2)
    |c| ≤ 1 ∧ (latch isSet isReset word → 1 / 2 ≤ c) ∧ (¬ latch isSet isReset word → c ≤ -1 / 2)

/-- **The sensitivity of a tied step to its state is at least one minus the gate,** for a write
that does not fall as the state rises. So across a hold it decays no faster than the gate's rate. -/
def tied_slope : Prop :=
  {i c : ℝ} → {g : ℝ → ℝ} → (low : 0 ≤ i) → (rising : Monotone g) →
    (smooth : DifferentiableAt ℝ g c) →
    1 - i ≤ deriv (fun x => tiedStep i (g x) x) c

/-! ## The stored state, as corrected -/

/-- A forget gate scaled below `limit < 1` bounds the stored state at every parameter, whatever the
gates are. Without such a limit eq. (15) grows without bound as the forget gate tends to one. -/
def state_bound : Prop :=
  {limit forget gate write c : ℝ} → (nonnegative : 0 ≤ forget) →
    (below : forget ≤ limit) → (under : limit < 1) → (gateLow : 0 ≤ gate) → (gateHigh : gate ≤ 1) →
    (bounded : |write| ≤ 1) → (state : |c| ≤ 1 / (1 - limit)) →
    |forget * c + gate * write| ≤ 1 / (1 - limit)

/-! ## What reaches the learners -/

/-- **Eq. (10) fades across a hold.** While a feature holds one value for `n` steps, its running
mean less the value is `β ^ n` times the first such difference, and its running variance has the
closed form below, at every real `β`. So for `0 < β < 1` and a floor `ε > 0` on the scale, its
standardized value is at most `β ^ n * |μ - h| / ε` in size, and a level taken at a running mean and
scale has no margin that serves every hold, whatever the column does. -/
def standardized_fades : Prop :=
  (β h μ v : ℝ) → (n : ℕ) →
    (meanStep β h)^[n] μ - h = β ^ n * (μ - h) ∧
      ((fun s : ℝ × ℝ => (meanStep β h s.1, varianceStep β h s.1 s.2))^[n] (μ, v)).2 =
        β ^ n * (v + (μ - h) ^ 2 * (1 - β ^ n))

/-- A margin that spans one cell is carried by the fixed grid, at every hold the margin serves: some
table on levels returns the latch. -/
def grid_carries : Prop :=
  {cells : ℕ} → (positive : 0 < cells) → {edge margin : ℝ} →
    (spans : 1 / (cells : ℝ) ≤ 2 * margin) → {α : Type} → (read : α → ℝ) → (armed : α → Prop) →
    (decides : ∀ a, (armed a → edge + margin ≤ read a) ∧ (¬ armed a → read a ≤ edge - margin)) →
    ∃ table : ℤ → Prop, ∀ a, table (gridLevel cells (read a)) ↔ armed a

/-- **The position in the range serves every hold and every scale above the floor.** If a feature's
values lie within `r` of `high` when armed and of `low` when not, with `8 * r ≤ ε` and the range
starting inside those bands and at least `ε` wide, the position is at least 3/4 when armed and at
most 1/4 when not, after every word, however long the hold. -/
def envelope_decides : Prop :=
  {α : Type} → {κ ε r high low top bottom : ℝ} → (rate : 0 ≤ κ) → (slow : κ ≤ 1 / 2) →
    (floor : 0 < ε) → (ripple : 0 ≤ r) → (narrow : 8 * r ≤ ε) → (above : top ≤ high + r) →
    (below : low - r ≤ bottom) → (wide : ε ≤ top - bottom) → (value : α → ℝ) → (armed : α → Prop) →
    (bands : ∀ a, (armed a → |value a - high| ≤ r) ∧ (¬ armed a → |value a - low| ≤ r)) →
    (word : List α) → (now : α) →
    let range :=
      envelopeStep κ ε ((word.map value).foldl (envelopeStep κ ε) (top, bottom)) (value now)
    (armed now → 3 / 4 ≤ position range (value now)) ∧
      (¬ armed now → position range (value now) ≤ 1 / 4)

/-- **A read cannot track with a small swing when its weight is bounded.** If `w * h + b` is within
`err` of two values at two feature values, and `|w| ≤ W`, the feature's swing is at least the gap
less `2 * err`, over `W`. -/
def swing_bound : Prop :=
  {w b W hArmed hDisarmed armed disarmed err : ℝ} → (bounded : |w| ≤ W) →
    (tracksArmed : |w * hArmed + b - armed| ≤ err) →
    (tracksDisarmed : |w * hDisarmed + b - disarmed| ≤ err) →
    armed - disarmed - 2 * err ≤ W * |hArmed - hDisarmed|

/-- **The column's word carries the latch at every hold.** The one composition this file states: the
setting of `cell_bands`, with the range starting at `(1 / 8, 0)` and floor `1 / 8`, gives a position
at least 3/4 when armed and at most 1/4 when not, after every word. -/
def cell_word_decides : Prop :=
  {F : Type} → {m : ℕ} →
    {input : F → Fin m → ℝ} → {isSet isReset : F → Prop} → {range κ : ℝ} →
    (positive : 0 ≤ range) → (rate : 0 ≤ κ) → (slow : κ ≤ 1 / 2) →
    (separable : Separable input isSet isReset range) →
    ∃ θ : Cell m, ∀ (word : List F) (now : F),
      let values := fun w : List F => (θ.run input w).2
      let earlier := (List.range word.length).map fun n => values (word.take (n + 1))
      let current := values (word ++ [now])
      let held := envelopeStep κ (1 / 8) (earlier.foldl (envelopeStep κ (1 / 8)) (1 / 8, 0)) current
      (latch isSet isReset (word ++ [now]) → 3 / 4 ≤ position held current) ∧
        (¬ latch isSet isReset (word ++ [now]) → position held current ≤ 1 / 4)

/-! ## Microduck's counts -/

/-- With `close` and `distant` the counts of the sixteen top zones and `steady` the count of upright
and fresh, near is `35 ≤ close + 17 * steady` and clear is `50 ≤ distant + 17 * steady`. These
integer scores separate them with a gap of one, with the set score at least `-18`, and the event
score separates either letter from neither. -/
def counts_separated : Prop :=
  (close distant steady : ℕ) → (zones : close + distant ≤ 16) → (few : steady ≤ 2) →
    let set : ℤ := distant + steady - 18
    let reset : ℤ := close + 16 * steady - 33
    let event : ℤ := 17 * close + distant + 273 * steady - 562
    (50 ≤ distant + 17 * steady ↔ 0 ≤ set) ∧ (¬ (50 ≤ distant + 17 * steady) → set ≤ -1) ∧
      -18 ≤ set ∧
      (35 ≤ close + 17 * steady ↔ 0 ≤ reset) ∧ (¬ (35 ≤ close + 17 * steady) → reset ≤ -1) ∧
      ((35 ≤ close + 17 * steady ∨ 50 ≤ distant + 17 * steady) ↔ 0 ≤ event) ∧
      (¬ (35 ≤ close + 17 * steady ∨ 50 ≤ distant + 17 * steady) → event ≤ -1)

end AcornVerif.Targets.ColumnLatch
