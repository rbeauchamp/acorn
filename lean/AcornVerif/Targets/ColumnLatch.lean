import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

namespace AcornVerif.ColumnLatch
open scoped BigOperators

variable {F : Type} {m : ℕ}

def sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

def score (input : F → Fin m → ℝ) (weights : Fin m → ℝ) (bias : ℝ) (frame : F) : ℝ :=
  (∑ j, weights j * input frame j) + bias

def latchStep (isSet isReset : F → Prop) (armed : Prop) (frame : F) : Prop :=
  ¬ isReset frame ∧ (armed ∨ isSet frame)

def latch (isSet isReset : F → Prop) (word : List F) : Prop :=
  word.foldl (latchStep isSet isReset) False

structure Separable (input : F → Fin m → ℝ) (isSet isReset : F → Prop) (range : ℝ) : Prop where
  exclusive : ∀ frame, ¬ (isSet frame ∧ isReset frame)
  witness : ∃ (setWeights resetWeights : Fin m → ℝ) (setBias resetBias : ℝ), ∀ frame,
    (isSet frame → 0 ≤ score input setWeights setBias frame) ∧
      (¬ isSet frame → score input setWeights setBias frame ≤ -1) ∧
      -range ≤ score input setWeights setBias frame ∧
      (isReset frame → 0 ≤ score input resetWeights resetBias frame) ∧
      (¬ isReset frame → score input resetWeights resetBias frame ≤ -1)

structure Gate (m : ℕ) where
  weights : Fin m → ℝ
  feedback : ℝ
  bias : ℝ

def Gate.arg (gate : Gate m) (input : Fin m → ℝ) (h : ℝ) : ℝ :=
  (∑ j, gate.weights j * input j) + gate.feedback * h + gate.bias

structure Cell (m : ℕ) where
  input : Gate m
  forget : Gate m
  output : Gate m
  write : Gate m

def Cell.step (θ : Cell m) (state : ℝ × ℝ) (x : Fin m → ℝ) : ℝ × ℝ :=
  let i := sigmoid (θ.input.arg x state.2)
  let f := sigmoid (θ.forget.arg x state.2)
  let o := sigmoid (θ.output.arg x state.2)
  let g := Real.tanh (θ.write.arg x state.2)
  let c := f * state.1 + i * g
  (c, o * Real.tanh c)

def Cell.run (θ : Cell m) (input : F → Fin m → ℝ) (word : List F) : ℝ × ℝ :=
  word.foldl (fun state frame => θ.step state (input frame)) (0, 0)

def frontStep (input : F → Fin m → ℝ) (setWeights resetWeights : Fin m → ℝ)
    (setBias resetBias gain : ℝ) (c : ℝ) (frame : F) : ℝ :=
  let a := sigmoid (gain * (score input setWeights setBias frame + 1 / 2))
  let b := sigmoid (gain * (score input resetWeights resetBias frame + 1 / 2))
  (1 / 10) * c + (9 / 10) * Real.tanh (6 * a - 6 * b + 3 * ((3 / 4) * Real.tanh c))

def tiedStep (i g c : ℝ) : ℝ := (1 - i) * c + i * g

def HoldsWithin (isEvent : F → Prop) (hold : ℕ) (word : List F) : Prop :=
  ¬ ∃ run : List F, run.length = hold + 1 ∧ run <:+: word ∧ ∀ frame ∈ run, ¬ isEvent frame

def tiedFrame (input : F → Fin m → ℝ) (eventWeights resetWeights : Fin m → ℝ)
    (eventBias resetBias gain : ℝ) (c : ℝ) (frame : F) : ℝ :=
  tiedStep (sigmoid (gain * (score input eventWeights eventBias frame + 1 / 2)))
    (Real.tanh (-gain * (2 * score input resetWeights resetBias frame + 1))) c

def meanStep (β h μ : ℝ) : ℝ := β * μ + (1 - β) * h

def varianceStep (β h μ v : ℝ) : ℝ := β * v + (1 - β) * (meanStep β h μ - h) * (μ - h)

def gridLevel (cells : ℕ) (h : ℝ) : ℤ := ⌊h * cells⌋

def envelopeStep (κ ε : ℝ) (range : ℝ × ℝ) (h : ℝ) : ℝ × ℝ :=
  let shrink := κ * max 0 (range.1 - range.2 - ε)
  (max h (range.1 - shrink), min h (range.2 + shrink))

def position (range : ℝ × ℝ) (h : ℝ) : ℝ := (h - range.2) / (range.1 - range.2)

end AcornVerif.ColumnLatch

namespace AcornVerif.Targets.ColumnLatch
open scoped BigOperators
open AcornVerif.ColumnLatch

def cell_accepts : Prop :=
  {F : Type} → {m : ℕ} →
    {input : F → Fin m → ℝ} → {isSet isReset : F → Prop} → {range : ℝ} →
    (positive : 0 ≤ range) → (separable : Separable input isSet isReset range) →
    ∃ (θ : Cell m) (edge : ℝ), ∀ word : List F,
      ‖θ.run input word‖ ≤ 2 ∧
        (latch isSet isReset word → edge + 1 / 3 ≤ (θ.run input word).2) ∧
        (¬ latch isSet isReset word → (θ.run input word).2 ≤ edge - 1 / 3)

def cell_bands : Prop :=
  {F : Type} → {m : ℕ} →
    {input : F → Fin m → ℝ} → {isSet isReset : F → Prop} → {range : ℝ} →
    (positive : 0 ≤ range) → (separable : Separable input isSet isReset range) →
    ∃ (θ : Cell m) (high : ℝ), 7 / 10 ≤ high ∧ ∀ word : List F,
      (latch isSet isReset word → |(θ.run input word).2 - high| ≤ 1 / 100) ∧
        (¬ latch isSet isReset word → |(θ.run input word).2| ≤ 1 / 100)

def read_lipschitz : Prop :=
  (s t : ℝ × ℝ) →
    |s.2 - t.2| ≤ ‖s - t‖

def threshold_trap : Prop :=
  (base : ℝ) → (shift : Fin 16 → ℝ) → {K tau : ℝ} →
    (clear : K ≤ base) →
    (others : ∀ S : Finset (Fin 16), S.Nonempty → |base + ∑ z ∈ S, shift z| ≤ tau) →
    K ≤ 3 * tau

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

def tied_bounded : Prop :=
  {i g c : ℝ} → (low : 0 ≤ i) → (high : i ≤ 1) → (write : |g| ≤ 1) → (state : |c| ≤ 1) →
    |tiedStep i g c| ≤ 1

def tied_fixed : Prop :=
  {i g c : ℝ} → (open_ : 0 < i) → (fixed : tiedStep i g c = c) →
    c = g

def tied_drift : Prop :=
  {e : ℝ} → (n : ℕ) → (gates : ℕ → ℝ) → (writes : ℕ → ℝ) → {c : ℝ} →
    (small : e ≤ 1) → (closed : ∀ t, 0 ≤ gates t ∧ gates t ≤ e) →
    (bounded : ∀ t, |writes t| ≤ 1) → (state : |c| ≤ 1) →
    |(List.range n).foldl (fun s t => tiedStep (gates t) (writes t) s) c - c| ≤ 2 * n * e

def tied_fades : Prop :=
  {i g : ℝ} → (n : ℕ) → (a b : ℝ) →
    (tiedStep i g)^[n] a - (tiedStep i g)^[n] b = (1 - i) ^ n * (a - b)

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

def tied_slope : Prop :=
  {i c : ℝ} → {g : ℝ → ℝ} → (low : 0 ≤ i) → (rising : Monotone g) →
    (smooth : DifferentiableAt ℝ g c) →
    1 - i ≤ deriv (fun x => tiedStep i (g x) x) c

def state_bound : Prop :=
  {limit forget gate write c : ℝ} → (nonnegative : 0 ≤ forget) →
    (below : forget ≤ limit) → (under : limit < 1) → (gateLow : 0 ≤ gate) → (gateHigh : gate ≤ 1) →
    (bounded : |write| ≤ 1) → (state : |c| ≤ 1 / (1 - limit)) →
    |forget * c + gate * write| ≤ 1 / (1 - limit)

def standardized_fades : Prop :=
  (β h μ v : ℝ) → (n : ℕ) →
    (meanStep β h)^[n] μ - h = β ^ n * (μ - h) ∧
      ((fun s : ℝ × ℝ => (meanStep β h s.1, varianceStep β h s.1 s.2))^[n] (μ, v)).2 =
        β ^ n * (v + (μ - h) ^ 2 * (1 - β ^ n))

def grid_carries : Prop :=
  {cells : ℕ} → (positive : 0 < cells) → {edge margin : ℝ} →
    (spans : 1 / (cells : ℝ) ≤ 2 * margin) → {α : Type} → (read : α → ℝ) → (armed : α → Prop) →
    (decides : ∀ a, (armed a → edge + margin ≤ read a) ∧ (¬ armed a → read a ≤ edge - margin)) →
    ∃ table : ℤ → Prop, ∀ a, table (gridLevel cells (read a)) ↔ armed a

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

def swing_bound : Prop :=
  {w b W hArmed hDisarmed armed disarmed err : ℝ} → (bounded : |w| ≤ W) →
    (tracksArmed : |w * hArmed + b - armed| ≤ err) →
    (tracksDisarmed : |w * hDisarmed + b - disarmed| ≤ err) →
    armed - disarmed - 2 * err ≤ W * |hArmed - hDisarmed|

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
