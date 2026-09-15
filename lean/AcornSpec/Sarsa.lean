/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Rng
import AcornSpec.Learner

/-!
# Executable specification: Swift-Sarsa

Mirrors `src/agent/sarsa.rs`: one `SwiftTD` learner per action; a shared TD
error and a shared `vδ` accumulator; all learners run the first loop, only
the chosen action's learner runs the second; SMDP updates bootstrap with
`γᵏ` and decay traces by `(γλ)ᵏ`; the terminal update runs only the first
loop and then clears every transient register.

Selection (`greedy` tie-breaking, `uniform`, ε-greedy) consumes the caller's
RNG stream in exactly the Rust draw order: the greedy tie-break draws once
per within-window candidate — the first included.
-/

namespace AcornSpec

/-- `sarsa::SwiftSarsa` — `learners.size` per-action learners plus shared
lagged state. -/
structure Sarsa where
  /-- One learner per action, in action order. -/
  learners : Array SwiftTd
  /-- Shared configuration (identical to every learner's). -/
  cfg : SwiftCfg
  /-- Previous prediction of the previously chosen action (bits). -/
  vOld : UInt32
  /-- Shared δw·φ accumulator (bits). -/
  vDelta : UInt32

namespace Sarsa

/-- A placeholder learner for the take-out update pattern; never observed. -/
def dummySwift : SwiftTd :=
  { cfg := SwiftCfg.control .g99
    w := #[], beta := #[], z := #[], zDelta := #[], deltaW := #[]
    h := #[], hOld := #[], hTemp := #[], zBar := #[], p := #[], lastAlpha := #[]
    eligible := #[], vDelta := 0, vOld := 0 }

/-- Take a learner out of the array, update it, put it back — keeps the
learner uniquely referenced so its arrays update in place. -/
@[inline]
def modifyLearner (a : Array SwiftTd) (j : Nat) (f : SwiftTd → SwiftTd) :
    Array SwiftTd :=
  let l := a[j]!
  let a := a.set! j dummySwift
  a.set! j (f l)

/-- A placeholder controller for the take-out update pattern; never
observed. -/
def dummySarsa : Sarsa :=
  { learners := #[], cfg := SwiftCfg.control .g99, vOld := 0, vDelta := 0 }

/-- `SwiftSarsa::new` — `m` identical fresh learners. -/
def new (m : Nat) (cfg : SwiftCfg) : Sarsa :=
  { learners := Array.ofFn (n := m) (fun _ => SwiftTd.new cfg)
    cfg, vOld := 0, vDelta := 0 }

/-- `SwiftSarsa::predict_all`. -/
def predictAll (s : Sarsa) (features : Array UInt32) : Array Float32 :=
  s.learners.map (fun l => l.predict features)

/-- Shared update core: the TD error is supplied by the caller (`step`,
`smdp_step`), every learner runs the first loop with the shared accumulator
and the given trace decay, then the chosen action's learner runs the second
loop. -/
private def updateCore (s : Sarsa) (features : Array UInt32) (action : Nat)
    (delta traceDecay newVOld : Float32) : Sarsa :=
  let vDelta := Float32.ofBits s.vDelta
  let ⟨learners, cfg, _, _⟩ := s
  let n := learners.size
  let learners := Id.run do
    let mut ls := learners
    for j in [0:n] do
      ls := modifyLearner ls j (fun l => l.learnFirstLoop delta vDelta traceDecay)
    pure ls
  let l := learners[action]!
  let learners := learners.set! action dummySwift
  let (l, vd) := l.learnSecondLoop features f32zero
  let learners := learners.set! action l
  ⟨learners, cfg, newVOld.toBits, vd.toBits⟩

/-- `SwiftSarsa::step` — one ordinary update for the chosen action. Returns
the controller and the pre-update action values. -/
def step (s : Sarsa) (features : Array UInt32) (action : Nat) (reward : Float32) :
    Sarsa × Array Float32 :=
  let vals := s.predictAll features
  let gamma := s.cfg.gamma
  let lambda := Float32.ofBits s.cfg.lambda
  let vOld := Float32.ofBits s.vOld
  let delta := reward + gamma * vals[action]! - vOld
  let s := s.updateCore features action delta (gamma * lambda) vals[action]!
  (s, vals)

/-- `SwiftSarsa::smdp_step` — an SMDP update over a `k`-step gap. -/
def smdpStep (s : Sarsa) (features : Array UInt32) (action : Nat)
    (cumReward : Float32) (k : UInt32) : Sarsa × Array Float32 :=
  let gamma := s.cfg.gamma
  let lambda := Float32.ofBits s.cfg.lambda
  let gk := pow32 gamma k
  let tk := pow32 (gamma * lambda) k
  let vals := s.predictAll features
  let vOld := Float32.ofBits s.vOld
  let delta := cumReward + gk * vals[action]! - vOld
  let s := s.updateCore features action delta tk vals[action]!
  (s, vals)

/-- `SwiftSarsa::terminal_step` — close the trajectory: first loop only, then
clear all transient state. -/
def terminalStep (s : Sarsa) (reward : Float32) : Sarsa :=
  let gamma := s.cfg.gamma
  let lambda := Float32.ofBits s.cfg.lambda
  let vOld := Float32.ofBits s.vOld
  let vDelta := Float32.ofBits s.vDelta
  let delta := reward - vOld
  let ⟨learners, cfg, _, _⟩ := s
  let n := learners.size
  let learners := Id.run do
    let mut ls := learners
    for j in [0:n] do
      ls := modifyLearner ls j
        (fun l => (l.learnFirstLoop delta vDelta (gamma * lambda)).clearTransient)
    pure ls
  ⟨learners, cfg, 0, 0⟩

/-- `SwiftSarsa::clear_transient`. -/
def clearTransient (s : Sarsa) : Sarsa :=
  let ⟨learners, cfg, _, _⟩ := s
  let n := learners.size
  let learners := Id.run do
    let mut ls := learners
    for j in [0:n] do
      ls := modifyLearner ls j (fun l => l.clearTransient)
    pure ls
  ⟨learners, cfg, 0, 0⟩

/-- `SwiftSarsa::plan_step` (PAR-14) — planning update on action `action`'s learner. -/
def planStep (s : Sarsa) (action : Nat) (features : Array UInt32) (target : Float32) :
    Sarsa × Float32 :=
  if action < s.learners.size then
    let l := s.learners[action]!
    let (l, err) := l.planStep features target
    let learners := s.learners.set! action dummySwift
    ({ s with learners := learners.set! action l }, err)
  else
    (s, f32zero)

/-- `SwiftSarsa::greedy` — arg-max with pseudorandom tie-breaking inside the
`best − 1e-6` window; one `next_below` draw per within-window candidate, the
first included. -/
def greedy (vals : Array Float32) (rng : Xoshiro256) : Nat × Xoshiro256 :=
  let best := (vals.foldl (fun b v => if b < v then v else b) vals[0]!)
  let window := best - Float32.ofBits Constants.tie1e6Bits
  Id.run do
    let mut ties : UInt64 := 0
    let mut pick : Nat := 0
    let mut g := rng
    for j in [0:vals.size] do
      if window ≤ vals[j]! then
        ties := ties + 1
        let (d, g') := g.nextBelow ties
        g := g'
        if d == 0 then
          pick := j
    pure (pick, g)

/-- `SwiftSarsa::uniform` — one `next_below m` draw. -/
@[inline]
def uniform (m : UInt64) (rng : Xoshiro256) : Nat × Xoshiro256 :=
  let (d, g) := rng.nextBelow m
  (d.toNat, g)

/-- `SwiftSarsa::explore_rate` — the mean of ν(β) over the concatenation of
the action learners' eligible sets, or ν(ln α_init) when none is eligible.
Projected into `[0, 1]`, mirroring `ExploreRate::set`. -/
def exploreRate (s : Sarsa) : Float32 :=
  let (sum, count) := s.learners.foldl
    (fun (acc : Float32 × Nat) l =>
      let (sm, n) := l.normalizedStepSizeSum
      (acc.1 + sm, acc.2 + n)) (f32zero, 0)
  let raw :=
    if count == 0 then s.learners[0]!.initialNormalizedStepSize
    else sum / natF32 count
  saturate raw f32zero (natF32 1)

/-- `SwiftSarsa::epsilon_greedy_choice`, decision half only: the declared
probability array is observational (it feeds the decision trace, never the
stream) and is omitted. Draw order: one `next_f64` comparison, then either
`uniform` or `greedy`. -/
def epsilonGreedyChoice (vals : Array Float32) (eps : Float32) (rng : Xoshiro256) :
    Nat × Xoshiro256 :=
  -- No projection: the rate arrives from `exploreRate`, already in `[0, 1]`,
  -- mirroring Rust's `ExploreRate` type invariant.
  let (u, rng) := rng.next
  let draw := UInt64.toFloat (u >>> 11) * (natF64 1 / UInt64.toFloat ((1 : UInt64) <<< 53))
  let explored := draw < widen eps
  if explored then uniform vals.size.toUInt64 rng
  else greedy vals rng

end Sarsa

end AcornSpec
