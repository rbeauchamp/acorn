/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Policy
import Acorn.FeatureConstants

/-!
# Bounded persistent exploration

Dabney, Ostrovski & Barreto, *Temporally-Extended ε-Greedy Exploration*,
ICLR (2021), arXiv:2006.01782v1 (2020), §4.2, PDF p. 5 and Algorithm 1,
PDF p. 14. Acorn's D3 sampler uses the capped reciprocal tail, not the exact
zeta distribution. It serves n total actions as in §4.2; Algorithm 1's n+1
loop is characterized separately by the retained mathematical owner.
The seeded generator is deterministic. Nominal epsilon observations do not
assert independent uniform draws or exact finite-word probabilities.
-/
namespace Acorn.Features

/-- Current primitive action count with its machine-width admission. -/
def primitiveCount : Word.Count := ⟨Acorn.FeatureConstants.primitiveCount.toUInt64, by decide⟩

/-- Current meta action count with its machine-width admission. -/
def metaCount : Word.Count := ⟨Acorn.FeatureConstants.metaActionCount.toUInt64, by decide⟩

/-- D3 fixes persistence to at most 128 primitive actions. -/
def explorationCap : Nat := Acorn.FeatureConstants.explorationMaxDuration

/-- A sampled run stores only its remaining actions after the returned first action. -/
structure ExploratoryRun (count : Word.Count) where
  /-- The receiving action space owns admission for the whole run. -/
  action : Action count.word.toNat
  /-- At most cap minus one actions remain. -/
  remaining : Fin explorationCap

instance (count : Word.Count) : Provenance (ExploratoryRun count) := ⟨some .explorationDuration⟩

/-- Serve one committed action without drawing or consulting a value function.
Spent runs produce no action; the caller resumes boundary selection. -/
def ExploratoryRun.serve {count : Word.Count} (run : ExploratoryRun count) :
    Option (Action count.word.toNat × ExploratoryRun count) :=
  if h : 0 < run.remaining.val then
    some (run.action, ⟨run.action, ⟨run.remaining.val - 1, by have := run.remaining.isLt; omega⟩⟩)
  else none

/-- An actual continuation repeats its committed action and reduces the clock by one. -/
theorem ExploratoryRun.serve_exact {count : Word.Count} (run next : ExploratoryRun count)
    (action : Action count.word.toNat) (served : run.serve = some (action, next)) :
    action = run.action ∧ next.action = run.action ∧ next.remaining.val + 1 = run.remaining.val := by
  unfold serve at served
  split at served
  · cases served
    exact ⟨rfl, rfl, by dsimp; omega⟩
  · contradiction

/-- No hidden extra action exists after the remaining clock reaches zero. -/
theorem ExploratoryRun.spent {count : Word.Count} (run : ExploratoryRun count) :
    run.serve = none ↔ run.remaining.val = 0 := by simp [serve]

/-- Reciprocal draw in the actual binary64 operation order. Truncation reads
the nonnegative finite dyadic fields; the stored remainder is capped at admission.
On the RNG's [0,1) range this is floor(1/(1-u)) minus the first served action. -/
def durationRemainingSpec (uniform : Binary64) : Fin explorationCap :=
  let one := Binary64.ofUInt64 1
  let reciprocal := one.div (one.sub uniform)
  let duration := if !(reciprocal.less (Binary64.ofUInt64 explorationCap.toUInt64)) then
    explorationCap else (Conversion.trunc64 reciprocal).toNat
  ⟨min (duration - 1) (explorationCap - 1), by
    have := Nat.min_le_right (duration - 1) (explorationCap - 1)
    simp only [explorationCap, Acorn.FeatureConstants.explorationMaxDuration] at *
    omega⟩

/-- Word duration classification preserves the draw's native operation order. -/
def durationCountWord (uniform : Binary64) : UInt32 :=
  let one := Binary64.ofUInt64 1
  let reciprocal := one.div (one.sub uniform)
  if !(reciprocal.less (Binary64.ofUInt64 explorationCap.toUInt64)) then 128
  else Conversion.cappedTrunc128 reciprocal

/-- Duration classification always fits the declared exploration cap. -/
theorem durationCountWord_bound (uniform : Binary64) :
    (durationCountWord uniform).toNat ≤ 128 := by
  dsimp only [durationCountWord]
  split
  · decide
  · rw [Conversion.cappedTrunc128_exact]
    exact Nat.min_le_right _ _

/-- Serve the first action before storing the scalar remaining clock. -/
def durationWord (uniform : Binary64) : UInt32 :=
  let count := durationCountWord uniform
  if count = 0 then 0 else count - 1

/-- Saturating word subtraction removes exactly the first served action. -/
theorem durationWord_exact (uniform : Binary64) :
    (durationWord uniform).toNat = (durationCountWord uniform).toNat - 1 := by
  dsimp only [durationWord]
  split
  · rename_i zero
    simp [zero]
  · rename_i nonzero
    rw [UInt32.toNat_sub_of_le]
    · rfl
    · rw [UInt32.le_iff_toNat_le]
      have : (durationCountWord uniform).toNat ≠ 0 := by
        intro h
        exact nonzero (UInt32.toNat.inj h)
      change 1 ≤ _
      omega

/-- The executing bounded clock leaves word storage only at its Fin boundary. -/
def durationRemaining (uniform : Binary64) : Fin explorationCap :=
  ⟨(durationWord uniform).toNat, by
    rw [durationWord_exact]
    have := durationCountWord_bound uniform
    change _ < 128
    omega⟩

/-- Early capping preserves the stored remainder over every raw draw, without
assuming the caller supplied an RNG-range value. -/
theorem durationRemaining_eq_spec (uniform : Binary64) :
    durationRemaining uniform = durationRemainingSpec uniform := by
  apply Fin.ext
  simp only [durationRemaining, durationWord_exact, durationCountWord, durationRemainingSpec]
  split
  · rfl
  · rw [Conversion.cappedTrunc128_exact]
    simp only [explorationCap, Acorn.FeatureConstants.explorationMaxDuration]
    omega

/-- Branch, duration, then action: the same draw order at every primitive boundary. -/
def beginExploration (count : Word.Count) (rate : SwiftTd.ExploreRate) (rng : Rng.Xoshiro256) :
    Option (ExploratoryRun count) × Rng.Xoshiro256 :=
  let branch := rng.nextF64
  if !(branch.1.less (Conversion.widen rate.value)) then (none, branch.2) else
    let duration := branch.2.nextF64
    let action := uniformAction count duration.2
    (some ⟨action.1, durationRemaining duration.1⟩, action.2)

/-- A primitive boundary draw retains its nominal snapshot and possible continuation. -/
structure PersistentDecision (count : Word.Count) where
  /-- The actual admitted action. -/
  action : Action count.word.toNat
  /-- True only when a new persistent run was drawn. -/
  explored : Bool
  /-- The run includes its already-served first action. -/
  run : Option (ExploratoryRun count)
  /-- Nominal masses at the boundary, before persistence conditions later steps. -/
  probabilities : Vector Binary32 count.word.toNat

/-- Persistent exploration or the existing ordered greedy reservoir. -/
def PolicySnapshot.drawPersistent {count : Word.Count} (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) : PersistentDecision count × Rng.Xoshiro256 :=
  let draw := beginExploration count snapshot.epsilon rng
  match draw.1 with
  | some run => (⟨run.action, true, some run, snapshot.probabilities⟩, draw.2)
  | none =>
    let greedy := snapshot.greedy draw.2
    (⟨greedy.1, false, none, snapshot.probabilities⟩, greedy.2)

/-- Served steps have point-mass observations, regardless of the boundary epsilon. -/
def servedProbabilities {count : Word.Count} (action : Action count.word.toNat) :
    Vector Binary32 count.word.toNat := Vector.ofFn fun query => if query = action then .one else .zero

/-- The selected action is the only nonzero reported mass while a run persists. -/
theorem served_probability {count : Word.Count} (action query : Action count.word.toNat) :
    (servedProbabilities action).get query = (if query = action then .one else .zero) := by
  simp [servedProbabilities, Vector.get, Fin.cast]

/-- A served step cannot provide support for a different action, even with
positive boundary epsilon. This is a conditional statement over every run. -/
theorem served_excludes_other {count : Word.Count} (run next : ExploratoryRun count)
    (action other : Action count.word.toNat) (served : run.serve = some (action, next))
    (different : other ≠ run.action) : action ≠ other := by
  rw [(run.serve_exact next action served).1]
  exact Ne.symm different

end Acorn.Features
