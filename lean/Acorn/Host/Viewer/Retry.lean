/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# Bounded restart policy

Three consecutive short failures stop automatic restart. A run exceeding the
30-second operational threshold begins a new failure sequence at one. Backoff
is derived from the admitted failure count, so no arbitrary shift or unbounded
failure counter enters scheduling.
-/
namespace Acorn.Host.Viewer

/-- Consecutive failures exhaust automatic restart at this closed bound. -/
def failureLimit : Nat := 3

/-- The complete consecutive-failure domain includes the exhausted state. -/
abbrev FailureCount := Fin (failureLimit + 1)

/-- Saturating deadlines cannot wrap into the past at the machine-word boundary. -/
def restartDeadline (now : UInt64) (delay : Nat) : UInt64 :=
  UInt64.ofNatLT (min (now.toNat + delay) 18446744073709551615) (by
    have := Nat.min_le_right (now.toNat + delay) 18446744073709551615
    change min (now.toNat + delay) 18446744073709551615 < 18446744073709551616
    omega)

/-- Saturation preserves deadline order even at the full-width clock boundary. -/
theorem restartDeadline_not_before (now : UInt64) (delay : Nat) :
    now.toNat ≤ (restartDeadline now delay).toNat := by
  simp only [restartDeadline, UInt64.toNat_ofNatLT]
  have bound := now.toNat_lt_size
  change now.toNat < 18446744073709551616 at bound
  omega

/-- Restart admission owns both its finite budget and the next allowed time. -/
structure Retry where
  private mk ::
  private failures : FailureCount
  private next : UInt64

/-- Initial startup and explicit Start begin with the complete retry budget. -/
def Retry.initial : Retry := ⟨0, 0⟩

/-- Read-only diagnostic failure count. -/
def Retry.count (retry : Retry) : Nat := retry.failures.val

/-- Exhaustion stops automatic restart until an explicit Start resets the budget. -/
def Retry.exhausted (retry : Retry) : Bool := retry.failures.val == failureLimit

/-- A retry needs both remaining budget and an elapsed deadline. -/
def Retry.ready (retry : Retry) (now : UInt64) : Bool :=
  !retry.exhausted && now ≥ retry.next

/-- Every unexpected exit or failed spawn consumes one admitted failure slot. -/
def Retry.failed (retry : Retry) (now : UInt64) (healthy : Bool) : Retry :=
  let count := if healthy then 1 else min (retry.failures.val + 1) failureLimit
  have bounded : count < failureLimit + 1 := by
    dsimp [count, failureLimit]
    split
    · omega
    · have := Nat.min_le_right (retry.failures.val + 1) 3; omega
  ⟨⟨count, bounded⟩, restartDeadline now (500 * 2 ^ count)⟩

/-- An exhausted budget can never admit a timed restart. -/
theorem Retry.exhausted_not_ready (retry : Retry) (now : UInt64)
    (exhausted : retry.exhausted = true) : retry.ready now = false := by
  simp [ready, exhausted]

/-- A healthy-duration exit begins the new short-failure sequence at exactly one. -/
theorem Retry.healthy_count (retry : Retry) (now : UInt64) :
    (retry.failed now true).count = 1 := rfl

/-- No failure report can grow the retained failure count beyond its fixed domain. -/
theorem Retry.count_bound (retry : Retry) : retry.count ≤ 3 := by
  have := retry.failures.isLt
  exact Nat.le_of_lt_succ this

end Acorn.Host.Viewer
