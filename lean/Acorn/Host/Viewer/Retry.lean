import Init

namespace Acorn.Host.Viewer

def failureLimit : Nat := 3

abbrev FailureCount := Fin (failureLimit + 1)

def restartDeadline (now : UInt64) (delay : Nat) : UInt64 :=
  UInt64.ofNatLT (min (now.toNat + delay) 18446744073709551615) (by
    have := Nat.min_le_right (now.toNat + delay) 18446744073709551615
    change min (now.toNat + delay) 18446744073709551615 < 18446744073709551616
    omega)

theorem restartDeadline_not_before (now : UInt64) (delay : Nat) :
    now.toNat ≤ (restartDeadline now delay).toNat := by
  simp only [restartDeadline, UInt64.toNat_ofNatLT]
  have bound := now.toNat_lt_size
  change now.toNat < 18446744073709551616 at bound
  omega

structure Retry where
  private mk ::
  private failures : FailureCount
  private next : UInt64

def Retry.initial : Retry := ⟨0, 0⟩

def Retry.count (retry : Retry) : Nat := retry.failures.val

def Retry.exhausted (retry : Retry) : Bool := retry.failures.val == failureLimit

def Retry.ready (retry : Retry) (now : UInt64) : Bool :=
  !retry.exhausted && now ≥ retry.next

def Retry.failed (retry : Retry) (now : UInt64) (healthy : Bool) : Retry :=
  let count := if healthy then 1 else min (retry.failures.val + 1) failureLimit
  have bounded : count < failureLimit + 1 := by
    dsimp [count, failureLimit]
    split
    · omega
    · have := Nat.min_le_right (retry.failures.val + 1) 3; omega
  ⟨⟨count, bounded⟩, restartDeadline now (500 * 2 ^ count)⟩

theorem Retry.initial_not_exhausted : Retry.initial.exhausted = false := rfl

theorem Retry.initial_ready (now : UInt64) : Retry.initial.ready now = true := by
  have fresh := initial_not_exhausted
  have due : now ≥ Retry.initial.next := UInt64.zero_le
  simp [ready, fresh, due]

theorem Retry.exhausted_not_ready (retry : Retry) (now : UInt64)
    (exhausted : retry.exhausted = true) : retry.ready now = false := by
  simp [ready, exhausted]

theorem Retry.healthy_count (retry : Retry) (now : UInt64) :
    (retry.failed now true).count = 1 := rfl

theorem Retry.count_bound (retry : Retry) : retry.count ≤ 3 := by
  have := retry.failures.isLt
  exact Nat.le_of_lt_succ this

end Acorn.Host.Viewer
