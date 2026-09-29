/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-! # Retained current mutation pins

Each digest is paired with its agent checksum. The fixed-width literal spelling
is also read by the native provenance bootstrap; this leaf is the single owner.
Changing a pin records an explicit dynamics decision, never a correctness proof.
All three pins record the published generate-and-test tester (PAR-11, D7) and
the task-reading generator; the declared-rate and differential pins also record
stable, sign-correct reward-respecting subtasks and the declared D6 exploration rate.
-/
namespace Acorn.Host.AuditPins

/-- Deployed ranked, declared-rate, discounted action digest. -/
def declaredDigest : UInt64 := 0x25ea4ea335774876
/-- Knowledge checksum paired with the deployed digest. -/
def declaredChecksum : UInt64 := 0x754fb5906278a9d0
/-- Annealed incumbent action digest. -/
def annealedDigest : UInt64 := 0x32a3ceaeacacb336
/-- Knowledge checksum paired with the incumbent digest. -/
def annealedChecksum : UInt64 := 0x5a7e9eeb17ffe8f7
/-- Differential research action digest. -/
def differentialDigest : UInt64 := 0x83f95efce2ebb599
/-- Knowledge checksum paired with the differential digest. -/
def differentialChecksum : UInt64 := 0x36265594d250fdf8

end Acorn.Host.AuditPins
