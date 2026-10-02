/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-! # Retained current mutation pins

Each digest is paired with its agent checksum. The fixed-width literal spelling
is also read by the native provenance bootstrap; this leaf is the single owner.
Changing a pin records an explicit dynamics decision, never a correctness proof.
All three pins record the published generate-and-test tester (PAR-11, D7), the
task-reading generator, off-policy option learning (PAR-17) and option expectation
models with planning under the current values (PAR-13, PAR-14); the declared-rate
and differential pins also record stable, sign-correct reward-respecting subtasks
and the declared D6 exploration rate.
-/
namespace Acorn.Host.AuditPins

/-- Deployed ranked, declared-rate, discounted action digest. -/
def declaredDigest : UInt64 := 0x3ea4b72d584c56f1
/-- Knowledge checksum paired with the deployed digest. -/
def declaredChecksum : UInt64 := 0x42fcabda2200a8ab
/-- Annealed incumbent action digest. -/
def annealedDigest : UInt64 := 0xb033e8926b40c162
/-- Knowledge checksum paired with the incumbent digest. -/
def annealedChecksum : UInt64 := 0x774e6c1a9e0e9189
/-- Differential research action digest. -/
def differentialDigest : UInt64 := 0x9b2a5aaa0bd8e12e
/-- Knowledge checksum paired with the differential digest. -/
def differentialChecksum : UInt64 := 0x812da8aad89ba364

end Acorn.Host.AuditPins
