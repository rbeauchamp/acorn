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
def declaredDigest : UInt64 := 0x1f06d07ff0192e8b
/-- Knowledge checksum paired with the deployed digest. -/
def declaredChecksum : UInt64 := 0x5e43a33f51993a9b
/-- Annealed incumbent action digest. -/
def annealedDigest : UInt64 := 0xb1edd22df70f4663
/-- Knowledge checksum paired with the incumbent digest. -/
def annealedChecksum : UInt64 := 0x26b4e9080578617b
/-- Differential research action digest. -/
def differentialDigest : UInt64 := 0xc15da626fcf27b4d
/-- Knowledge checksum paired with the differential digest. -/
def differentialChecksum : UInt64 := 0xf815941ae978025a

end Acorn.Host.AuditPins
