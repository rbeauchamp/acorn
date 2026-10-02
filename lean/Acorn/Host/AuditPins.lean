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
task-reading generator and off-policy option learning (PAR-17); the declared-rate
and differential pins also record stable, sign-correct reward-respecting subtasks
and the declared D6 exploration rate.
-/
namespace Acorn.Host.AuditPins

/-- Deployed ranked, declared-rate, discounted action digest. -/
def declaredDigest : UInt64 := 0x7433307b046fd16c
/-- Knowledge checksum paired with the deployed digest. -/
def declaredChecksum : UInt64 := 0x385b2f84db38eef2
/-- Annealed incumbent action digest. -/
def annealedDigest : UInt64 := 0x73355bc3ce9747ff
/-- Knowledge checksum paired with the incumbent digest. -/
def annealedChecksum : UInt64 := 0x3e761e92a9584855
/-- Differential research action digest. -/
def differentialDigest : UInt64 := 0xe75a9f5260ce566a
/-- Knowledge checksum paired with the differential digest. -/
def differentialChecksum : UInt64 := 0xea34c0f0eb25b8bb

end Acorn.Host.AuditPins
