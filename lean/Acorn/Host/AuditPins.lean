/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-! # Retained current mutation pins

Each digest is paired with its agent checksum. The fixed-width literal spelling
is also read by the native provenance bootstrap; this leaf is the single owner.
Changing a pin records an explicit dynamics decision, never a correctness proof.
The declared-rate and differential pins record two such decisions: stable,
sign-correct reward-respecting subtasks and the declared D6 exploration rate.
-/
namespace Acorn.Host.AuditPins

/-- Deployed ranked, declared-rate, discounted action digest. -/
def declaredDigest : UInt64 := 0x9f7690b338600144
/-- Knowledge checksum paired with the deployed digest. -/
def declaredChecksum : UInt64 := 0xeb40c4d351658e61
/-- Annealed incumbent action digest. -/
def annealedDigest : UInt64 := 0xd41d9d77b74b9858
/-- Knowledge checksum paired with the incumbent digest. -/
def annealedChecksum : UInt64 := 0x4b15707c76a9191a
/-- Differential research action digest. -/
def differentialDigest : UInt64 := 0x9f2e2ac81d20b6ff
/-- Knowledge checksum paired with the differential digest. -/
def differentialChecksum : UInt64 := 0x6d70ef3bd4b15545

end Acorn.Host.AuditPins
