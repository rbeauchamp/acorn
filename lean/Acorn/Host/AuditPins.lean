/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-! # Retained current mutation pins

Each digest is paired with its agent checksum. The fixed-width literal spelling
is also read by the native provenance bootstrap; this leaf is the single owner.
Changing a pin records an explicit dynamics decision, never a correctness proof.
-/
namespace Acorn.Host.AuditPins

/-- Deployed ranked, derived-exploration, discounted action digest. -/
def derivedDigest : UInt64 := 0x829aef890c81afaf
/-- Knowledge checksum paired with the deployed digest. -/
def derivedChecksum : UInt64 := 0xb1a076b6ac5884f0
/-- Annealed incumbent action digest. -/
def annealedDigest : UInt64 := 0xd41d9d77b74b9858
/-- Knowledge checksum paired with the incumbent digest. -/
def annealedChecksum : UInt64 := 0x4b15707c76a9191a
/-- Differential research action digest. -/
def differentialDigest : UInt64 := 0xbb1d5b590fad9933
/-- Knowledge checksum paired with the differential digest. -/
def differentialChecksum : UInt64 := 0x47a82981b9a9ee2d

end Acorn.Host.AuditPins
