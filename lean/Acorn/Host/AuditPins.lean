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
models with planning under the current values (PAR-13, PAR-14), and the checksums fold
every option's off-policy questions (PAR-18). All three also record persistent
exploration by whichever layer selects the action, with a run interrupting the option
whose draw began it (PAR-8, D3); the declared-rate
and differential pins also record stable, sign-correct reward-respecting subtasks
assigned at every free decision boundary and the declared D6 exploration rate.
-/
namespace Acorn.Host.AuditPins

/-- Deployed ranked, declared-rate, discounted action digest. -/
def declaredDigest : UInt64 := 0x876ce9aa95323db5
/-- Knowledge checksum paired with the deployed digest. -/
def declaredChecksum : UInt64 := 0xa8437ba4191b7dc2
/-- Annealed incumbent action digest. -/
def annealedDigest : UInt64 := 0x545f839c86d84577
/-- Knowledge checksum paired with the incumbent digest. -/
def annealedChecksum : UInt64 := 0x1470c342197223ff
/-- Differential research action digest. -/
def differentialDigest : UInt64 := 0xb5082d4f8c69d1b9
/-- Knowledge checksum paired with the differential digest. -/
def differentialChecksum : UInt64 := 0x4f6c4e67ebb02467

end Acorn.Host.AuditPins
