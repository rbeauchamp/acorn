# Repair, simplification, and verification


Close each finding at the highest layer that reaches it — type, derivation,
exhaustion, proof, guard — and say which layer you used. A finding closed one
layer lower than it could be is a finding half-closed.

## Simplify the changed code

Runs **last**, and only over code the earlier phases changed. That ordering is
the point: simplifying code you are about to rewrite is wasted work, and
simplifying code you have not yet corrected polishes a defect.

### What "simpler" means here

Not fewer lines. Fewer things a reader must hold in their head, and fewer places
a fact is stated.

- **One definition per fact.** A constant, a length, an ordering or a path
  spelled twice is the defect this codebase keeps rediscovering. Collapse it —
  or, when immutable evidence and a current consumer cannot share it, leave a build gate that checks
  the copies agree.
- **Delete what nothing reads.** A field written every step and read nowhere, a
  helper with no caller, an enumeration array only a log line consumes: each is a
  claim the code no longer supports. Remove it, or give it the consumer its doc
  comment promises.
- **Let the type carry it.** A branch that exists because a value *might* be
  illegal is simpler as a value that cannot be.
- **Collapse a guard the invariant already gives.** Two checks of one fact are
  one check plus a lie about which is load-bearing.
- **Explicit over clever.** No nested ternaries, no dense one-liners, no bare
  arithmetic where a named binding would say what the number is. Clarity beats
  brevity; people reason about this code.

### What you may not simplify away

The hazard here is specific: much of this repository's apparent complexity is
*load-bearing*, and removing it silently weakens a proof.

- A **refinement newtype** with enforced admission owns its legal domain.
  Preserve that enforcement; a wrapper's presence alone is not a guarantee.
- An **exhaustive match** must not gain a `_ =>` arm. The compile error on a new
  variant is the feature.
- A **closed-domain compiler check**, a Lean theorem or a
  gate-suite check is not redundant because it has never fired.
- **Private fields** restrict direct writes. Trace accessors and restoration
  before crediting them with a state invariant; preserve the actual boundary.
- A comment asserting *why* is not noise. Delete comments that restate the code;
  keep the ones a reader could not derive. Apply lens 3's rationale-yes /
  changelog-no rule to anything you rewrite here.

Account for the purpose of any enforcement artifact a simplification would
remove, and establish appropriate replacement coverage before retiring it.

### The check that makes this safe

Establish preservation through the repaired guarantees' types, derivations or
proofs and their execution links, using the proof standard's questions. Run the applicable compiled audit arms and verification required by
`AGENTS.md` on the final changes. Matching audit pins establish agreement only for
the audited executions; they cannot establish universal behavior preservation.
Investigate unexpected digest or checksum movement without re-pinning a supposed
simplification. Report remaining assumptions or proof gaps explicitly.

## Verify the gates, don't trust them

For an added or changed gate, establish its stated acceptance/rejection contract
using a formal owner where available. Otherwise use a discriminating violation
in a disposable copy: observe rejection, restore, and observe acceptance. Name
the affected bypass and what the diagnostic establishes. A green run alone does
not show rejection works; one rejected mutation proves neither complete gate
coverage nor the protected property's universal correctness.

## Verification

Use `AGENTS.md`'s local check command rather than maintaining a second command
list here. Inspect actual proof results and report meaningful outcomes in the PR.
Do not create full-output archives, exported source manifests or separate receipts.
A deliberate dynamics change updates its pin with an explanation in the PR;
unexpected pin movement is a finding, not something to overwrite.
