# Proof scoring standard


> If a property matters, the compiler must check it — in Lean, against the executed definitions.
> Proofs must verify the *absence* of bugs. Every "test gap" is a missing
> universal theorem, typed invariant, compiler-enforced refinement, or
> deterministic-audit mutation. Counterexamples are adversarial diagnostics
> only; their permanent closure must be a proof or an oracle/compiler contract
> that makes the bad state **or the bypass** uninhabitable. Code must be
> **correct by construction**.

And the ordering that goes with it:

1. a **type** whose inhabitants are exactly the legal values
2. **derivation** over assertion (a relation made definitionally true needs no check)
3. **exhaustion** over a closed domain the compiler enumerates
4. a **proof** — Lean for bit-precise, inductive and mathematical contracts.
   Ranked internally, math first, computation last: analytic/structural
   argument → small closed kernel `decide` → reflection (`native_decide`),
   which certifies re-execution and is the last resort *inside* proof
5. a **runtime guard**, last resort, and only when its predicate is *derived
   from the invariant* — a guard on the wrong set is worse than none
6. **measurement** — an *absolute* last resort, below the guard

### Match the claim to its evidence

For each changed guarantee and inherited guarantee the reviewed behavior relies
on, check the following. These are reasoning questions, not a required record:

- **Claim and domain:** the exact property, legal states and representations;
  distinguish machine arithmetic from mathematical values.
- **Hypotheses and bounds:** assumptions, admission predicates, symbolic inputs,
  loop/length limits and the domain actually quantified by the owner.
- **Enforcement and execution link:** the owning type, derivation, theorem or
  gate; every relevant construction/write/load path; how the checked statement
  reaches the actual implementation, including explicit trusted boundaries.
- **Composition and mission:** state the end-to-end property the user relies on.
  For producer/receiver boundaries, prove emitted values satisfy admission and
  preserve meaning; matching names, shapes or generated code is insufficient.
  Do not assume receiver admission in the theorem claiming compatibility. For
  lifecycle work, distinguish safety from progress: trace owned blocking work
  through completion and errors, naming any dependence on future external input.
- **Limits and closure:** what remains assumed, bounded or unresolved, and the
  simplest sound strengthening where needed, with initial and recurring cost.

A proof checks its supplied statement. Names, attributes, private fields,
non-Copy tokens, passing proof counts and documentation are not substitutes for
checking that linkage. A legal operation sequence that violates the claimed contract is a
finding even if current callers avoid it; distinguish that gap from an observed
runtime failure. A source pin detects changes to reviewed code, and an emitted
constant link checks constants; neither alone proves implementation correspondence.

Select challenges relevant to the claim; these are reasoning prompts, not a
required set of probes or a reason to expand into a whole-repository audit:

| Claimed guarantee | Discriminating check |
|---|---|
| Universal numeric behavior | Inspect quantified input representations and assumptions; one special value does not cover every encoding of its class. A ground identity is adequate for a genuinely ground claim. |
| Exhaustive domain | Trace inventory generation back to the domain declaration; check whether an added variant can escape the inventory or its required metadata. |
| Capability or encapsulation | Trace minting, owner association, reuse, interleaving, accessors and restoration; one-use or field privacy alone may not enforce the promised invariant. |
| Arbitrary traversal/history | Identify the invariant, base case, preserved transition and linkage to the actual traversal. A bounded harness establishes only its bound unless a valid induction supplies the rest. |
| Evidence or accuracy attribution | Match the precise predicate to its owner; separate diagnostics from closure, rounded identities from approximation bounds, and audit agreement from universal preservation. |

Prefer a structural argument or compiler rejection. Use a disposable mutation
when it discriminates between the claimed enforcement and a plausible bypass;
the diagnostic is not permanent closure. Do not reject an honestly bounded
guarantee for lacking an unclaimed universal, or inflate proof bounds to replace
an available inductive argument.

### Compute-frugality is part of the standard

An ounce of math is worth a pound of computation. Flag as findings: a
reflection proof where an analytic argument or a small static `decide` was in
reach; and any reflection-based proof program whose total certification
compute (including the recurring re-proof tax on spec edits) is not estimated
against the empirical run it replaces, or costs no less than it, without a
recorded owner decision. Decidability permits decision procedures; it is
neither required for mathematical proof nor a justification for its cost.
Certified re-execution must still justify its compute against a structural
argument.

### Proof first, measurement last

Before accepting a measured claim, classify its evidence obligation.
Conformance, identities, bounds, invariants, expected values and counting claims
require formal evidence when claimed universally; these general classes are
not necessarily decidable. A measured instance cannot establish a universal,
even when its number is right. Name the missing universal obligation and its
appropriate owner. An unresolved proof obligation remains unresolved; it does
not become irreducibly empirical because a proof is difficult.

Measurement is legitimate only for the **irreducibly empirical**: a constant of
the world, a regime, an effect size. Those must be labelled `UNKNOWN` at the
point of use with the reason no derivation reaches them, reported as
**observed** with their run and configuration, and carry a threshold fixed
*before* the run.

### A witness is still a test, whatever language it is in

`∃ x, f x ≠ g x` in Lean is a hand-picked instance wearing a proof assistant's
hat. Reject it as a closure exactly as you would reject a unit test. The
closure is the **universal**: quantify over the whole domain, or — better —
state the discrepancy as an identity that holds everywhere,

```text
∀ x, f x - g x = <explicit expression>
```

which characterises the difference completely instead of exhibiting one case of
it. If a reviewer proposes "add a Lean example showing the bug", translate it
the way the table below translates every other test-shaped instinct.

## Findings that are invalid here — reject on sight

Do not report, and reject if a sub-agent returns them:

- "Add a unit / integration / scenario / property test."
- "Add a regression test for this bug."
- "This code path is untested."
- "Increase coverage."
- "Add a runtime assertion to catch X" — when a type could make X
  unrepresentable. Say that instead.

Respect documented nonfatal isolation paths: telemetry delivery must not affect
the learning run, and the viewer can drop slow-browser frames, recover locks,
or absorb log-write failures where its contract permits that behavior. This is
not a blanket exemption for either directory. Check the owning contract before
flagging or accepting an absorbed error; required fault visibility, argument
validation, persistence status, and lifecycle correctness still apply.

## Translate, don't discard

A test-shaped instinct usually points at something real. Restate it:

| Test-shaped instinct | What to report instead |
|---|---|
| "untested edge case" | which type change makes the case unrepresentable |
| "no regression test" | the Lean theorem or typed admission that closes it permanently |
| "assert this at runtime" | the refinement type, or a compiler-exhaustive match or theorem over the actual closed type |
| "untested numeric behaviour" | a refinement over the relevant machine domain; a one-step proof needs the invariant and induction that justify composition |
| "no test for this algorithm" | the theorem for the claimed property and its execution link; generated constants establish only that part of the correspondence |
| "behaviour might silently change" | the owning semantic guarantee and the audit's explicitly limited mutation coverage |

A compiler check closes a finite-domain claim only when the domain is actually
closed by its type and the check covers every constructor. An exhaustive match
on `Acorn.Departure` cannot silently omit a new constructor. Hand-listing a few
values from an open domain is still sampled checking, even during compilation.
