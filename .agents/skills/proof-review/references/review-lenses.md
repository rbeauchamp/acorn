# Proof review lenses


Apply lenses to the changed surface and supporting guarantees, including
unchanged owners on which the reviewed claims rely. Skip a lens only when that
surface cannot exercise it; do not audit unrelated repository code.

1. **Proof coverage** — use the [proof questions](proof-standard.md#match-the-claim-to-its-evidence).
   Inspect the actual predicates, domains, hypotheses and execution links in
   Lean, types, gates and their actual constant owners. Name an inherited gap even
   when the owning file is unchanged. Proof counts and artifact names do not
   establish sufficiency.
2. **Correct by construction** — challenge the claimed enforcement through
   every relevant constructor, mutation, capability and load path. Use the
   proof standard's applicable prompts; report legal bypasses even when current
   call order avoids them. Describe the enforced boundary instead of rating it.
3. **Claim accuracy** — every comment and doc line must say what is true now
   and *why* it is that way. Verify each claim against the code: a confidently
   wrong comment is worse than none. Check the pinned digest is consistent
   across README, `docs/`, `AGENTS.md`, and that every documented flag
   exists.

   **Rationale yes, changelog no.** Git holds the history. A file must not
   narrate what was broken, what was fixed, or what a previous version did.
   Report such narration as a finding, and restate whatever it was carrying as
   a present-tense property of the code. The same fact usually has both shapes:

   | Keep — why the code is this way | Reject — what once happened to it |
   |---|---|
   | "the bound is derived from γ, so it cannot drift from the range it protects" | "the original defect set γ after construction" |
   | "`exp`/`ln`/`powf` are not bit-identical across libm implementations, so the digest gates on decisions rather than weight bits" | "the digest used to fold weight bits, and the two platforms disagreed" |

   The test: could a reader who has never seen this repository's history act on
   the sentence? Why a bound is γ-derived tells them what to preserve. What
   broke in a run they cannot inspect does not.

4. **Silent failure** — swallowed errors, `let _ =`, lock poisoning, dropped
   frames. Respect the [documented nonfatal isolation paths](proof-standard.md).
5. **Learned-only purity** — the learned core must name nothing from
   `Acorn.Handcrafted` or `Acorn.Host`. Apply the exact compiler-owned module and
   composition boundary in `AGENTS.md` and `docs/learned-only-binding.md`;
   permitted composition and provenance declarations are not purity defects.
   Any new hand-authored
   domain bias needs a `Provenance` witness and an entry in
   `docs/learned-only-binding.md`. The source and compiled checks in `AcornTools/Boundary/Audit.lean` enforce module ownership;
   typed origin witnesses govern the admitted producers. Neither mechanism
   proves that a provenance declaration is scientifically honest.
6. **Observer invariant** — nothing in `NativeApp.Viewer` or `Acorn.Host.Viewer` may
   change agent decisions, and the audit digest must confirm it.
7. **Prior-art traceability and defect disclosure** — any code symbol, algorithm,
   or mathematical proof derived from prior art must carry an explicit in-code
   citation (`/-- ... -/` or `/-! ... -/` in Lean) stating the
   work, authors, venue/year, and specific equation/section/theorem number. If
   the code or proof repairs an issue, degenerate case, or defect in published
   prior art, the fix must be documented both in doc comments and as a formal
   characterization theorem or identity (the `stepRef_hTemp_error` model).
   Peer reviewers must be able to verify correctness directly against the
   cited source text. Apply the [canonical admission standard](../../../../docs/prior-art-review.md#admission-standard)
   to the implemented mechanism, including its material adaptations and semantic
   composition. Check the rationale and preserved/lost guarantees, not only
   source citations and numerical bounds. A narrow published benchmark is not
   itself a setting incompatibility; benchmark replication and whole-agent
   convergence are not admission requirements. Record the refutation attempt
   against the actual adaptation contract.

8. **Portable scientific evidence** — apply the
   [deliverable placement policy](../../../../CONTRIBUTING.md#deliverable-placement)
   to added files: check scientific ownership, shared implementation reuse, and
   whether temporary engineering records are being committed as research.
   Discover every dossier and resolve each
   published study/protocol/run/comparison citation. Check immutable protocol
   revisions, complete inventories, distinct run identities, interrupted-run
   records, and original bytes versus semantic presentations. Kind, lifecycle,
   and outcome must remain separate typed dimensions; a completed refutation
   is not an aborted run, and a draft needs no fabricated result. Preserve
   registered streams, observations, thresholds, canonical outputs, and audit
   pins during relocation. No new study or scenario test closes a rename.
   Apply the canonical essential-evidence/secondary-trace distinction: every
   study declares what supports its claims, whether full step traces are
   needed, and what reproduction means. Do not require full trajectories
   merely because a runner can emit them. Verify retained secondary archives
   against original member identities; do not treat a current packaging
   decision as preregistration or a rerun as the original observation.
   Review content integrity separately from analysis reproduction, historical
   rerun support, and registration timing. Hash-only preregistration and
   self-authored trust anchors are findings. Future timestamps use OpenSSL 3
   against the independent external `ACORN_REGISTRATION_TRUST` policy only
   when optional timestamp authentication is claimed; routine gates need no CA;
   historical Git objects retain timing and blindness limitations. Ordinary
   verification runs in the Git checkout with provisioned tools.
   Verify future empirical protocols against the complete research requirements
   in the dossier standard, including resource equality and prior data access.



Apply the canonical [admission and promotion standard](../../../../docs/prior-art-review.md#default-promotion-and-demotion).
Admission permits research integration; it does not promote a default. Review
the declared benefit, prospective margins/tradeoffs, actual composition, fresh
confirmation where empirical, and explicit fallback/qualification decision.
Preserve negative results and do not turn legacy retention into a new pass.
