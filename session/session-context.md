# Session context: Acorn content review

**Date:** 2026-09-15
**Branch / starting basis for this cleanup:** `codex/repository-trim-review` /
`7ff461a22f9fed2c4ec15c21d043cd6a6f2715e7`
**Persistence / resume authority:** The commit containing this handoff, pushed to
`origin`. Resolve the actual branch tip when resuming; the hash above is the
starting basis, not this saved commit.
**Primary checkout:** `/Users/richard/Developer/github/acorn`
**Remote:** `https://github.com/rbeauchamp/acorn.git` — private when checked.
**Active focus:** Owner-led review of Acorn's contents, starting minimal with
what the executing agent uses and what supports its mission and current proofs.

## Completed cleanup

The earlier cleanup removed AcornStudy, its dedicated StudyAdmission proofs,
the optional NOTICE and private/public verification switches; it consolidated
ordinary verification in `scripts/verify.sh` under the hard 300-second deadline.

The owner then approved removing superfluous content: “i would rather start
minimal with the what is truly used (no dead code) and useful to our mission.”
The current cleanup removes the separate AcornSpec evaluator, its study schemas,
reducers and six dedicated verification modules, plus the unused Acorn.Host.Study
runner. Their imports, ownership entries, obsolete constant identities and axiom
message guards are removed together.

The 30 live machine-word definitions moved unchanged to `Acorn.Constants`.
Surviving application bodies are unchanged apart from that namespace relocation;
comments and direct imports were updated. The rational/dimensional proof inputs
now live in `AcornVerif.ModelConstants`, with historical protocol constants and
two unused prediction constants removed. Useful current implementation contracts
and supporting mathematical identities remain.

README, verification documentation and the shipped review reference describe the
current layout. BigWorld and Energy comments now state their exact mathematical
scope: fixed formula arithmetic and conditional ledger inequalities. They do not
claim unproved state reachability, checkpoint introspection or execution linkage.
No learning study, dynamics rerun, audit-pin change or runtime/checkpoint edit
was performed. Acorn-dev was not accessed or modified.

## Review and verification

One independent proof-first reviewer checked the diff and dependency/gate
boundaries. All findings were fixed: unused constants, stale model/execution
claims, an unproved state-product reachability claim and wording about binary64
approximations. The reviewer rechecked those repairs with no unresolved finding.

The complete `./scripts/verify.sh` passed in the actual checkout under the
unchanged hard 300-second process-group deadline. Observed scope: **210 modules,
16 native entries, 14 required execution/proof links and 117 native routes**.
Compiler-owned theorem declarations: **2,152 AcornVerif, 4,110 Acorn and 31
NativeApp; total 6,293**. Counts describe checked scope, not correctness or
learning quality. The first build found two line-length violations introduced by
the module rename; both were repaired before the passing complete suite.

No hosted CI result is claimed. No PR was opened or merged during this cleanup;
the owner is still reviewing content. Hosted checks apply to the exact proposed
head when the final PR is prepared. No separate roadmap or issue owns this
editorial review; this handoff holds the continuation point.

## Local work to preserve

Separate formatting edits remain unstaged and uncommitted in:

- docs/design.md
- docs/frontier.md
- docs/prior-art-review.md
- docs/viewer-ux.md

All four were preserved byte-for-byte throughout this cleanup and were present
for the full suite. Do not reset or silently stage them. They are absent from a
fresh clone. The viewer-spec edit removes spaces around three code spans in one
table cell; that small editorial issue remains for its owner's next selection.

## Standing owner directives


- “you do not need to update acorn-dev anymore. that is now immutable.”
  Acorn is the go-forward repository. Do not edit, synchronize, rebuild or clean
  `/Users/richard/Developer/github/acorn-dev`; consult it only when the owner
  explicitly asks to draw from it.
- “do not merge the acorn PR.” Keep this branch unmerged during content review.
  Do not treat general standing merge authorization as overriding this direction.
- “we will continue meticulously reviewing the content of acorn in a fresh session.”
  Continue collaborating on content; do not autonomously publish a final release
  or change repository visibility. The repository is private for these revisions.
- Use direct, inviting language for OaK lab members, researchers and newcomers.
  Let code, documentation and artifacts speak without repeated defensive
  disclaimers or unsupported claims. Preserve exact scientific qualifications
  and theorem hypotheses that change the meaning of a claim.
- The viewer and continuously running agent are the first-run entry point;
  scripts/start.sh owns preparation, builds and default launch settings. Advanced
  bounded runs, research profiles and algorithm details follow that experience.
- Keep docs Markdown filenames lowercase. Keep the dedicated lean package layout
  and the shipped proof-first review skills. Do not reintroduce .claude or Rust.
- Preserve local runtime/checkpoints, .lake dependencies and recovery directories.
  Apply current AGENTS, signed commits, independent review, no scenario tests,
  and the hard 300-second full-suite requirement.

## Next action

Revalidate the actual branch, remote and local edits. Continue the owner's
content review from the updated README and follow their next selected file or
topic. AcornSpec and the unused study runner have been removed; do not restore
historical machinery merely because it appeared in an earlier handoff.

The remaining layout is `lean/Acorn` for execution and proof-bearing state,
`lean/AcornVerif` for implementation contracts and supporting mathematics,
`lean/AcornTools` for verification, and `lean/NativeApp` for native entry points.
Further cleanup should identify concrete consumers or mission value, preserve
current invariants and check execution linkage. This pass removed the separate
evaluator/study dependency group; it is not a repository-wide theorem that every
remaining declaration is necessary. Present materially broader removals before
proceeding. Algorithm changes and new scientific campaigns remain outside this
editorial review.
