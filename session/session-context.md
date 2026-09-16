# Session context: Acorn content review and delivery

**Date:** 2026-09-15
**Branch / starting basis for this cleanup:** `codex/repository-trim-review` /
`7ff461a22f9fed2c4ec15c21d043cd6a6f2715e7`
**Persistence / resume authority:** Git and the live PR for this branch. Resolve
its actual delivery state when resuming; the hash above is the cleanup's starting
basis. After a verified merge, use `main` and its current tip.
**Primary checkout:** `/Users/richard/Developer/github/acorn`
**Remote:** `https://github.com/rbeauchamp/acorn.git` — private when checked.
**Active instruction:** The owner authorized stopping the agent and viewer,
committing and pushing the reviewed changes, creating a PR, and merging once CI
passes. Complete required reviews and exact-head checks. This supersedes the
earlier temporary instruction to keep the content-review branch unmerged.

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
For this evaluator removal, surviving application bodies are unchanged apart
from that namespace relocation; comments and direct imports were updated. The rational/dimensional proof inputs
now live in `AcornVerif.ModelConstants`, with historical protocol constants and
two unused prediction constants removed. Useful current implementation contracts
and supporting mathematical identities remain.

README, verification documentation and the shipped review reference describe the
current layout. BigWorld and Energy comments now state their exact mathematical
scope: fixed formula arithmetic and conditional ledger inequalities. They do not
claim unproved state reachability, checkpoint introspection or execution linkage.
No learning study, audit-pin change or checkpoint-format change was performed.
Acorn-dev was not accessed or modified.

README, AGENTS and the GitHub About description now state Acorn's mission
directly. The viewer distinguishes checkpoint-persistent agent lifetime from
current-world steps and renders quantity-aware collection goals such as
“Hold at least 2 stones.” Counter labels stack above values so the healthy
desktop header remains one row.

The requested live operational check observed advancing telemetry, populated
agent panels, successful checkpoint saves and resumed lifetime counts. Wide and
compact rendered views were inspected. These observations concern operation,
not learning quality. The agent and viewer were then stopped at the owner's
request; the final checkpoint saved successfully and the viewer port closed.

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

The publication review covers the aggregate branch diff. CI explicitly checks
out the proposed PR head and confirms its SHA before verification; push and
manual runs use their event SHA. Recheck the final local result and the live PR's
checks, reviews and merge state when continuing. GitHub owns the current hosted
CI and merge results. No separate issue owns this editorial review.

## Local work to preserve

Separate formatting edits belong to the local worktree, outside this PR:

- docs/design.md
- docs/frontier.md
- docs/prior-art-review.md
- docs/viewer-ux.md

They are temporarily stashed for clean-head verification and merge, then restored
on `main`. If closeout is interrupted, locate the stash named
`Acorn: preserve preexisting documentation formatting during PR closeout` and
restore it only after checking the current worktree. Do not reset or silently
commit these edits. They are absent from a fresh clone. The viewer-spec edit
removes spaces around three code spans in one table cell; that editorial issue
remains for its owner's next selection.

## Standing owner directives


- “you do not need to update acorn-dev anymore. that is now immutable.”
  Acorn is the go-forward repository. Do not edit, synchronize, rebuild or clean
  `/Users/richard/Developer/github/acorn-dev`; consult it only when the owner
  explicitly asks to draw from it.
- The owner now explicitly authorizes this PR's merge after CI passes. Preserve
  branch protections and required reviews. No release or visibility change is
  authorized; the repository remains private.
- Keep the agent and viewer stopped after delivery. Preserve saved learning and
  local run files for a later owner-requested launch.
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
  and the current AGENTS.md full-suite deadline.

## Next action

Revalidate the checkout and live PR for `codex/repository-trim-review`. If delivery
is pending, finish signed publication, exact-head local/hosted verification,
required review, squash merge and primary-checkout cleanup. If merged, verify
the merge is on `origin/main`, use `main`, and preserve the separate local edits.
Then follow the owner's next selected topic; no next implementation task is
selected. Do not restore removed machinery merely because an older handoff named it.

The remaining layout is `lean/Acorn` for execution and proof-bearing state,
`lean/AcornVerif` for implementation contracts and supporting mathematics,
`lean/AcornTools` for verification, and `lean/NativeApp` for native entry points.
Further cleanup should identify concrete consumers or mission value, preserve
current invariants and check execution linkage. This pass removed the separate
evaluator/study dependency group; it is not a repository-wide theorem that every
remaining declaration is necessary. Present materially broader removals before
proceeding. Algorithm changes and new scientific campaigns remain outside this
editorial review.
