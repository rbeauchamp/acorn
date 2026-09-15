# Session context: Acorn content review

**Date:** 2026-09-15
**Source branch / starting basis:** `codex/repository-trim-review` /
`999b67786b856c3d0eca3360424f3548d5b3a8a0`
**Persistence / resume authority:** The signed commit containing this handoff on
`codex/repository-trim-review`, pushed to `origin`. Resolve the actual branch tip
when resuming; the hash above is the starting basis, not the saved commit.
**Primary checkout:** `/Users/richard/Developer/github/acorn`
**Remote:** `https://github.com/rbeauchamp/acorn.git` — private when checked.
**Active focus:** Continue the owner's meticulous review of Acorn's contents.

## Completed cleanup

- Removed the optional root NOTICE and its README link; LICENSE and source
  copyright/license notices remain.
- Removed AcornStudy and its sole dedicated external proof owner,
  AcornVerif.StudyAdmission. Removed their ownership/import/process allowances.
- Removed the source verification-profile switch, absent private Lake targets,
  protocol-provenance branch and private archive/citation exemptions. The source
  checker now has one explicit complete module and native-entry inventory.
- Folded verify-lean.sh into verify.sh inside the existing 300-second timeout.
  The ordinary suite still checks every source/native entry, compiled ownership,
  proof axioms, native routes/resources, browser generation and maintained corpus.
  The corpus tool retains its focused `documents` mode; ordinary verification
  always runs complete corpus admission.
- Consolidated contributor policy in AGENTS, with scientific recordkeeping in
  CONTRIBUTING and focused review questions in the shipped skills. Updated
  README, verification and performance documentation accordingly.
- Replaced obsolete Rust/Kani/migration narration with current Lean ownership and
  model-domain descriptions. All retained Lean mathematics and application bodies
  are unchanged except three WorldDriver admission diagnostic messages.

## Decisions and evidence

AcornStudy had no application importers. Its only external proof importer was
StudyAdmission. Keep Acorn.Json: the viewer uses it. Keep AcornSpec.Constants,
StudySchedule, StudyCompatibility and the other retained specification/analysis
modules: they have real application or proof users. Removing those requires a
separate dependency and semantic review; their names alone do not make them dead.
Model identities do not automatically establish current execution correspondence.

One independent proof-first reviewer checked the actual diff. Both findings were
fixed: i64ToF32 documentation again states its signed-64-bit input domain, and
MetaGradient no longer claims to import model constants when its inputs are
symbolic. Compiler checks caught and closed the obsolete Corpus.Main call after
removal of the evidence parameters.

The complete `./scripts/verify.sh` passed in the actual checkout in **110.39 s**
under the unchanged hard 300-second deadline, before these session files were
added. Observed scope: 241 maintained modules, 16 native entries, 14 required
execution/proof links, 117 native routes; 2,360 AcornVerif, 427 AcornSpec,
4,145 Acorn and 31 NativeApp theorem declarations, total **6,963**. The decrease
from 7,066 consists of AcornStudy's 96 and StudyAdmission's 7 declarations.
Counts describe checked scope, not correctness or learning quality.

Disposable admission mutations were rejected for missing and extra modules,
an extra evaluated native entry, an archived document path, a stale published
pin, and the removed studies command. All original bytes were restored before
the final suite. An initial extra-entry diagnostic reused an existing executable
root and was rejected earlier by Lake; using a distinct root exercised the
intended ownership refusal. These are gate diagnostics, not scenario tests.
No learning study, dynamics rerun or audit-pin change was performed.

No GitHub CI result is claimed for this branch. No PR was opened or merged.
The user is still reviewing contents; hosted checks apply when the final PR is
prepared. No separate roadmap or issue owns this editorial review, so this
handoff holds the next step without introducing a planning system.

## Local work to preserve

Separate formatting edits appeared during this task in:

- docs/design.md
- docs/frontier.md
- docs/prior-art-review.md
- docs/viewer-ux.md

These four files remain **unstaged and uncommitted**, preserved in this checkout;
they are not part of the cleanup commit. They mostly change table spacing, blank
lines and URL markup. The viewer-spec diff also removes spaces around three code
spans in one table cell; inspect that hunk in the next review. Do not reset or
silently stage these separately owned edits. The complete suite above saw these
local formatting changes. A fresh clone will not contain them.

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

Read the actual branch status and preserve the four local formatting edits above.
Then reread README as a newcomer and review the remaining top-level content with
the owner. Begin with the retained lean/AcornSpec and lean/AcornVerif roles: explain
what supports the executing agent, what is a separate mathematical/evaluator
model, and identify any further removal or wording proposals with their concrete
users and consequences. Present recommendations before materially broader
removals. Follow the owner's next selected file or topic; this is an editorial
review, not authorization for algorithm changes or new studies.

Useful entry points: README.md, AGENTS.md, CONTRIBUTING.md, docs/verification.md,
lean/AcornSpec.lean, lean/AcornVerif.lean and lean/AcornTools/Ownership.lean.
