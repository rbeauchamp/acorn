# Security reporting

Use GitHub's private vulnerability reporting for
[rbeauchamp/acorn](https://github.com/rbeauchamp/acorn/security/advisories/new):
Security → Advisories → Report a vulnerability. Richard Beauchamp is the
responsible maintainer. Keep vulnerability details, credentials and private run
data in the private report.

Include the affected revision, impact, relevant code paths, assumptions and the
smallest safe reproduction or reasoning needed to assess the report. Avoid
accessing other people's systems or data.

Run the viewer on loopback and keep its run directory accessible only to the
local operator. Keep it behind that local boundary when handling sensitive run
data. Operator-supplied commands execute with the operator's permissions.

Report both traditional security flaws (such as a viewer, launcher or native
`lean/os/checkpoint-sync.c` defect that crosses the local loopback or
filesystem boundary) and soundness or gate-bypass flaws in Acorn's trusted base
(`scripts/`, `lean/lakefile.lean`, `site/lakefile.toml`, `lean/AcornTools/`,
`lean/AcornTools.lean`, `lean/Bootstrap.lean`, `lean/os/` and `.github/`) that
could let unproved or forbidden code pass `./scripts/gate.sh`.

New private reports are reviewed by the owner ([@rbeauchamp](https://github.com/rbeauchamp))
and the organization's agents, targeting initial triage within seven days
without promising 24/7 response or a fixed release schedule. Confirmed defects
are fixed and checked through `./scripts/gate.sh` before public disclosure.
