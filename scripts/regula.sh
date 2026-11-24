#!/bin/bash
# The Regula audit: Regula v0.13.1's proof verdict on the package in lean/, by the route that
# the release publishes (its README and specification/README.md at the tag, "What a pass
# means" and "The named configurations"). Its two commands run in order on one build, each from
# the package's own directory with no option of Lake's and with REGULA_FULL unset:
# `lake build --wfail`, then `lake lint`. `lake lint` reads the build, replays the cone of the
# claim in Lean's kernel into an empty environment and runs Regula's rules under the profile of
# the package's `lintDriverArgs`. It exits 0 for a pass, 1 for a fail and 2 for an incomplete run
# (RG2001), and its last line states the verdict. The audit passes only when `lake lint` exits 0
# and its last line is the pass on this directory's real path, as Regula v0.13.1 prints it
# (`Regula.Closed.Verdict.proofLineOn`, lean/Regula/Verdict.lean at the tag); any other exit or
# last line fails it.
#
# Regula states what that pass means: the proofs of the claimed modules are sound and use only
# axioms that the profile allows, for a project that places no file or code aimed at the checker
# or the toolchain. That a project is not aimed at them is an assumption about the project, which
# Acorn makes of itself and which no check here establishes. Regula's full verdict needs no such
# assumption, and Acorn cannot get it: Acorn has dependencies and imports Mathlib
# (docs/verification.md#regula-audit).
set -euo pipefail
repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
[[ ! -L "$repo_root/scripts" && -d "$repo_root/scripts" && ! -L "$repo_root/scripts/tracked-files.sh" && -f "$repo_root/scripts/tracked-files.sh" ]] || {
  echo "regula: missing non-symlink scripts/tracked-files.sh" >&2
  exit 1
}
"$repo_root/scripts/tracked-files.sh" admit-file "$repo_root" scripts/tracked-files.sh scripts/regula.sh
"$repo_root/scripts/tracked-files.sh" sync-config "$repo_root"
cd "$repo_root/lean"
# With REGULA_FULL set, `lake lint` runs Regula's full gate on the directory it names, which is
# not the published route of the proof verdict.
unset REGULA_FULL
# Acorn's verification keeps Lake's artifact cache off.
export LAKE_ARTIFACT_CACHE=false

lake build --wfail

report=$(mktemp)
trap 'rm -f "$report"' EXIT
status=0
lake lint > "$report" || status=$?
cat "$report"

verdict=$(tail -n 1 "$report")
expected="regula: proof verdict: pass, which says nothing about what ran during the build, on $(pwd -P)"
if [[ "$status" != 0 || "$verdict" != "$expected" ]]; then
  echo "Regula audit: lake lint exited $status with the last line: $verdict" >&2
  exit 1
fi
echo "Regula audit: Regula's proof verdict passes on $(pwd -P)"
