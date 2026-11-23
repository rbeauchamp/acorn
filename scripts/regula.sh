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
cd "$(dirname "$0")/../lean"
# With REGULA_FULL set, `lake lint` runs Regula's full gate on the directory it names, which is
# not the published route of the proof verdict.
unset REGULA_FULL
# Acorn's verification keeps Lake's artifact cache off.
export LAKE_ARTIFACT_CACHE=false

sync_tracked_lake_config() {
  local top prefix_dir tracked_tmp entry
  top=$(git -C . rev-parse --show-toplevel)
  prefix_dir=$(git -C . rev-parse --show-prefix)
  if [[ -z "$top" || "$prefix_dir" != "lean/" || "$(pwd -P)" != "$(cd "$top" && pwd -P)/lean" ]]; then
    echo "regula: must run inside tracked lean/ directory" >&2
    exit 1
  fi
  if [[ -L lakefile.lean || ! -f lakefile.lean ]]; then
    echo "regula: lean/lakefile.lean must be a regular file" >&2
    exit 1
  fi
  git -C . -c core.quotePath=false ls-files --error-unmatch -- lakefile.lean >/dev/null
  mkdir -p .lake
  tracked_tmp=$(mktemp .lake/acorn-tracked-modules.z.XXXXXX)
  if ! git -C . -c core.quotePath=false ls-files --stage -z -- '*.lean' > "$tracked_tmp" || [[ ! -s "$tracked_tmp" ]]; then
    rm -f "$tracked_tmp"
    echo "regula: failed to enumerate tracked lean/*.lean modules" >&2
    exit 1
  fi
  if [[ ! -f .lake/acorn-tracked-modules.z ]] || ! cmp -s "$tracked_tmp" .lake/acorn-tracked-modules.z; then
    for entry in .lake/config/lakefile.olean .lake/config/lakefile.olean.trace .lake/config/*/lakefile.olean .lake/config/*/lakefile.olean.trace ../site/.lake/config/lakefile.olean ../site/.lake/config/lakefile.olean.trace ../site/.lake/config/*/lakefile.olean ../site/.lake/config/*/lakefile.olean.trace; do
      if [[ -e "$entry" || -L "$entry" ]]; then
        rm -f "$entry"
      fi
    done
    mv -f "$tracked_tmp" .lake/acorn-tracked-modules.z
  else
    rm -f "$tracked_tmp"
  fi
}

sync_tracked_lake_config

lake -f lakefile.lean build --wfail

report=$(mktemp)
trap 'rm -f "$report"' EXIT
status=0
lake -f lakefile.lean lint > "$report" || status=$?
cat "$report"

verdict=$(tail -n 1 "$report")
expected="regula: proof verdict: pass, which says nothing about what ran during the build, on $(pwd -P)"
if [[ "$status" != 0 || "$verdict" != "$expected" ]]; then
  echo "Regula audit: lake lint exited $status with the last line: $verdict" >&2
  exit 1
fi
echo "Regula audit: Regula's proof verdict passes on $(pwd -P)"
