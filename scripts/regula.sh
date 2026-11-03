#!/bin/bash
# The Regula audit: Regula v0.12.0's proof verdict on the package in lean/, on one build, each
# command from the package's own directory with no option of Lake's. The release names
# `lake build --wfail`, `lake check --inadvisably-no-sandbox` and `lake lint`, in that order.
# Here the second is the package's script `kernelReplay` (lean/lakefile.lean), which replays
# every constant of every claimed module, with every constant it depends on, in Lean's kernel
# from an empty environment, and refuses an axiom outside the three `lake check` admits.
# `lake check` replays the whole imported environment, Mathlib's included, from an export it
# holds in memory, which does not fit the machines Acorn's gate runs on.
# The claim is the modules of the package's default targets and every module of the package
# their imports reach. The audit passes only when `lake lint` exits 0 and its last line is the
# pass on this package's directory; a fail (exit 1), an incomplete run (exit 2) and any other
# last line fail it.
set -euo pipefail
cd "$(dirname "$0")/../lean"
# Acorn's verification keeps Lake's artifact cache off.
export LAKE_ARTIFACT_CACHE=false

lake build --wfail
lake script run kernelReplay

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
echo "Regula audit: proof verdict pass on $(pwd -P)"
