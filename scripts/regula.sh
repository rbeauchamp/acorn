#!/bin/bash
# The Regula audit, on one build of the package in lean/, each command from the package's own
# directory with no option of Lake's. Regula v0.12.0's release names three commands for its
# proof verdict: `lake build --wfail`, `lake check --inadvisably-no-sandbox` and `lake lint`, in
# that order. `lake check` replays the whole imported environment, Mathlib's included, from an
# export it holds in memory, which does not fit the machines that run Acorn's gate. In its place
# this audit runs Acorn's kernel replay, `lake exe kernel-replay` (lean/AcornTools/KernelReplay.lean):
# the claim that Regula itself reads of this build, and every constant it depends on, replayed in
# Lean's kernel from an empty environment, with the quotient check and the axiom list of
# `lake check`. So the audit obtains Regula's rules under the profile and that replay, not
# Regula v0.12.0's proof verdict as the release defines it.
# The claim is the modules of the package's default targets and every module of the package
# their imports reach. The replay reads it once, with Regula's own code, under the profile of the
# package's `lintDriverArgs`; it runs Regula's rules on that one input and replays the same input's
# claim, and exits 0 only when the rules pass and the kernel accepts. Then `lake lint` runs as the
# release names it. Both print Regula's line of what they read, and the audit fails unless the two
# lines agree: a consistency check that both runs read the same numbers of claimed modules and
# constants, not a check that the build did not change between them. The audit passes only when
# `lake lint` also exits 0 and its last line is the pass on this package's directory; a fail
# (exit 1), an incomplete run (exit 2) and any other last line fail it.
set -euo pipefail
cd "$(dirname "$0")/../lean"
# Acorn's verification keeps Lake's artifact cache off.
export LAKE_ARTIFACT_CACHE=false

lake build --wfail

replayed=$(mktemp)
report=$(mktemp)
trap 'rm -f "$replayed" "$report"' EXIT
lake exe kernel-replay | tee "$replayed"

status=0
lake lint > "$report" || status=$?
cat "$report"

# Regula's line of what it read (`Regula.Shell.coverage`, which `lake lint` indents by two spaces):
# the replay's and the lint's must state the same numbers of claimed modules and constants.
coverage() {
  grep -E '^ *regula: read [0-9]+ claimed modules and [0-9]+ of their constants$' "$1" |
    sed -E 's/^ +//' || true
}
replay_read=$(coverage "$replayed")
lint_read=$(coverage "$report")
if [[ -z "$replay_read" || "$replay_read" != "$lint_read" ]]; then
  echo "Regula audit: the kernel replay read '$replay_read' and lake lint read '$lint_read'" >&2
  exit 1
fi

verdict=$(tail -n 1 "$report")
expected="regula: proof verdict: pass, which says nothing about what ran during the build, on $(pwd -P)"
if [[ "$status" != 0 || "$verdict" != "$expected" ]]; then
  echo "Regula audit: lake lint exited $status with the last line: $verdict" >&2
  exit 1
fi
echo "Regula audit: Regula's rules pass on the claim the kernel replay accepts, and lake lint passes, on $(pwd -P)"
