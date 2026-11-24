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
admit_tracked_helper() {
  local root="$1" require_clean="$2" top prefix real_root real_top
  local rec='' line meta path mode oid stage extra count=0 vrec='' vcount=0
  local helper='scripts/tracked-files.sh'
  [[ -n "$root" && ! -L "$root" && -d "$root" && ! -L "$root/scripts" && -d "$root/scripts" &&
    ! -L "$root/$helper" && -f "$root/$helper" ]] || return 1
  top=$(git --no-optional-locks -C "$root" rev-parse --show-toplevel) || return 1
  prefix=$(git --no-optional-locks -C "$root" rev-parse --show-prefix) || return 1
  [[ -n "$top" && -z "$prefix" ]] || return 1
  real_root=$(cd "$root" && pwd -P) || return 1
  real_top=$(cd "$top" && pwd -P) || return 1
  [[ "$real_root" == "$real_top" ]] || return 1
  while IFS= read -r -d '' line; do
    rec="$line"
    count=$((count + 1))
  done < <(git --no-optional-locks --literal-pathspecs -C "$root" -c core.quotePath=false ls-files --stage -z -- "$helper")
  (( count == 1 )) || return 1
  meta="${rec%%$'\t'*}"
  path="${rec#*$'\t'}"
  IFS=' ' read -r mode oid stage extra <<< "$meta"
  [[ "$meta" != "$rec" && -z "${extra:-}" && "$path" == "$helper" &&
    "$stage" == "0" && ( "$mode" == "100644" || "$mode" == "100755" ) &&
    "$oid" =~ ^[0-9a-f]{40}([0-9a-f]{24})?$ ]] || return 1
  if [[ "$require_clean" == 1 ]]; then
    git --no-optional-locks -C "$root" rev-parse --verify -q HEAD >/dev/null || return 1
    git --no-optional-locks -C "$root" diff-index --cached --quiet --ignore-submodules=none HEAD -- "$helper" || return 1
    git --no-optional-locks -C "$root" -c core.symlinks=true -c core.fsmonitor=false diff --no-ext-diff --no-textconv --quiet --ignore-submodules=none HEAD -- "$helper" || return 1
    while IFS= read -r -d '' line; do
      vrec="$line"
      vcount=$((vcount + 1))
    done < <(git --no-optional-locks --literal-pathspecs -C "$root" -c core.quotePath=false ls-files -v -z -- "$helper")
    [[ "$vcount" == 1 && "$vrec" == "H $helper" ]] || return 1
  fi
}

admit_tracked_helper "$repo_root" 1 || {
  echo "regula: scripts/tracked-files.sh failed pre-execution Git admission" >&2
  exit 1
}
"$repo_root/scripts/tracked-files.sh" admit-file --clean "$repo_root" scripts/tracked-files.sh scripts/regula.sh
"$repo_root/scripts/tracked-files.sh" sync-config --clean --for-regula "$repo_root"
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
