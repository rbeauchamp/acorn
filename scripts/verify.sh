#!/bin/bash
# Complete local merge checks in the actual Git checkout, within six minutes.
# Arguments pass to acorn-gates. In work on a change, run this script only in a
# form that the closed list in the Test instructions of .no-mistakes.yaml gives;
# the diagnostics argument is not on that list and needs the owner's
# authorization for that run (CONTRIBUTING.md, "Running a program").
set -euo pipefail

if command -v gtimeout >/dev/null 2>&1; then
  timeout_command=gtimeout
elif command -v timeout >/dev/null 2>&1; then
  timeout_command=timeout
else
  echo "verification requires GNU coreutils timeout (macOS: brew install coreutils)" >&2
  exit 127
fi

# Invoked by the supervised child Bash through its exported definition.
# shellcheck disable=SC2329
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
export -f admit_tracked_helper

# Invoked by the supervised child Bash through its exported definition.
# shellcheck disable=SC2329
acorn_verify_checks() {
  local admit_clean=1
  local -a admit_args
  if [[ $("$2" --version) != *"GNU coreutils"* ]]; then
    echo "verification requires GNU coreutils timeout" >&2
    exit 127
  fi
  cd "$(dirname "$1")/.."
  if [[ "$#" == 4 && "$3" == "site" && "$4" == "write" ]]; then
    admit_clean=0
  fi
  admit_tracked_helper . "$admit_clean" || {
    echo "verify.sh: scripts/tracked-files.sh failed pre-execution Git admission" >&2
    exit 1
  }
  admit_args=(admit-file)
  if [[ "$admit_clean" == 1 ]]; then
    admit_args+=(--clean)
  fi
  ./scripts/tracked-files.sh "${admit_args[@]}" . \
    scripts/tracked-files.sh scripts/verify.sh scripts/lean.sh scripts/start.sh scripts/gate.sh scripts/regula.sh
  git diff --check
  git diff --cached --check
  SHELLCHECK_OPTS='' shellcheck --norc \
    scripts/tracked-files.sh scripts/verify.sh scripts/lean.sh scripts/start.sh scripts/gate.sh scripts/regula.sh
  shift 2
  ./scripts/lean.sh exe acorn-gates "$@"
}
export -f acorn_verify_checks

# One fixed timer includes check setup and every descendant in this process
# group. No --foreground (excludes descendants), --verbose (can block before
# signaling), wall-clock subtraction, budget override or wind-up grace period.
# GNU timeout reports SIGKILL as failure status 137, never a partial pass.
exec "$timeout_command" --signal=KILL 360s \
  bash -c 'set -euo pipefail; acorn_verify_checks "$@"' bash "$0" "$timeout_command" "$@"
