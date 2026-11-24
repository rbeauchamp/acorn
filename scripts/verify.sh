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
acorn_verify_checks() {
  if [[ $("$2" --version) != *"GNU coreutils"* ]]; then
    echo "verification requires GNU coreutils timeout" >&2
    exit 127
  fi
  cd "$(dirname "$1")/.."
  [[ ! -L scripts && -d scripts && ! -L scripts/tracked-files.sh && -f scripts/tracked-files.sh ]] || {
    echo "verify.sh: missing non-symlink scripts/tracked-files.sh" >&2
    exit 1
  }
  ./scripts/tracked-files.sh admit-file . \
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
