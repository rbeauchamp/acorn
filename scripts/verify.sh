#!/bin/bash
# Complete local merge checks in the actual Git checkout, within five minutes.
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
  git diff --check
  git diff --cached --check
  shellcheck scripts/verify.sh scripts/lean.sh scripts/start.sh
  shift 2
  ./scripts/lean.sh exe acorn-gates "$@"
}
export -f acorn_verify_checks

# One fixed timer includes check setup and every descendant in this process
# group. No --foreground (excludes descendants), --verbose (can block before
# signaling), wall-clock subtraction, budget override or wind-up grace period.
# GNU timeout reports SIGKILL as failure status 137, never a partial pass.
exec "$timeout_command" --signal=KILL 300s \
  bash -c 'set -euo pipefail; acorn_verify_checks "$@"' bash "$0" "$timeout_command" "$@"
