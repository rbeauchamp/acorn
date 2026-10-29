#!/bin/bash
# The merge gate: provision the pinned dependencies, then run every merge check, in a
# Git checkout that may hold nothing but tracked files. no-mistakes runs it as the
# Test step's command (.no-mistakes.yaml); `./scripts/gate.sh provision` stops after
# provisioning, as the build that no-mistakes stores for later runs does.
set -euo pipefail

usage='usage: ./scripts/gate.sh [provision]'
case "$*" in
  '') provision_only=0 ;;
  provision) provision_only=1 ;;
  *) echo "$usage" >&2; exit 2 ;;
esac
cd "$(dirname "$0")/.."
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:/opt/homebrew/bin:/usr/local/bin:$PATH"

step() { printf 'gate: %s at %s (%d s)\n' "$1" "$(date -u +%H:%M:%SZ)" "$SECONDS"; }

# Dependency checkouts hold a symbolic link as a plain file holding its target (Git's
# core.symlinks), so lean/.lake/packages holds only directories and regular files, the
# only entries no-mistakes stores. This assumes no dependency builds through a link: a
# linked Lean file would fail to compile, and a linked directory of modules would leave
# them out, failing any import of them. Lake's check of each checkout for local changes
# runs Git under the same setting, so it finds none.
dependency_git() {
  local n=${GIT_CONFIG_COUNT:-0}
  export GIT_CONFIG_COUNT=$((n + 1)) "GIT_CONFIG_KEY_$n=core.symlinks" "GIT_CONFIG_VALUE_$n=false"
}

step 'provisioning the pinned dependencies'
(
  dependency_git
  cd lean
  # Lake decides whether Mathlib and Regula's tools need provisioning: with --no-build
  # it exits 3 unless every artifact and trace of these targets is current.
  current=0
  lake build --no-build Mathlib regula/lint regula/axiomGate || current=$?
  case "$current" in
    0) ;;
    3)
      # The upstream cache can omit modules; Lake compiles only those it lacks.
      lake exe cache get
      lake build Mathlib regula/lint regula/axiomGate ;;
    *) exit "$current" ;;
  esac
  # FloatLib and lean-intent publish no build cache. This builds the modules the proof bridge
  # imports, the lean-intent modules the intent bridge imports and the Regula interface
  # modules the decision registries import.
  lake build floatlibBridge regulaInterface leanIntentBridge
)
./scripts/lean.sh provision-status
(
  dependency_git
  cd site
  # Verso's modules and the shared library its documents load.
  lake build verso/VersoManual verso/VersoManual:shared
)
step 'provisioned'
[[ "$provision_only" == 0 ]] || exit 0

# The two stages of ordinary verification, each under its own 360-second deadline, then
# the Regula audit. The audit runs even when verification fails, so one run reports both.
verified=0
step 'verification, stage one'
if ./scripts/verify.sh build-executing; then
  step 'verification, stage two'
  ./scripts/verify.sh || verified=$?
else
  verified=$?
fi
step "verification exited $verified; Regula audit"
audited=0
./scripts/lean.sh lint || audited=$?
step "Regula audit exited $audited"
[[ "$verified" == 0 && "$audited" == 0 ]] || exit 1
step 'every merge check passed'
