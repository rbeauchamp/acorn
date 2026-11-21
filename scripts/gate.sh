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
  # Parallel cache extraction can exhaust macOS's inherited 256-descriptor limit.
  # Give provisioning a process-local floor before Lake can fetch dependencies;
  # preserve higher limits and the hard limit. This is a budget, not a peak bound.
  descriptor_limit=$(ulimit -Sn)
  if [[ "$descriptor_limit" != unlimited ]] && (( descriptor_limit < 4096 )); then
    ulimit -Sn 4096
  fi
  dependency_git
  cd lean
  # Lake decides whether Mathlib and Regula's lint driver need provisioning: with
  # --no-build it exits 3 unless every artifact and trace of these targets is current.
  current=0
  lake build --no-build Mathlib regula/lint || current=$?
  case "$current" in
    0) ;;
    3)
      # The upstream cache can omit modules; Lake compiles only those it lacks.
      lake exe cache get
      lake build Mathlib regula/lint ;;
    *) exit "$current" ;;
  esac
  # FloatLib, lean-intent and Regula publish no build cache. This builds the modules the proof
  # bridge imports, the lean-intent modules the intent bridge and intent-check import with the
  # native objects intent-check links, and the Regula modules the decision registries and
  # AcornTools.Theorems import with their native objects.
  lake build floatlibBridge regulaInterface leanIntentBridge leanIntentNative
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
# the Regula audit (scripts/regula.sh: Regula's proof verdict, by the two commands its release
# publishes) on its own build with no deadline, lean-intent's two checks with no deadline:
# intent-check (lean/AcornTools/Intent.lean) runs the confirmation check and the implementation
# check on one list of modules, those Lake lists for the default libraries, and passes only when the
# first finds nothing and the second finds only the deliverables its closed list names as awaiting
# an implementation. Last, frame-check (lean/AcornTools/Frame.lean) compares each target's pin
# file, if it has one, with the declarations the target reads in the finished build. The audit
# and the checks run even when an earlier step fails, so one run reports all four. When ordinary
# verification passed, every module and executable is already built and lean/.lake/acorn-path-packages.json
# is current, so the audit and the two checks read the finished build without writing to lean/.lake/
# and run side by side; when verification failed, they run one after another.
post_logs=''
post_checks_pid=''
# Invoked by the EXIT/INT/TERM traps; older ShellCheck does not trace trap callbacks.
# shellcheck disable=SC2317,SC2329
cleanup_post_checks() {
  local pid="$post_checks_pid"
  post_checks_pid=''
  if [[ -n "$pid" ]]; then
    kill -- -"$pid" 2>/dev/null || true
    wait "$pid" 2>/dev/null || true
  fi
  if [[ -n "$post_logs" ]]; then
    rm -rf "$post_logs"
    post_logs=''
  fi
}
trap cleanup_post_checks EXIT
trap 'cleanup_post_checks; exit 130' INT
trap 'cleanup_post_checks; exit 143' TERM

verified=0
step 'verification, stage one'
if ./scripts/verify.sh build-executing; then
  step 'verification, stage two'
  ./scripts/verify.sh || verified=$?
else
  verified=$?
fi
if [[ "$verified" == 0 ]]; then
  step "verification exited $verified; Regula audit beside lean-intent and frame checks"
  post_logs=$(mktemp -d)
  set -m
  (
    sub_intended=0
    ( dependency_git; ./scripts/lean.sh exe intent-check ) > "$post_logs/intent.log" 2>&1 || sub_intended=$?
    printf '%d\n' "$sub_intended" > "$post_logs/intent.status"
    sub_framed=0
    ( dependency_git; ./scripts/lean.sh exe frame-check ) > "$post_logs/frame.log" 2>&1 || sub_framed=$?
    printf '%d\n' "$sub_framed" > "$post_logs/frame.status"
  ) < /dev/null &
  post_checks_pid=$!
  set +m
  audited=0
  ( dependency_git; ./scripts/regula.sh ) || audited=$?
  post_checks_status=0
  wait "$post_checks_pid" || post_checks_status=$?
  post_checks_pid=''
  step "Regula audit exited $audited; lean-intent checks"
  if [[ -f "$post_logs/intent.log" ]]; then
    cat "$post_logs/intent.log"
  fi
  intended=1
  if [[ "$post_checks_status" == 0 && -f "$post_logs/intent.status" ]]; then
    intended=$(cat "$post_logs/intent.status")
  fi
  step "lean-intent checks exited $intended; frame check"
  if [[ -f "$post_logs/frame.log" ]]; then
    cat "$post_logs/frame.log"
  fi
  framed=1
  if [[ "$post_checks_status" == 0 && -f "$post_logs/frame.status" ]]; then
    framed=$(cat "$post_logs/frame.status")
  fi
  step "frame check exited $framed"
else
  step "verification exited $verified; Regula audit"
  audited=0
  ( dependency_git; ./scripts/regula.sh ) || audited=$?
  step "Regula audit exited $audited; lean-intent checks"
  intended=0
  ( dependency_git; ./scripts/lean.sh exe intent-check ) || intended=$?
  step "lean-intent checks exited $intended; frame check"
  framed=0
  ( dependency_git; ./scripts/lean.sh exe frame-check ) || framed=$?
  step "frame check exited $framed"
fi
[[ "$verified" == 0 && "$audited" == 0 && "$intended" == 0 && "$framed" == 0 ]] || exit 1
step 'every merge check passed'
