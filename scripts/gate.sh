#!/bin/bash
# The merge gate: provision the pinned dependencies, then run every merge check, in a
# Git checkout that may hold nothing but tracked files. no-mistakes runs it as the
# Test step's command (.no-mistakes.yaml); `./scripts/gate.sh provision` stops after
# provisioning, as the build that no-mistakes stores for later runs does.
#
# The checks form groups, each a sequence of checks on one build. `./scripts/gate.sh groups`
# prints the groups' names, one to a line, and `./scripts/gate.sh group NAME` runs the checks
# of one group without provisioning, for a caller that has provisioned the dependencies
# itself. The verification workflow (.github/workflows/verify.yml) makes one job of each name
# the first prints and runs the second in it, so the checks GitHub runs on a pull request are
# the ones this file runs, taken from this file.
set -euo pipefail

usage='usage: ./scripts/gate.sh [provision | groups | group NAME]'
groups=(verification audit)
group=
case "$#:${1-}" in
  0:) mode=all ;;
  1:provision) mode=provision ;;
  1:groups) printf '%s\n' "${groups[@]}"; exit 0 ;;
  2:group)
    mode=group
    for name in "${groups[@]}"; do
      [[ "$name" != "$2" ]] || group=$name
    done
    [[ -n "$group" ]] || { echo "$usage" >&2; exit 2; } ;;
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

provision() {
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
    # FloatLib and lean-intent publish no build cache. This builds the modules the proof bridge
    # imports, the lean-intent modules the intent bridge and intent-check import with the native
    # objects intent-check links, and the Regula interface modules the decision registries import.
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
}

# The checks of one group. Each check reports its exit status, and a group fails when any of
# its checks failed.
#
# verification: the two stages of ordinary verification, each under its own 360-second
# deadline; the second runs only when the first passed.
#
# audit: the Regula audit (scripts/regula.sh: Regula's proof verdict, by the two commands its
# release publishes) on its own build with no deadline, then lean-intent's two checks with no
# deadline: intent-check (lean/AcornTools/Intent.lean) runs the confirmation check and the
# implementation check on one list of modules, those Lake lists for the default libraries, and
# passes only when the first finds nothing and the second finds only the deliverables its closed
# list names as awaiting an implementation. Last, frame-check (lean/AcornTools/Frame.lean)
# compares each target's pin file, if it has one, with the declarations the target reads in the
# finished build. Each of the three runs even when an earlier one failed.
run_group() {
  local verified=0 audited=0 intended=0 framed=0
  case "$1" in
    verification)
      step 'verification, stage one'
      if ./scripts/verify.sh build-executing; then
        step 'verification, stage two'
        ./scripts/verify.sh || verified=$?
      else
        verified=$?
      fi
      step "verification exited $verified"
      [[ "$verified" == 0 ]] ;;
    audit)
      step 'Regula audit'
      ( dependency_git; ./scripts/regula.sh ) || audited=$?
      step "Regula audit exited $audited; lean-intent checks"
      ( dependency_git; ./scripts/lean.sh exe intent-check ) || intended=$?
      step "lean-intent checks exited $intended; frame check"
      ( dependency_git; ./scripts/lean.sh exe frame-check ) || framed=$?
      step "frame check exited $framed"
      [[ "$audited" == 0 && "$intended" == 0 && "$framed" == 0 ]] ;;
    *)
      echo "gate: no checks are defined for the group $1" >&2
      return 2 ;;
  esac
}

if [[ "$mode" == group ]]; then
  run_group "$group" || exit 1
  step "every check of the group $group passed"
  exit 0
fi

provision
[[ "$mode" == all ]] || exit 0

# Every group runs even when an earlier one failed, so one run reports them all.
failed=0
for name in "${groups[@]}"; do
  run_group "$name" || failed=1
done
[[ "$failed" == 0 ]] || exit 1
step 'every merge check passed'
