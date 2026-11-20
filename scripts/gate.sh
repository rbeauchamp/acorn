#!/bin/bash
# The merge gate: run the admission check of the owner's trusted base, provision the pinned
# dependencies, then run every merge check, in a Git checkout that may hold nothing but tracked
# files. no-mistakes runs it in the Test step's command (.no-mistakes.yaml).
# `./scripts/gate.sh admission` runs the admission check alone. `./scripts/gate.sh provision`
# provisions and stops, as the build that no-mistakes stores for later runs does, on a commit of
# the default branch; it runs no admission check, so it is not for a change under review.
set -euo pipefail

usage='usage: ./scripts/gate.sh [provision|admission]'
provision_only=0
admission_only=0
case "$*" in
  '') ;;
  provision) provision_only=1 ;;
  admission) admission_only=1 ;;
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

# The admission check comes first, before anything of this change is provisioned, built or run:
# a refusal ends the gate here. It is the copy of scripts/admission.sh that the commit this change
# starts from holds, never this tree's copy, so a change that edits the check is checked by the
# one it started from. Only where that commit holds no copy (it predates the check) does this
# tree's own copy run, and it still requires an admission. The starting commit is the merge base
# with the default branch of Acorn's own repository, fetched without writing a ref; the local copy
# of that branch is used, with a printed notice, only when the repository cannot be reached. Bash
# does not stop a function on a failed command while a condition is calling it, so every step
# below has its own failure branch, and no failed read of the starting commit's copy ends in a
# pass: only a tree that Git lists without the file selects this tree's copy.
admission() {
  local url=https://github.com/rbeauchamp/acorn.git listing object ref tip='' start entry script
  # Git matches a listing's pattern against trailing components of ref names, so only the line
  # whose ref name is exactly refs/heads/main is read.
  if listing=$(git ls-remote "$url" refs/heads/main 2>/dev/null); then
    while read -r object ref; do
      if [[ $ref == refs/heads/main && $object =~ ^[0-9a-f]{40}$ ]]; then tip=$object; fi
    done <<< "$listing"
  fi
  if [[ -n $tip ]]; then
    git fetch --quiet --no-tags --no-write-fetch-head "$url" "$tip" 2>/dev/null || tip=''
  fi
  if [[ -z $tip ]]; then
    tip=refs/remotes/origin/main
    echo "admission: could not reach $url, so the check is selected by the checkout's copy of the default branch, which may be stale or another repository's"
  fi
  start=$(git merge-base HEAD "$tip") || {
    echo "admission: HEAD and the default branch have no merge base, so the change has no starting commit" >&2
    return 1
  }
  entry=$(git ls-tree "$start" -- scripts/admission.sh) || {
    echo "admission: could not list the tree of the starting commit $start" >&2
    return 1
  }
  if [[ -z $entry ]]; then
    ./scripts/admission.sh
    return
  fi
  script=$(git show "$start:scripts/admission.sh") || {
    echo "admission: could not read the admission check of the starting commit $start" >&2
    return 1
  }
  [[ -n $script ]] || {
    echo "admission: the admission check of the starting commit $start is empty" >&2
    return 1
  }
  bash -c "$script" acorn-admission
}
if [[ "$provision_only" == 0 ]]; then
  step 'admission of changes to the owner paths'
  if ! admission; then
    step 'admission refused: this run of the gate provisioned, built and ran nothing of this change'
    exit 1
  fi
  step 'admitted'
  [[ "$admission_only" == 0 ]] || exit 0
fi

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
[[ "$provision_only" == 0 ]] || exit 0

# The two stages of ordinary verification, each under its own 360-second deadline, then
# the Regula audit (scripts/regula.sh: Regula's proof verdict, by the two commands its release
# publishes) on its own build with no deadline, then lean-intent's two checks with no deadline:
# intent-check (lean/AcornTools/Intent.lean) runs the confirmation check and the implementation
# check on one list of modules, those Lake lists for the default libraries, and passes only when the
# first finds nothing and the second finds only the deliverables its closed list names as awaiting
# an implementation. Last, frame-check (lean/AcornTools/Frame.lean) compares each target's pin
# file, if it has one, with the declarations the target reads in the finished build, and the
# registration of the landed missions' statements with the record of landings. The audit and the
# checks run even when an earlier step fails, so one run reports all four.
step 'verification, stage one'
verified=0
if ./scripts/verify.sh build-executing; then
  step 'verification, stage two'
  ./scripts/verify.sh || verified=$?
else
  verified=$?
fi
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
[[ "$verified" == 0 && "$audited" == 0 && "$intended" == 0 && "$framed" == 0 ]] || exit 1
step 'every merge check passed'
