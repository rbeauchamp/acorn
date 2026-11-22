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

nc_pin='lean/no-comments.pin'
if [[ -L lean || ! -d lean || ! -f "$nc_pin" || -L "$nc_pin" ]]; then
  echo "gate: missing or non-regular pin file: $nc_pin" >&2
  exit 1
fi
{
  IFS= read -r nc_line1 &&
    IFS= read -r nc_line2 &&
    IFS= read -r nc_line3 &&
    ! IFS= read -r nc_extra &&
    [[ -z "$nc_extra" ]]
} < "$nc_pin" || {
  echo "gate: malformed pin file: $nc_pin" >&2
  exit 1
}
if [[ ! $nc_line1 =~ ^VERSION=(v[0-9]+\.[0-9]+\.[0-9]+)$ ]] ||
    [[ ! $nc_line2 =~ ^DARWIN_SHA256=([0-9a-f]{64})$ ]] ||
    [[ ! $nc_line3 =~ ^LINUX_SHA256=([0-9a-f]{64})$ ]]; then
  echo "gate: malformed pin values in $nc_pin" >&2
  exit 1
fi
nc_version="${nc_line1#VERSION=}"
nc_darwin_sha256="${nc_line2#DARWIN_SHA256=}"
nc_linux_sha256="${nc_line3#LINUX_SHA256=}"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    nc_target='darwin-arm64'
    nc_sha256="$nc_darwin_sha256" ;;
  Linux-x86_64)
    nc_target='linux-x86_64'
    nc_sha256="$nc_linux_sha256" ;;
  *)
    echo "gate: unsupported platform for no-comments: $(uname -s)-$(uname -m)" >&2
    exit 1 ;;
esac

verify_sha256() {
  local expected="$1" file="$2" actual
  [[ -f "$file" && ! -L "$file" ]] || return 1
  if ! command -v openssl >/dev/null 2>&1; then
    echo 'gate: OpenSSL is unavailable for SHA-256 verification' >&2
    return 1
  fi
  actual=$(openssl dgst -sha256 -r "$file" | awk '{print $1}') || return 1
  [[ "$actual" == "$expected" ]]
}

nc_pkg_dir='lean/.lake/packages'
nc_root="$nc_pkg_dir/.no-comments"
nc_dir="$nc_root/$nc_version"
nc_bin="$nc_dir/no-comments"

check_nc_cache_dirs() {
  local mode="$1" dir
  for dir in lean lean/.lake "$nc_pkg_dir"; do
    if [[ -L "$dir" || ! -d "$dir" ]]; then
      echo "gate: cache parent must be a real directory: $dir" >&2
      return 1
    fi
  done
  for dir in "$nc_root" "$nc_dir"; do
    if [[ -L "$dir" ]]; then
      echo "gate: refusing symlinked cache directory: $dir" >&2
      return 1
    elif [[ -e "$dir" && ! -d "$dir" ]]; then
      echo "gate: refusing non-directory cache path: $dir" >&2
      return 1
    elif [[ ! -d "$dir" && "$mode" != allow-missing ]]; then
      echo "gate: missing cache directory: $dir" >&2
      return 1
    fi
  done
}

ensure_nc_cache_dirs() {
  check_nc_cache_dirs allow-missing || return 1
  [[ -d "$nc_root" ]] || mkdir "$nc_root" || return 1
  [[ -d "$nc_dir" ]] || mkdir "$nc_dir" || return 1
  check_nc_cache_dirs require-present
}

nc_tmp=''
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
  if [[ -n "$nc_tmp" ]]; then
    rm -rf "$nc_tmp"
    nc_tmp=''
  fi
}
trap cleanup_post_checks EXIT
trap 'cleanup_post_checks; exit 130' INT
trap 'cleanup_post_checks; exit 143' TERM

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
check_nc_cache_dirs allow-missing
if [[ ! -L "$nc_bin" && -e "$nc_bin" && ! -f "$nc_bin" ]]; then
  echo "gate: refusing unexpected non-regular cache entry: $nc_bin" >&2
  exit 1
fi
if verify_sha256 "$nc_sha256" "$nc_bin"; then
  [[ -x "$nc_bin" ]] || chmod 755 "$nc_bin"
else
  if [[ -L "$nc_bin" ]]; then
    echo "gate: removing symlinked $nc_bin; re-downloading" >&2
    rm -f "$nc_bin"
  elif [[ -f "$nc_bin" ]]; then
    echo "gate: cached $nc_bin failed SHA-256 verification; re-downloading" >&2
  fi
  nc_tmp=$(mktemp -d)
  curl --fail --silent --show-error --location --proto '=https' --tlsv1.2 \
    --connect-timeout 10 --max-time 180 --retry 2 --retry-delay 2 --retry-max-time 300 \
    --output "$nc_tmp/no-comments" \
    "https://github.com/rbeauchamp/lean-no-comments/releases/download/${nc_version}/no-comments-${nc_target}"
  if ! verify_sha256 "$nc_sha256" "$nc_tmp/no-comments"; then
    echo "gate: downloaded no-comments-${nc_target} failed SHA-256 verification" >&2
    exit 1
  fi
  ensure_nc_cache_dirs
  if [[ -L "$nc_bin" || ( -e "$nc_bin" && ! -f "$nc_bin" ) ]]; then
    echo "gate: refusing unexpected non-regular cache entry: $nc_bin" >&2
    exit 1
  fi
  chmod 755 "$nc_tmp/no-comments"
  mv -f "$nc_tmp/no-comments" "$nc_bin"
  rmdir "$nc_tmp"
  nc_tmp=''
fi
step 'provisioned'
[[ "$provision_only" == 0 ]] || exit 0

# The two stages of ordinary verification, each under its own 360-second deadline, then
# the Regula audit (scripts/regula.sh: Regula's proof verdict, by the two commands its release
# publishes) on its own build with no deadline, lean-intent's two checks with no deadline:
# intent-check (lean/AcornTools/Intent.lean) runs the confirmation check and the implementation
# check on one list of modules, those Lake lists for the default libraries, and passes only when the
# first finds nothing and the second finds only the deliverables its closed list names as awaiting
# an implementation. Next, frame-check (lean/AcornTools/Frame.lean) compares each target's pin
# file, if it has one, with the declarations the target reads in the finished build. Last, because
# the pinned no-comments binary (lean/no-comments.pin) elaborates scoped Lean files, it runs
# serially after Regula only when ordinary verification succeeded (guaranteeing source admission
# passed first), offline-verified by SHA-256 and enforcing the ratcheted comment ban across lean/
# and site/ code (.no-comments.json, comment-ratchet.json); when verification failed, no-comments is
# refused without elaborating un-admitted sources. The Regula audit and the intent and frame checks
# run even when an earlier step fails. When ordinary verification passed, every module and
# executable is already built and lean/.lake/acorn-path-packages.json is current, so the audit and
# the intent/frame checks read the finished build without writing to lean/.lake/ and run side by
# side; when verification failed, they run one after another.

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
fi
step "frame check exited $framed; no-comments check"
commented=0
if [[ "$verified" != 0 ]]; then
  echo "gate: refusing no-comments check because verification exited $verified" >&2
  commented=1
  step 'no-comments check refused (verification failed)'
elif ! check_nc_cache_dirs require-present; then
  commented=1
  step 'no-comments check refused (integrity check failed)'
elif ! verify_sha256 "$nc_sha256" "$nc_bin"; then
  echo "gate: offline SHA-256 verification failed for $nc_bin" >&2
  commented=1
  step 'no-comments check refused (integrity check failed)'
else
  nc_args=(check --bootstrap)
  if [[ -n "${ACORN_BASE_REF:-}" ]]; then
    nc_args+=(--base-ref "$ACORN_BASE_REF")
  fi
  ( dependency_git; "$nc_bin" "${nc_args[@]}" ) || commented=$?
  step "no-comments check exited $commented"
fi
[[ "$verified" == 0 && "$audited" == 0 && "$intended" == 0 && "$framed" == 0 && "$commented" == 0 ]] || exit 1
step 'every merge check passed'
