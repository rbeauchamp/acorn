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

nc_pin='lean/no-comments.pin'
admit_tracked_helper . 1 || {
  echo "gate: scripts/tracked-files.sh failed pre-execution Git admission" >&2
  exit 1
}
./scripts/tracked-files.sh admit-file --clean . \
  scripts/tracked-files.sh scripts/gate.sh scripts/lean.sh scripts/verify.sh scripts/regula.sh "$nc_pin"
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
    kill -TERM -- -"$pid" 2>/dev/null || true
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

format_duration() {
  local secs="$1"
  printf '%dm %02ds (%d s)' $((secs / 60)) $((secs % 60)) "$secs"
}

detect_nc_jobs() {
  local cpus=4 jobs
  if command -v nproc >/dev/null 2>&1; then
    cpus=$(nproc 2>/dev/null || echo 4)
  elif command -v sysctl >/dev/null 2>&1; then
    cpus=$(sysctl -n hw.logicalcpu 2>/dev/null || echo 4)
  fi
  if [[ ! "$cpus" =~ ^[0-9]+$ ]] || (( cpus < 1 )); then
    cpus=4
  fi
  jobs=$((cpus - 1))
  if (( jobs < 1 )); then
    jobs=1
  elif (( jobs > 6 )); then
    jobs=6
  fi
  printf '%d\n' "$jobs"
}

emit_budget_warning() {
  local phase="$1" actual="$2" budget="$3"
  if [[ "${GITHUB_ACTIONS:-}" == 'true' ]]; then
    printf '::warning title=Verify / gate budget::%s took %s (target <= %s).\n' \
      "$phase" "$(format_duration "$actual")" "$(format_duration "$budget")"
  else
    printf 'gate: budget warning: %s took %s (target <= %s)\n' \
      "$phase" "$(format_duration "$actual")" "$(format_duration "$budget")"
  fi
}

status_label() {
  local rc="$1" over="$2"
  if [[ "$rc" == 'skipped' || "$rc" == 'refused' ]]; then
    printf '%s' "$rc"
  elif [[ "$rc" == '0' ]]; then
    if [[ "$over" == '1' ]]; then
      printf 'ok (over budget)'
    else
      printf 'ok'
    fi
  elif [[ "$rc" == '137' ]]; then
    printf 'timed out (SIGKILL, exit 137)'
  else
    printf 'failed (exit %s)' "$rc"
  fi
}

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

provision_start="$SECONDS"
step 'provisioning the pinned dependencies'
(
  # Parallel cache extraction can exhaust macOS's inherited 256-descriptor limit.
  # Give provisioning a process-local floor before Lake can fetch dependencies;
  # preserve higher limits and the hard limit. This is a budget, not a peak bound.
  descriptor_limit=$(ulimit -Sn)
  if [[ "$descriptor_limit" != unlimited ]] && (( descriptor_limit < 4096 )); then
    ulimit -Sn 4096
  fi
  ./scripts/tracked-files.sh sync-config --clean --admit-manifest .
  dependency_git
  cd lean
  # Lake decides whether Mathlib and Regula's lint driver need provisioning: with
  # --no-build it exits 3 unless every artifact and trace of these targets is current.
  current=0
  lake -f lakefile.lean build --no-build Mathlib regula/lint || current=$?
  case "$current" in
    0) ;;
    3)
      # The upstream cache can omit modules; Lake compiles only those it lacks.
      lake -f lakefile.lean exe cache get
      lake -f lakefile.lean build Mathlib regula/lint ;;
    *) exit "$current" ;;
  esac
  # FloatLib, lean-intent and Regula publish no build cache. This builds the modules the proof
  # bridge imports, the lean-intent modules the intent bridge and intent-check import with the
  # native objects intent-check links, and the Regula modules the decision registries and
  # AcornTools.Theorems import with their native objects.
  lake -f lakefile.lean build floatlibBridge regulaInterface leanIntentBridge leanIntentNative
)
./scripts/lean.sh provision-status
./scripts/tracked-files.sh admit-site --clean .
(
  dependency_git
  cd site
  # Verso's modules and the shared library its documents load.
  lake -f lakefile.toml build verso/VersoManual verso/VersoManual:shared
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
provision_dur=$((SECONDS - provision_start))
step 'provisioned'
[[ "$provision_only" == 0 ]] || exit 0

if command -v gtimeout >/dev/null 2>&1; then
  timeout_command=gtimeout
elif command -v timeout >/dev/null 2>&1; then
  timeout_command=timeout
else
  echo "gate: GNU coreutils timeout is required (macOS: brew install coreutils)" >&2
  exit 127
fi
if [[ $("$timeout_command" --version) != *"GNU coreutils"* ]]; then
  echo "gate: GNU coreutils timeout is required" >&2
  exit 127
fi

# Per-check hard process-group SIGKILL deadlines (matching verify.sh's 360-second
# no-grace-period discipline) and early-warning target budgets in seconds.
regula_timeout_s=360
intent_timeout_s=180
frame_timeout_s=120
nc_timeout_s=300
provision_budget_s=480
verify_budget_s=360
regula_budget_s=240
nc_budget_s=180
gate_budget_s=600
job_budget_s=900

# The two stages of ordinary verification, each under its own 360-second deadline, then
# the Regula audit (scripts/regula.sh: Regula's proof verdict, by the two commands its release
# publishes) under its own 360-second deadline, lean-intent's two checks (180-second deadline):
# intent-check (lean/AcornTools/Intent.lean) runs the confirmation check and the implementation
# check on one list of modules, those Lake lists for the default libraries, and passes only when the
# first finds nothing and the second finds only the deliverables its closed list names as awaiting
# an implementation. Next, frame-check (lean/AcornTools/Frame.lean, 120-second deadline) compares
# each target's pin file, if it has one, with the declarations the target reads in the finished
# build. Last, because the pinned no-comments binary (lean/no-comments.pin) elaborates scoped Lean
# files, it runs (under its 300-second deadline) only when ordinary verification succeeded
# (guaranteeing source admission passed first), after cache-containment, offline SHA-256 and
# tracked-file admission (.no-comments.json, comment-ratchet.json, lean/no-comments.pin); when
# verification failed, no-comments is refused without elaborating un-admitted sources. The Regula
# audit and the intent and frame checks run even when an earlier step fails. When ordinary
# verification passed, every module and executable is already built and
# lean/.lake/acorn-path-packages.json is current, so after admitting no-comments upfront, the
# Regula audit runs in the foreground while lean-intent, frame-check and (when admitted)
# no-comments run one after another in a background subshell without writing to lean/.lake/ or
# site/.lake/, capping no-comments workers to leave one core for Regula and stay within the memory
# budget; when verification failed, Regula, lean-intent and frame-check run one after another.

verified=0
stage1_status=0
stage2_status='skipped'
stage1_dur=0
stage2_dur=0
stage1_start="$SECONDS"
step 'verification, stage one'
if ./scripts/verify.sh build-executing; then
  stage1_dur=$((SECONDS - stage1_start))
  stage2_start="$SECONDS"
  step 'verification, stage two'
  stage2_status=0
  ./scripts/verify.sh || stage2_status=$?
  stage2_dur=$((SECONDS - stage2_start))
  verified="$stage2_status"
else
  stage1_status=$?
  stage1_dur=$((SECONDS - stage1_start))
  verified="$stage1_status"
fi
verify_dur=$((stage1_dur + stage2_dur))

audited=0
intended=0
framed=0
commented=0
regula_dur=0
intent_dur=0
frame_dur=0
nc_dur=0
nc_jobs=$(detect_nc_jobs)
nc_refusal=''
nc_admitted=0
post_mode='serial'
post_start="$SECONDS"

if [[ "$verified" == 0 ]]; then
  post_mode='overlapped'
  nc_admit_start="$SECONDS"
  if ! check_nc_cache_dirs require-present; then
    nc_refusal='integrity'
    commented=1
  elif ! verify_sha256 "$nc_sha256" "$nc_bin"; then
    echo "gate: offline SHA-256 verification failed for $nc_bin" >&2
    nc_refusal='integrity'
    commented=1
  elif ! ./scripts/tracked-files.sh admit-no-comments --clean .; then
    nc_refusal='admit'
    commented=1
  else
    nc_admitted=1
  fi
  nc_admit_dur=$((SECONDS - nc_admit_start))

  nc_args=(check --jobs "$nc_jobs")
  if [[ -n "${ACORN_BASE_REF:-}" ]]; then
    nc_args+=(--base-ref "$ACORN_BASE_REF")
  fi

  if [[ "$nc_admitted" == 1 ]]; then
    step "verification exited $verified; Regula audit beside lean-intent, frame and no-comments checks"
  else
    step "verification exited $verified; Regula audit beside lean-intent and frame checks"
  fi
  post_logs=$(mktemp -d)
  set -m
  (
    bg_child_pid=''
    # Invoked by the background subshell's EXIT/INT/TERM traps.
    # shellcheck disable=SC2317,SC2329
    cleanup_bg_child() {
      if [[ -n "$bg_child_pid" ]]; then
        kill -KILL -- -"$bg_child_pid" 2>/dev/null || true
        kill -KILL "$bg_child_pid" 2>/dev/null || true
        wait "$bg_child_pid" 2>/dev/null || true
        bg_child_pid=''
      fi
    }
    trap cleanup_bg_child EXIT
    trap 'cleanup_bg_child; exit 130' INT
    trap 'cleanup_bg_child; exit 143' TERM

    run_bg_bounded() {
      local limit_s="$1" log_file="$2" status_file="$3" dur_file="$4"
      shift 4
      local t0="$SECONDS" rc=0
      ( dependency_git; exec "$timeout_command" --signal=KILL "${limit_s}s" "$@" ) > "$log_file" 2>&1 < /dev/null &
      bg_child_pid=$!
      wait "$bg_child_pid" || rc=$?
      bg_child_pid=''
      printf '%d\n' "$rc" > "$status_file"
      printf '%d\n' $((SECONDS - t0)) > "$dur_file"
    }

    run_bg_bounded "$intent_timeout_s" "$post_logs/intent.log" "$post_logs/intent.status" "$post_logs/intent.dur" \
      ./scripts/lean.sh exe intent-check
    run_bg_bounded "$frame_timeout_s" "$post_logs/frame.log" "$post_logs/frame.status" "$post_logs/frame.dur" \
      ./scripts/lean.sh exe frame-check
    if [[ "$nc_admitted" == 1 ]]; then
      run_bg_bounded "$nc_timeout_s" "$post_logs/no-comments.log" "$post_logs/no-comments.status" "$post_logs/no-comments.dur" \
        "$nc_bin" "${nc_args[@]}"
    fi
  ) < /dev/null &
  post_checks_pid=$!
  set +m

  regula_start="$SECONDS"
  ( dependency_git; exec "$timeout_command" --signal=KILL "${regula_timeout_s}s" ./scripts/regula.sh ) || audited=$?
  regula_dur=$((SECONDS - regula_start))

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
  if [[ -f "$post_logs/intent.dur" ]]; then
    intent_dur=$(cat "$post_logs/intent.dur")
  fi

  step "lean-intent checks exited $intended; frame check"
  if [[ -f "$post_logs/frame.log" ]]; then
    cat "$post_logs/frame.log"
  fi
  framed=1
  if [[ "$post_checks_status" == 0 && -f "$post_logs/frame.status" ]]; then
    framed=$(cat "$post_logs/frame.status")
  fi
  if [[ -f "$post_logs/frame.dur" ]]; then
    frame_dur=$(cat "$post_logs/frame.dur")
  fi

  step "frame check exited $framed; no-comments check"
  if [[ "$nc_refusal" == 'integrity' ]]; then
    commented=1
    nc_dur="$nc_admit_dur"
    step 'no-comments check refused (integrity check failed)'
  elif [[ "$nc_refusal" == 'admit' ]]; then
    commented=1
    nc_dur="$nc_admit_dur"
    step "no-comments check exited $commented"
  else
    if [[ -f "$post_logs/no-comments.log" ]]; then
      cat "$post_logs/no-comments.log"
    fi
    commented=1
    if [[ "$post_checks_status" == 0 && -f "$post_logs/no-comments.status" ]]; then
      commented=$(cat "$post_logs/no-comments.status")
    fi
    nc_exec_dur=0
    if [[ -f "$post_logs/no-comments.dur" ]]; then
      nc_exec_dur=$(cat "$post_logs/no-comments.dur")
    fi
    nc_dur=$((nc_admit_dur + nc_exec_dur))
    step "no-comments check exited $commented"
  fi
else
  step "verification exited $verified; Regula audit"
  regula_start="$SECONDS"
  ( dependency_git; exec "$timeout_command" --signal=KILL "${regula_timeout_s}s" ./scripts/regula.sh ) || audited=$?
  regula_dur=$((SECONDS - regula_start))

  step "Regula audit exited $audited; lean-intent checks"
  intent_start="$SECONDS"
  ( dependency_git; exec "$timeout_command" --signal=KILL "${intent_timeout_s}s" ./scripts/lean.sh exe intent-check ) || intended=$?
  intent_dur=$((SECONDS - intent_start))

  step "lean-intent checks exited $intended; frame check"
  frame_start="$SECONDS"
  ( dependency_git; exec "$timeout_command" --signal=KILL "${frame_timeout_s}s" ./scripts/lean.sh exe frame-check ) || framed=$?
  frame_dur=$((SECONDS - frame_start))

  step "frame check exited $framed; no-comments check"
  echo "gate: refusing no-comments check because verification exited $verified" >&2
  nc_refusal='verification'
  commented=1
  step 'no-comments check refused (verification failed)'
fi
post_wall_dur=$((SECONDS - post_start))
gate_total_dur="$SECONDS"

job_total_dur=''
if [[ "${ACORN_JOB_START_EPOCH:-}" =~ ^[0-9]+$ ]]; then
  now_epoch=$(date +%s)
  if (( now_epoch >= ACORN_JOB_START_EPOCH )); then
    job_total_dur=$((now_epoch - ACORN_JOB_START_EPOCH))
  fi
fi

verify_over=0
if (( verify_dur > verify_budget_s )); then
  verify_over=1
  emit_budget_warning 'Verification stages 1+2' "$verify_dur" "$verify_budget_s"
fi
regula_over=0
if (( regula_dur > regula_budget_s )); then
  regula_over=1
  emit_budget_warning 'Regula audit' "$regula_dur" "$regula_budget_s"
fi
nc_over=0
if [[ -z "$nc_refusal" ]] && (( nc_dur > nc_budget_s )); then
  nc_over=1
  emit_budget_warning 'no-comments check' "$nc_dur" "$nc_budget_s"
fi
gate_over=0
if (( gate_total_dur > gate_budget_s )); then
  gate_over=1
  emit_budget_warning 'Merge gate (scripts/gate.sh)' "$gate_total_dur" "$gate_budget_s"
fi
job_over=0
if [[ -n "$job_total_dur" ]] && (( job_total_dur > job_budget_s )); then
  job_over=1
  emit_budget_warning 'Total Verify / gate job' "$job_total_dur" "$job_budget_s"
fi

if [[ -n "${GITHUB_STEP_SUMMARY:-}" && ! -L "$GITHUB_STEP_SUMMARY" && ( ! -e "$GITHUB_STEP_SUMMARY" || -f "$GITHUB_STEP_SUMMARY" ) ]]; then
  {
    printf '## Verify / gate phase timings\n\n'
    printf '| Phase | Duration | Target budget | Hard limit | Status |\n'
    printf '|---|---:|---:|---:|---|\n'
    if [[ "${ACORN_PROVISION_SECONDS:-}" =~ ^[0-9]+$ ]]; then
      prov_over=0
      if (( ACORN_PROVISION_SECONDS > provision_budget_s )); then
        prov_over=1
      fi
      printf '| Provision pinned dependencies | %s | <= %s | 12m | %s |\n' \
        "$(format_duration "$ACORN_PROVISION_SECONDS")" \
        "$(format_duration "$provision_budget_s")" \
        "$(status_label 0 "$prov_over")"
    fi
    printf '| Gate dependency re-check | %s | - | - | ok |\n' \
      "$(format_duration "$provision_dur")"
    printf '| Verification stage 1 (build-executing) | %s | - | %s | %s |\n' \
      "$(format_duration "$stage1_dur")" \
      "$(format_duration 360)" \
      "$(status_label "$stage1_status" 0)"
    if [[ "$stage2_status" == 'skipped' ]]; then
      printf '| Verification stage 2 (verify.sh) | - | <= %s (stages 1+2) | %s | skipped |\n' \
        "$(format_duration "$verify_budget_s")" \
        "$(format_duration 360)"
    else
      printf '| Verification stage 2 (verify.sh) | %s | <= %s (stages 1+2) | %s | %s |\n' \
        "$(format_duration "$stage2_dur")" \
        "$(format_duration "$verify_budget_s")" \
        "$(format_duration 360)" \
        "$(status_label "$stage2_status" "$verify_over")"
    fi
    printf '| Regula audit (scripts/regula.sh) | %s | <= %s | %s | %s |\n' \
      "$(format_duration "$regula_dur")" \
      "$(format_duration "$regula_budget_s")" \
      "$(format_duration "$regula_timeout_s")" \
      "$(status_label "$audited" "$regula_over")"
    printf '| lean-intent checks (intent-check) | %s | - | %s | %s |\n' \
      "$(format_duration "$intent_dur")" \
      "$(format_duration "$intent_timeout_s")" \
      "$(status_label "$intended" 0)"
    printf '| Frame check (frame-check) | %s | - | %s | %s |\n' \
      "$(format_duration "$frame_dur")" \
      "$(format_duration "$frame_timeout_s")" \
      "$(status_label "$framed" 0)"
    if [[ "$nc_refusal" == 'admit' ]]; then
      printf '| no-comments check | %s | <= %s | %s | failed (admission) |\n' \
        "$(format_duration "$nc_dur")" \
        "$(format_duration "$nc_budget_s")" \
        "$(format_duration "$nc_timeout_s")"
    elif [[ -n "$nc_refusal" ]]; then
      printf '| no-comments check | %s | <= %s | %s | refused (%s) |\n' \
        "$(format_duration "$nc_dur")" \
        "$(format_duration "$nc_budget_s")" \
        "$(format_duration "$nc_timeout_s")" \
        "$nc_refusal"
    else
      printf '| no-comments check (--jobs %s) | %s | <= %s | %s | %s |\n' \
        "$nc_jobs" \
        "$(format_duration "$nc_dur")" \
        "$(format_duration "$nc_budget_s")" \
        "$(format_duration "$nc_timeout_s")" \
        "$(status_label "$commented" "$nc_over")"
    fi
    printf '| Post-verification wall (%s) | %s | - | - | - |\n' \
      "$post_mode" \
      "$(format_duration "$post_wall_dur")"
    gate_rc=0
    if [[ "$verified" != 0 || "$audited" != 0 || "$intended" != 0 || "$framed" != 0 || "$commented" != 0 ]]; then
      gate_rc=1
    fi
    printf '| **Merge gate total (scripts/gate.sh)** | **%s** | **<= %s** | **13m** | **%s** |\n' \
      "$(format_duration "$gate_total_dur")" \
      "$(format_duration "$gate_budget_s")" \
      "$(status_label "$gate_rc" "$gate_over")"
    if [[ -n "$job_total_dur" ]]; then
      printf '| **Total Verify / gate job** | **%s** | **<= %s** | **20m** | **%s** |\n' \
        "$(format_duration "$job_total_dur")" \
        "$(format_duration "$job_budget_s")" \
        "$(status_label "$gate_rc" "$job_over")"
    fi
    printf '\n'
  } >> "$GITHUB_STEP_SUMMARY"
fi

printf 'gate: phase timings (s): provision=%d stage1=%d stage2=%d regula=%d intent=%d frame=%d no-comments=%d post-wall=%d (%s, nc-jobs=%d) total=%d\n' \
  "$provision_dur" "$stage1_dur" "$stage2_dur" "$regula_dur" "$intent_dur" "$frame_dur" "$nc_dur" "$post_wall_dur" "$post_mode" "$nc_jobs" "$gate_total_dur"
[[ "$verified" == 0 && "$audited" == 0 && "$intended" == 0 && "$framed" == 0 && "$commented" == 0 ]] || exit 1
step 'every merge check passed'
