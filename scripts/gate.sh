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

gate_scratch=''
post_logs=''
post_checks_pid=''
fg_child_pid=''
summary_written=0
bg_supervisor_launched=0

# Per-check hard process-group SIGKILL deadlines (matching verify.sh's 360-second
# no-grace-period discipline) and early-warning target budgets in seconds.
nc_admit_timeout_s=60
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

provision_dur=0
provision_state='running'
stage1_dur=0
stage1_state='not reached'
stage2_dur=0
stage2_state='not reached'
nc_admit_dur=0
nc_admit_state='not reached'
regula_dur=0
regula_state='not reached'
intent_dur=''
intent_state='not reached'
frame_dur=''
frame_state='not reached'
nc_exec_dur=''
nc_state='not reached'
post_wall_dur=0
post_start=''
post_mode='serial'
post_checks_status=0
nc_jobs=''
nc_refusal=''
verified=1
audited=1
intended=1
framed=1
commented=1

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
  local state="$1" over="$2"
  if [[ "$state" == '0' ]]; then
    if [[ "$over" == '1' ]]; then
      printf 'ok (over budget)'
    else
      printf 'ok'
    fi
  elif [[ "$state" == '137' ]]; then
    printf 'killed (SIGKILL / timeout, exit 137)'
  elif [[ "$state" =~ ^[0-9]+$ ]]; then
    printf 'failed (exit %s)' "$state"
  else
    printf '%s' "$state"
  fi
}

summary_phase_state() {
  local state="$1" early_abort="$2"
  if [[ "$early_abort" == 1 && "$state" == 'running' ]]; then
    printf 'interrupted / unfinished'
  else
    printf '%s' "$state"
  fi
}

summary_phase_dur() {
  local state="$1" dur="$2"
  case "$state" in
    'not reached'|'skipped'|'skipped ('*|'interrupted / unfinished'|'status unavailable'|'refused ('*)
      printf '%s' '-' ;;
    *)
      if [[ "$dur" =~ ^[0-9]+$ ]]; then
        format_duration "$dur"
      else
        printf '%s' 'unavailable'
      fi ;;
  esac
}

summary_phase_secs() {
  local state="$1" dur="$2"
  case "$state" in
    'not reached'|'skipped'|'skipped ('*|'interrupted / unfinished'|'status unavailable'|'refused ('*)
      printf '%s' '-' ;;
    *)
      if [[ "$dur" =~ ^[0-9]+$ ]]; then
        printf '%s' "$dur"
      else
        printf '%s' 'unavailable'
      fi ;;
  esac
}

# Inspect actual start/completion marker files written by the background subshell so
# completed checks stay observed even on early cancellation or later supervisor failure,
# and unstarted checks report `not reached` rather than `interrupted`.
# shellcheck disable=SC2317,SC2329
sync_bg_phase_state() {
  local early_abort="$1"
  local raw='' dur_raw=''
  [[ "$bg_supervisor_launched" == 1 && -n "$post_logs" ]] || return 0

  if [[ -f "$post_logs/intent.status" ]]; then
    raw=$(cat "$post_logs/intent.status" 2>/dev/null || true)
    if [[ "$raw" =~ ^[0-9]+$ ]]; then
      intended="$raw"
      intent_state="$raw"
    elif [[ "$early_abort" == 1 ]]; then
      intent_state='interrupted / unfinished'
    else
      intent_state='status unavailable'
    fi
  elif [[ -f "$post_logs/intent.started" ]]; then
    if [[ "$early_abort" == 1 ]]; then
      intent_state='interrupted / unfinished'
    else
      intent_state='status unavailable'
    fi
  fi
  if [[ -f "$post_logs/intent.dur" ]]; then
    dur_raw=$(cat "$post_logs/intent.dur" 2>/dev/null || true)
    if [[ "$dur_raw" =~ ^[0-9]+$ ]]; then
      intent_dur="$dur_raw"
    fi
  fi

  if [[ -f "$post_logs/frame.status" ]]; then
    raw=$(cat "$post_logs/frame.status" 2>/dev/null || true)
    if [[ "$raw" =~ ^[0-9]+$ ]]; then
      framed="$raw"
      frame_state="$raw"
    elif [[ "$early_abort" == 1 ]]; then
      frame_state='interrupted / unfinished'
    else
      frame_state='status unavailable'
    fi
  elif [[ -f "$post_logs/frame.started" ]]; then
    if [[ "$early_abort" == 1 ]]; then
      frame_state='interrupted / unfinished'
    else
      frame_state='status unavailable'
    fi
  fi
  if [[ -f "$post_logs/frame.dur" ]]; then
    dur_raw=$(cat "$post_logs/frame.dur" 2>/dev/null || true)
    if [[ "$dur_raw" =~ ^[0-9]+$ ]]; then
      frame_dur="$dur_raw"
    fi
  fi

  if [[ -z "$nc_refusal" ]]; then
    if [[ -f "$post_logs/no-comments.status" ]]; then
      raw=$(cat "$post_logs/no-comments.status" 2>/dev/null || true)
      if [[ "$raw" =~ ^[0-9]+$ ]]; then
        commented="$raw"
        nc_state="$raw"
      elif [[ "$early_abort" == 1 ]]; then
        nc_state='interrupted / unfinished'
      else
        nc_state='status unavailable'
      fi
    elif [[ -f "$post_logs/no-comments.started" ]]; then
      if [[ "$early_abort" == 1 ]]; then
        nc_state='interrupted / unfinished'
      else
        nc_state='status unavailable'
      fi
    fi
    if [[ -f "$post_logs/no-comments.dur" ]]; then
      dur_raw=$(cat "$post_logs/no-comments.dur" 2>/dev/null || true)
      if [[ "$dur_raw" =~ ^[0-9]+$ ]]; then
        nc_exec_dur="$dur_raw"
      fi
    fi
  fi
}

# Invoked both on normal completion and from the EXIT/INT/TERM cleanup trap on early abort.
# shellcheck disable=SC2317,SC2329
emit_gate_summary() {
  local early_abort="${1:-0}"
  local gate_total_dur="$SECONDS"
  local verify_dur=$((stage1_dur + stage2_dur))
  local effective_post_wall="$post_wall_dur"
  local workflow_elapsed_dur='' now_epoch
  local verify_over=0 regula_over=0 nc_over=0 gate_over=0 job_over=0 prov_over=0
  local s_prov s_s1 s_s2 s_nca s_reg s_int s_frm s_nc gate_state nc_label

  summary_written=1
  if [[ "$early_abort" == 1 ]]; then
    sync_bg_phase_state 1
    if [[ -n "$post_start" ]]; then
      effective_post_wall=$((SECONDS - post_start))
    fi
  fi
  if [[ "${ACORN_JOB_START_EPOCH:-}" =~ ^[0-9]+$ ]]; then
    now_epoch=$(date +%s)
    if (( now_epoch >= ACORN_JOB_START_EPOCH )); then
      workflow_elapsed_dur=$((now_epoch - ACORN_JOB_START_EPOCH))
    fi
  fi

  if [[ "$stage1_state" =~ ^[0-9]+$ ]] && (( verify_dur > verify_budget_s )); then
    verify_over=1
    emit_budget_warning 'Verification stages 1+2' "$verify_dur" "$verify_budget_s"
  fi
  if [[ "$regula_state" =~ ^[0-9]+$ ]] && (( regula_dur > regula_budget_s )); then
    regula_over=1
    emit_budget_warning 'Regula audit' "$regula_dur" "$regula_budget_s"
  fi
  if [[ "$nc_state" =~ ^[0-9]+$ && "$nc_exec_dur" =~ ^[0-9]+$ ]] && (( nc_exec_dur > nc_budget_s )); then
    nc_over=1
    emit_budget_warning 'no-comments check' "$nc_exec_dur" "$nc_budget_s"
  fi
  if (( gate_total_dur > gate_budget_s )); then
    gate_over=1
    emit_budget_warning 'Merge gate (scripts/gate.sh)' "$gate_total_dur" "$gate_budget_s"
  fi
  if [[ -n "$workflow_elapsed_dur" ]] && (( workflow_elapsed_dur > job_budget_s )); then
    job_over=1
    emit_budget_warning 'Workflow elapsed (commit check through gate)' "$workflow_elapsed_dur" "$job_budget_s"
  fi

  s_prov=$(summary_phase_state "$provision_state" "$early_abort")
  s_s1=$(summary_phase_state "$stage1_state" "$early_abort")
  s_s2=$(summary_phase_state "$stage2_state" "$early_abort")
  s_nca=$(summary_phase_state "$nc_admit_state" "$early_abort")
  s_reg=$(summary_phase_state "$regula_state" "$early_abort")
  s_int=$(summary_phase_state "$intent_state" "$early_abort")
  s_frm=$(summary_phase_state "$frame_state" "$early_abort")
  s_nc=$(summary_phase_state "$nc_state" "$early_abort")

  if [[ "$early_abort" == 1 ]]; then
    gate_state='interrupted / failed early'
  elif [[ "$verified" == 0 && "$audited" == 0 && "$intended" == 0 && "$framed" == 0 && "$commented" == 0 && "$post_checks_status" == 0 ]]; then
    gate_state='0'
  elif [[ "$verified" == 0 && "$audited" == 0 && "$intended" == 0 && "$framed" == 0 && "$commented" == 0 && "$post_checks_status" != 0 ]]; then
    gate_state="failed (background supervisor exit $post_checks_status)"
  else
    gate_state='1'
  fi

  if [[ -n "$nc_jobs" && "$s_nc" =~ ^[0-9]+$ ]]; then
    nc_label="no-comments check (--jobs $nc_jobs)"
  else
    nc_label='no-comments check'
  fi

  if [[ -n "${GITHUB_STEP_SUMMARY:-}" && ! -L "$GITHUB_STEP_SUMMARY" && ( ! -e "$GITHUB_STEP_SUMMARY" || -f "$GITHUB_STEP_SUMMARY" ) ]]; then
    local write_rc=0
    {
      printf '## Verify / gate phase timings\n\n'
      printf '| Phase | Duration | Target budget | Hard limit | Status |\n'
      printf '|---|---:|---:|---:|---|\n'
      if [[ "${ACORN_PROVISION_SECONDS:-}" =~ ^[0-9]+$ ]]; then
        if (( ACORN_PROVISION_SECONDS > provision_budget_s )); then
          prov_over=1
        fi
        printf '| Provision pinned dependencies | %s | <= %s | 12m | %s |\n' \
          "$(format_duration "$ACORN_PROVISION_SECONDS")" \
          "$(format_duration "$provision_budget_s")" \
          "$(status_label 0 "$prov_over")"
      fi
      printf '| Gate dependency re-check | %s | - | - | %s |\n' \
        "$(summary_phase_dur "$s_prov" "$provision_dur")" \
        "$(status_label "$s_prov" 0)"
      printf '| Verification stage 1 (build-executing) | %s | - | %s | %s |\n' \
        "$(summary_phase_dur "$s_s1" "$stage1_dur")" \
        "$(format_duration 360)" \
        "$(status_label "$s_s1" 0)"
      printf '| Verification stage 2 (verify.sh) | %s | <= %s (stages 1+2) | %s | %s |\n' \
        "$(summary_phase_dur "$s_s2" "$stage2_dur")" \
        "$(format_duration "$verify_budget_s")" \
        "$(format_duration 360)" \
        "$(status_label "$s_s2" "$verify_over")"
      printf '| no-comments admission (admit-no-comments) | %s | - | %s | %s |\n' \
        "$(summary_phase_dur "$s_nca" "$nc_admit_dur")" \
        "$(format_duration "$nc_admit_timeout_s")" \
        "$(status_label "$s_nca" 0)"
      printf '| Regula audit (scripts/regula.sh) | %s | <= %s | %s | %s |\n' \
        "$(summary_phase_dur "$s_reg" "$regula_dur")" \
        "$(format_duration "$regula_budget_s")" \
        "$(format_duration "$regula_timeout_s")" \
        "$(status_label "$s_reg" "$regula_over")"
      printf '| lean-intent checks (intent-check) | %s | - | %s | %s |\n' \
        "$(summary_phase_dur "$s_int" "$intent_dur")" \
        "$(format_duration "$intent_timeout_s")" \
        "$(status_label "$s_int" 0)"
      printf '| Frame check (frame-check) | %s | - | %s | %s |\n' \
        "$(summary_phase_dur "$s_frm" "$frame_dur")" \
        "$(format_duration "$frame_timeout_s")" \
        "$(status_label "$s_frm" 0)"
      printf '| %s | %s | <= %s | %s | %s |\n' \
        "$nc_label" \
        "$(summary_phase_dur "$s_nc" "$nc_exec_dur")" \
        "$(format_duration "$nc_budget_s")" \
        "$(format_duration "$nc_timeout_s")" \
        "$(status_label "$s_nc" "$nc_over")"
      printf '| Post-verification wall (%s) | %s | - | - | - |\n' \
        "$post_mode" \
        "$(format_duration "$effective_post_wall")"
      printf '| **Merge gate total (scripts/gate.sh)** | **%s** | **<= %s** | **13m** | **%s** |\n' \
        "$(format_duration "$gate_total_dur")" \
        "$(format_duration "$gate_budget_s")" \
        "$(status_label "$gate_state" "$gate_over")"
      if [[ -n "$workflow_elapsed_dur" ]]; then
        printf '| **Workflow elapsed (commit check through gate)** | **%s** | **<= %s** | **20m (job)** | **%s** |\n' \
          "$(format_duration "$workflow_elapsed_dur")" \
          "$(format_duration "$job_budget_s")" \
          "$(status_label "$gate_state" "$job_over")"
      fi
      printf '\n'
    } >> "$GITHUB_STEP_SUMMARY" || write_rc=$?
    if [[ "$write_rc" != 0 ]]; then
      echo "gate: failed to write phase summary to $GITHUB_STEP_SUMMARY" >&2
      if [[ "$early_abort" == 0 ]]; then
        return 1
      fi
    fi
  fi

  printf 'gate: phase timings (s): provision=%d stage1=%d stage2=%d nc-admit=%d regula=%d intent=%s frame=%s no-comments=%s post-wall=%d (%s, nc-jobs=%s) total=%d\n' \
    "$provision_dur" "$stage1_dur" "$stage2_dur" "$nc_admit_dur" "$regula_dur" \
    "$(summary_phase_secs "$s_int" "$intent_dur")" \
    "$(summary_phase_secs "$s_frm" "$frame_dur")" \
    "$(summary_phase_secs "$s_nc" "$nc_exec_dur")" \
    "$effective_post_wall" "$post_mode" "${nc_jobs:-none}" "$gate_total_dur"
}

# Invoked by the EXIT/INT/TERM traps; older ShellCheck does not trace trap callbacks.
# shellcheck disable=SC2317,SC2329
cleanup_post_checks() {
  local fg_pid="$fg_child_pid"
  local pid="$post_checks_pid"
  local bg_child=''
  fg_child_pid=''
  post_checks_pid=''
  if [[ -n "$fg_pid" ]]; then
    kill -KILL -- -"$fg_pid" 2>/dev/null || true
    kill -KILL "$fg_pid" 2>/dev/null || true
    wait "$fg_pid" 2>/dev/null || true
  fi
  if [[ -n "$pid" ]]; then
    kill -TERM -- -"$pid" 2>/dev/null || true
    for _ in 1 2 3 4 5 6 7 8 9 10; do
      if ! kill -0 "$pid" 2>/dev/null; then
        break
      fi
      sleep 0.1
    done
    kill -KILL -- -"$pid" 2>/dev/null || true
    kill -KILL "$pid" 2>/dev/null || true
    wait "$pid" 2>/dev/null || true
  fi
  if [[ -n "$post_logs" && -f "$post_logs/bg-child.pid" ]]; then
    bg_child=$(cat "$post_logs/bg-child.pid" 2>/dev/null || true)
    if [[ "$bg_child" =~ ^[0-9]+$ ]]; then
      kill -KILL -- -"$bg_child" 2>/dev/null || true
      kill -KILL "$bg_child" 2>/dev/null || true
    fi
  fi
  if [[ "$provision_only" == 0 && "$summary_written" == 0 ]]; then
    emit_gate_summary 1 || true
  fi
  if [[ -n "$gate_scratch" ]]; then
    rm -rf "$gate_scratch"
    gate_scratch=''
    post_logs=''
  fi
}
trap cleanup_post_checks EXIT
trap 'cleanup_post_checks; exit 130' INT
trap 'cleanup_post_checks; exit 143' TERM

gate_scratch=$(mktemp -d)
post_logs="$gate_scratch/logs"
mkdir -p "$post_logs" "$gate_scratch/prov-tmp" "$gate_scratch/stage1-tmp" \
  "$gate_scratch/stage2-tmp" "$gate_scratch/admit-tmp" \
  "$gate_scratch/regula-tmp" "$gate_scratch/intent-tmp" \
  "$gate_scratch/frame-tmp" "$gate_scratch/nc-tmp"

# Run a foreground bash function in its own process group with an interruptible wait so
# INT/TERM traps reach and reap the active child group; always reap any surviving
# group members before clearing fg_child_pid.
run_fg_group() {
  local rc=0
  set -m
  (
    set +m
    "$@"
  ) &
  fg_child_pid=$!
  set +m
  wait "$fg_child_pid" || rc=$?
  kill -KILL -- -"$fg_child_pid" 2>/dev/null || true
  fg_child_pid=''
  return "$rc"
}

# Run a foreground external command via exec in its own process group with isolated
# TMPDIR so tools that exec GNU timeout (notably scripts/verify.sh) keep PID == PGID ==
# fg_child_pid and cancellation signals reach and reap the timer and its descendants.
run_fg_exec() {
  local custom_tmpdir="$1"
  shift
  local rc=0
  set -m
  (
    set +m
    exec env TMPDIR="$custom_tmpdir" "$@"
  ) &
  fg_child_pid=$!
  set +m
  wait "$fg_child_pid" || rc=$?
  kill -KILL -- -"$fg_child_pid" 2>/dev/null || true
  fg_child_pid=''
  return "$rc"
}

run_fg_dep_bounded() {
  local limit_s="$1" custom_tmpdir="$2"
  shift 2
  local rc=0
  set -m
  (
    set +m
    dependency_git
    if [[ -n "$custom_tmpdir" ]]; then
      exec env TMPDIR="$custom_tmpdir" "$timeout_command" --signal=KILL "${limit_s}s" "$@"
    else
      exec "$timeout_command" --signal=KILL "${limit_s}s" "$@"
    fi
  ) &
  fg_child_pid=$!
  set +m
  wait "$fg_child_pid" || rc=$?
  kill -KILL -- -"$fg_child_pid" 2>/dev/null || true
  fg_child_pid=''
  return "$rc"
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

provision_lean_workspace() {
  # Parallel cache extraction can exhaust macOS's inherited 256-descriptor limit.
  # Give provisioning a process-local floor before Lake can fetch dependencies;
  # preserve higher limits and the hard limit. This is a budget, not a peak bound.
  export TMPDIR="$gate_scratch/prov-tmp"
  local descriptor_limit current=0
  descriptor_limit=$(ulimit -Sn)
  if [[ "$descriptor_limit" != unlimited ]] && (( descriptor_limit < 4096 )); then
    ulimit -Sn 4096
  fi
  ./scripts/tracked-files.sh sync-config --clean --admit-manifest .
  dependency_git
  cd lean
  # Lake decides whether Mathlib and Regula's lint driver need provisioning: with
  # --no-build it exits 3 unless every artifact and trace of these targets is current.
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
}

provision_site_workspace() {
  export TMPDIR="$gate_scratch/prov-tmp"
  dependency_git
  cd site
  # Verso's modules and the shared library its documents load.
  lake -f lakefile.toml build verso/VersoManual verso/VersoManual:shared
}

provision_start="$SECONDS"
step 'provisioning the pinned dependencies'
run_fg_group provision_lean_workspace
run_fg_exec "$gate_scratch/prov-tmp" ./scripts/lean.sh provision-status
run_fg_exec "$gate_scratch/prov-tmp" ./scripts/tracked-files.sh admit-site --clean .
run_fg_group provision_site_workspace
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
  nc_dl_dir="$gate_scratch/nc-download"
  mkdir -p "$nc_dl_dir"
  run_fg_exec "$gate_scratch/prov-tmp" curl --fail --silent --show-error --location --proto '=https' --tlsv1.2 \
    --connect-timeout 10 --max-time 180 --retry 2 --retry-delay 2 --retry-max-time 300 \
    --output "$nc_dl_dir/no-comments" \
    "https://github.com/rbeauchamp/lean-no-comments/releases/download/${nc_version}/no-comments-${nc_target}"
  if ! verify_sha256 "$nc_sha256" "$nc_dl_dir/no-comments"; then
    echo "gate: downloaded no-comments-${nc_target} failed SHA-256 verification" >&2
    exit 1
  fi
  ensure_nc_cache_dirs
  if [[ -L "$nc_bin" || ( -e "$nc_bin" && ! -f "$nc_bin" ) ]]; then
    echo "gate: refusing unexpected non-regular cache entry: $nc_bin" >&2
    exit 1
  fi
  chmod 755 "$nc_dl_dir/no-comments"
  mv -f "$nc_dl_dir/no-comments" "$nc_bin"
  rmdir "$nc_dl_dir"
fi
provision_dur=$((SECONDS - provision_start))
provision_state='0'
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
# bounded tracked-file admission (60-second deadline: .no-comments.json, comment-ratchet.json,
# lean/no-comments.pin); when verification failed, no-comments is refused without elaborating
# un-admitted sources. The Regula audit and the intent and frame checks run even when an earlier
# step fails. When ordinary verification passed, compiled build outputs, Lake configuration
# caches, lean/.lake/acorn-path-packages.json and lean/.lake/acorn-tracked-modules.z are already
# current (scripts/tracked-files.sh sync-config writes its comparison file in TMPDIR and creates
# no files under lean/.lake/ on a stamp hit, scripts/tracked-files.sh refuses Lake reconfiguring
# flags in .no-comments.json, and gate.sh isolates every bounded phase's TMPDIR under a
# parent-owned scratch directory removed on exit or cancellation), so after admitting
# no-comments upfront, the Regula audit runs in the foreground while lean-intent, frame-check
# and (when admitted) no-comments run one after another in a background subshell, capping
# no-comments workers to leave one core for Regula's single-threaded kernel replay and limit
# concurrent worker parallelism; when verification failed, Regula, lean-intent and frame-check
# run one after another.

verified=0
stage1_state='running'
stage1_start="$SECONDS"
step 'verification, stage one'
stage1_rc=0
run_fg_exec "$gate_scratch/stage1-tmp" ./scripts/verify.sh build-executing || stage1_rc=$?
stage1_dur=$((SECONDS - stage1_start))
stage1_state="$stage1_rc"
if [[ "$stage1_rc" == 0 ]]; then
  stage2_state='running'
  stage2_start="$SECONDS"
  step 'verification, stage two'
  stage2_rc=0
  run_fg_exec "$gate_scratch/stage2-tmp" ./scripts/verify.sh || stage2_rc=$?
  stage2_dur=$((SECONDS - stage2_start))
  stage2_state="$stage2_rc"
  verified="$stage2_rc"
else
  stage2_state='skipped'
  verified="$stage1_rc"
fi

audited=0
intended=0
framed=0
commented=0
nc_jobs=$(detect_nc_jobs)
nc_refusal=''
nc_admitted=0
nc_admit_rc=0
post_mode='serial'
post_start="$SECONDS"

if [[ "$verified" == 0 ]]; then
  post_mode='overlapped'
  if ! check_nc_cache_dirs require-present; then
    nc_refusal='integrity'
    nc_admit_state='skipped (integrity failed)'
    nc_state='refused (integrity)'
    commented=1
  elif ! verify_sha256 "$nc_sha256" "$nc_bin"; then
    echo "gate: offline SHA-256 verification failed for $nc_bin" >&2
    nc_refusal='integrity'
    nc_admit_state='skipped (integrity failed)'
    nc_state='refused (integrity)'
    commented=1
  else
    nc_admit_state='running'
    nc_admit_start="$SECONDS"
    nc_admit_rc=0
    run_fg_dep_bounded "$nc_admit_timeout_s" "$gate_scratch/admit-tmp" ./scripts/tracked-files.sh admit-no-comments --clean . || nc_admit_rc=$?
    nc_admit_dur=$((SECONDS - nc_admit_start))
    nc_admit_state="$nc_admit_rc"
    if [[ "$nc_admit_rc" != 0 ]]; then
      nc_refusal='admit'
      nc_state="refused (admission, exit $nc_admit_rc)"
      commented=1
    else
      nc_admitted=1
    fi
  fi

  nc_args=(check --jobs "$nc_jobs")
  if [[ -n "${ACORN_BASE_REF:-}" ]]; then
    nc_args+=(--base-ref "$ACORN_BASE_REF")
  fi

  if [[ "$nc_admitted" == 1 ]]; then
    step "verification exited $verified; Regula audit beside lean-intent, frame and no-comments checks"
  else
    step "verification exited $verified; Regula audit beside lean-intent and frame checks"
  fi
  regula_state='running'
  bg_supervisor_launched=1

  set -m
  (
    set +m
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
      rm -f "$post_logs/bg-child.pid"
    }
    trap cleanup_bg_child EXIT
    trap 'cleanup_bg_child; exit 130' INT
    trap 'cleanup_bg_child; exit 143' TERM

    run_bg_bounded() {
      local limit_s="$1" custom_tmpdir="$2" prefix="$3"
      shift 3
      local t0="$SECONDS" rc=0
      : > "${prefix}.started"
      set -m
      (
        set +m
        dependency_git
        exec env TMPDIR="$custom_tmpdir" "$timeout_command" --signal=KILL "${limit_s}s" "$@"
      ) > "${prefix}.log" 2>&1 < /dev/null &
      bg_child_pid=$!
      set +m
      printf '%d\n' "$bg_child_pid" > "$post_logs/bg-child.pid"
      wait "$bg_child_pid" || rc=$?
      kill -KILL -- -"$bg_child_pid" 2>/dev/null || true
      bg_child_pid=''
      rm -f "$post_logs/bg-child.pid"
      printf '%d\n' $((SECONDS - t0)) > "${prefix}.dur.tmp"
      mv -f "${prefix}.dur.tmp" "${prefix}.dur"
      printf '%d\n' "$rc" > "${prefix}.status.tmp"
      mv -f "${prefix}.status.tmp" "${prefix}.status"
    }

    run_bg_bounded "$intent_timeout_s" "$gate_scratch/intent-tmp" "$post_logs/intent" \
      ./scripts/lean.sh exe intent-check
    run_bg_bounded "$frame_timeout_s" "$gate_scratch/frame-tmp" "$post_logs/frame" \
      ./scripts/lean.sh exe frame-check
    if [[ "$nc_admitted" == 1 ]]; then
      run_bg_bounded "$nc_timeout_s" "$gate_scratch/nc-tmp" "$post_logs/no-comments" \
        "$nc_bin" "${nc_args[@]}"
    fi
  ) < /dev/null &
  post_checks_pid=$!
  set +m

  regula_start="$SECONDS"
  audited=0
  run_fg_dep_bounded "$regula_timeout_s" "$gate_scratch/regula-tmp" ./scripts/regula.sh || audited=$?
  regula_dur=$((SECONDS - regula_start))
  regula_state="$audited"

  post_checks_status=0
  wait "$post_checks_pid" || post_checks_status=$?
  post_checks_pid=''

  intended=1
  framed=1
  commented=1
  sync_bg_phase_state 0

  step "Regula audit exited $audited; lean-intent checks"
  if [[ -f "$post_logs/intent.log" ]]; then
    cat "$post_logs/intent.log"
  fi
  if [[ "$intent_state" =~ ^[0-9]+$ ]]; then
    step "lean-intent checks exited $intended; frame check"
  elif [[ "$intent_state" == 'not reached' ]]; then
    step "lean-intent checks not reached (background supervisor exited $post_checks_status); frame check"
  else
    step "lean-intent checks status unavailable (background supervisor exited $post_checks_status); frame check"
  fi

  if [[ -f "$post_logs/frame.log" ]]; then
    cat "$post_logs/frame.log"
  fi
  if [[ "$frame_state" =~ ^[0-9]+$ ]]; then
    step "frame check exited $framed; no-comments check"
  elif [[ "$frame_state" == 'not reached' ]]; then
    step "frame check not reached (background supervisor exited $post_checks_status); no-comments check"
  else
    step "frame check status unavailable (background supervisor exited $post_checks_status); no-comments check"
  fi

  if [[ "$nc_refusal" == 'integrity' ]]; then
    commented=1
    step 'no-comments check refused (integrity check failed)'
  elif [[ "$nc_refusal" == 'admit' ]]; then
    commented=1
    step "no-comments check refused (admission check failed, exit $nc_admit_rc)"
  else
    if [[ -f "$post_logs/no-comments.log" ]]; then
      cat "$post_logs/no-comments.log"
    fi
    if [[ "$nc_state" =~ ^[0-9]+$ ]]; then
      step "no-comments check exited $commented"
    elif [[ "$nc_state" == 'not reached' ]]; then
      step "no-comments check not reached (background supervisor exited $post_checks_status)"
    else
      step "no-comments check status unavailable (background supervisor exited $post_checks_status)"
    fi
  fi
else
  nc_admit_state='skipped'
  step "verification exited $verified; Regula audit"
  regula_state='running'
  regula_start="$SECONDS"
  audited=0
  run_fg_dep_bounded "$regula_timeout_s" "$gate_scratch/regula-tmp" ./scripts/regula.sh || audited=$?
  regula_dur=$((SECONDS - regula_start))
  regula_state="$audited"

  step "Regula audit exited $audited; lean-intent checks"
  intent_state='running'
  intent_start="$SECONDS"
  intended=0
  run_fg_dep_bounded "$intent_timeout_s" "$gate_scratch/intent-tmp" ./scripts/lean.sh exe intent-check || intended=$?
  intent_dur=$((SECONDS - intent_start))
  intent_state="$intended"

  step "lean-intent checks exited $intended; frame check"
  frame_state='running'
  frame_start="$SECONDS"
  framed=0
  run_fg_dep_bounded "$frame_timeout_s" "$gate_scratch/frame-tmp" ./scripts/lean.sh exe frame-check || framed=$?
  frame_dur=$((SECONDS - frame_start))
  frame_state="$framed"

  step "frame check exited $framed; no-comments check"
  echo "gate: refusing no-comments check because verification exited $verified" >&2
  nc_refusal='verification'
  nc_state='refused (verification)'
  commented=1
  step 'no-comments check refused (verification failed)'
fi
post_wall_dur=$((SECONDS - post_start))

emit_gate_summary 0
if [[ "$post_checks_status" != 0 ]]; then
  echo "gate: background post-check supervisor exited $post_checks_status" >&2
fi
[[ "$verified" == 0 && "$audited" == 0 && "$intended" == 0 && "$framed" == 0 && "$commented" == 0 && "$post_checks_status" == 0 ]] || exit 1
step 'every merge check passed'
