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
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$HOME/.local/bin:/opt/homebrew/bin:/usr/local/bin:$PATH"

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
sc_pin='scripts/shellcheck.pin'
admit_tracked_helper . 1 || {
  echo "gate: scripts/tracked-files.sh failed pre-execution Git admission" >&2
  exit 1
}
./scripts/tracked-files.sh admit-file --clean . \
  scripts/tracked-files.sh scripts/gate.sh scripts/lean.sh scripts/verify.sh scripts/regula.sh "$nc_pin" "$sc_pin"
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
fg_reap_open=0
sup_ctrl_open=0
summary_written=0
summary_table_written=0
warnings_emitted=0
timings_logged=0
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

provision_dur=''
provision_start=''
provision_state='not reached'
stage1_dur=''
stage1_start=''
stage1_state='not reached'
stage2_dur=''
stage2_start=''
stage2_state='not reached'
nc_admit_dur=''
nc_admit_start=''
nc_admit_state='not reached'
regula_dur=''
regula_start=''
regula_state='not reached'
intent_dur=''
intent_start=''
intent_state='not reached'
frame_dur=''
frame_start=''
frame_state='not reached'
nc_exec_dur=''
nc_start=''
nc_state='not reached'
post_wall_dur=''
post_wall_state='not reached'
post_start=''
post_mode='serial'
post_checks_status=0
nc_jobs=''
nc_refusal=''
gate_passed=0
gate_verdict_state='1'
verified=1
audited=1
intended=1
framed=1
commented=1

format_duration() {
  local _out="$1" _secs="$2"
  printf -v "$_out" '%dm %02ds (%d s)' $((_secs / 60)) $((_secs % 60)) "$_secs"
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

append_budget_warning() {
  local _out="$1" _phase="$2" _actual="$3" _budget="$4" _fa='' _fb='' _line=''
  format_duration _fa "$_actual"
  format_duration _fb "$_budget"
  if [[ "${GITHUB_ACTIONS:-}" == 'true' ]]; then
    printf -v _line '::warning title=Verify / gate budget::%s took %s (target <= %s).\n' \
      "$_phase" "$_fa" "$_fb"
  else
    printf -v _line 'gate: budget warning: %s took %s (target <= %s)\n' \
      "$_phase" "$_fa" "$_fb"
  fi
  printf -v "$_out" '%s%s' "${!_out}" "$_line"
}

status_label() {
  local _out="$1" _state="$2" _over="$3"
  if [[ "$_state" == '0' ]]; then
    if [[ "$_over" == '1' ]]; then
      printf -v "$_out" '%s' 'ok (over budget)'
    else
      printf -v "$_out" '%s' 'ok'
    fi
  elif [[ "$_state" == '137' ]]; then
    printf -v "$_out" '%s' 'killed (SIGKILL / timeout, exit 137)'
  elif [[ "$_state" =~ ^[0-9]+$ ]]; then
    if [[ "$_over" == '1' ]]; then
      printf -v "$_out" 'failed (exit %s, over budget)' "$_state"
    else
      printf -v "$_out" 'failed (exit %s)' "$_state"
    fi
  elif [[ "$_over" == '1' ]]; then
    printf -v "$_out" '%s (over budget)' "$_state"
  else
    printf -v "$_out" '%s' "$_state"
  fi
}

summary_phase_state() {
  local _out="$1" _state="$2" _early_abort="$3"
  if [[ "$_early_abort" == 1 && "$_state" == 'running' ]]; then
    printf -v "$_out" '%s' 'interrupted / unfinished'
  else
    printf -v "$_out" '%s' "$_state"
  fi
}

phase_elapsed_secs() {
  local _out="$1" _state="$2" _dur="$3" _start="$4" _now="$5"
  if [[ "$_dur" =~ ^[0-9]+$ ]]; then
    printf -v "$_out" '%s' "$_dur"
  elif [[ "$_state" == 'interrupted / unfinished' && "$_start" =~ ^[0-9]+$ ]] && (( _now >= _start )); then
    printf -v "$_out" '%s' $((_now - _start))
  else
    printf -v "$_out" '%s' ''
  fi
}

summary_phase_dur() {
  local _out="$1" _state="$2" _dur="$3" _start="$4" _now="$5" _elapsed='' _fd=''
  case "$_state" in
    'not reached'|'skipped'|'skipped ('*|'refused ('*)
      printf -v "$_out" '%s' '-' ;;
    'interrupted / unfinished')
      phase_elapsed_secs _elapsed "$_state" "$_dur" "$_start" "$_now"
      if [[ -n "$_elapsed" ]]; then
        format_duration _fd "$_elapsed"
        printf -v "$_out" '%s (interrupted)' "$_fd"
      else
        printf -v "$_out" '%s' 'unavailable (interrupted)'
      fi ;;
    *)
      if [[ "$_dur" =~ ^[0-9]+$ ]]; then
        format_duration "$_out" "$_dur"
      else
        printf -v "$_out" '%s' 'unavailable'
      fi ;;
  esac
}

summary_phase_secs() {
  local _out="$1" _state="$2" _dur="$3" _start="$4" _now="$5" _elapsed=''
  case "$_state" in
    'not reached'|'skipped'|'skipped ('*|'refused ('*)
      printf -v "$_out" '%s' '-' ;;
    'interrupted / unfinished')
      phase_elapsed_secs _elapsed "$_state" "$_dur" "$_start" "$_now"
      if [[ -n "$_elapsed" ]]; then
        printf -v "$_out" 'interrupted:%s' "$_elapsed"
      else
        printf -v "$_out" '%s' 'unavailable'
      fi ;;
    *)
      if [[ "$_dur" =~ ^[0-9]+$ ]]; then
        printf -v "$_out" '%s' "$_dur"
      else
        printf -v "$_out" '%s' 'unavailable'
      fi ;;
  esac
}

compute_gate_verdict() {
  local early_abort="${1:-0}"
  gate_passed=0
  if [[ "$early_abort" == 1 ]]; then
    gate_verdict_state='interrupted / failed early'
  elif [[ "$verified" == 0 && "$audited" == 0 && "$intended" == 0 && "$framed" == 0 && "$commented" == 0 ]]; then
    if [[ "$post_checks_status" == 0 ]]; then
      gate_passed=1
      gate_verdict_state='0'
    else
      gate_verdict_state="failed (background supervisor exit $post_checks_status)"
    fi
  else
    gate_verdict_state='1'
  fi
}

# Inspect actual start/completion marker files written by the background subshell so
# completed checks stay observed even on early cancellation or later supervisor failure,
# and unstarted checks report `not reached` rather than `interrupted`.
# shellcheck disable=SC2317,SC2329
sync_bg_phase_state() {
  local early_abort="$1"
  local raw='' dur_raw='' start_raw=''
  [[ "$bg_supervisor_launched" == 1 && -n "$post_logs" ]] || return 0

  if [[ -f "$post_logs/intent.started" ]]; then
    start_raw=$(cat "$post_logs/intent.started" 2>/dev/null || true)
    if [[ "$start_raw" =~ ^[0-9]+$ ]]; then
      intent_start="$start_raw"
    fi
  fi
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

  if [[ -f "$post_logs/frame.started" ]]; then
    start_raw=$(cat "$post_logs/frame.started" 2>/dev/null || true)
    if [[ "$start_raw" =~ ^[0-9]+$ ]]; then
      frame_start="$start_raw"
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
    if [[ -f "$post_logs/no-comments.started" ]]; then
      start_raw=$(cat "$post_logs/no-comments.started" 2>/dev/null || true)
      if [[ "$start_raw" =~ ^[0-9]+$ ]]; then
        nc_start="$start_raw"
      fi
    fi
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
  local now="$SECONDS"
  local gate_total_dur="$now"
  local workflow_elapsed_dur='' now_epoch=''
  local s1_over=0 s2_over=0 regula_over=0 nc_over=0 gate_over=0 job_over=0 prov_over=0
  local e_s1='' e_s2='' verify_elapsed='' e_reg='' e_nc=''
  local s_prov='' s_s1='' s_s2='' s_nca='' s_reg='' s_int='' s_frm='' s_nc='' s_post='' nc_label=''
  local t_prov='' t_s1='' t_s2='' t_nca='' t_reg='' t_int='' t_frm='' t_nc='' t_post=''
  local f_dur='' f_bud='' f_lim='' f_st=''
  local summary_body='' warnings_body='' timings_line='' row='' summary_suitable=0 summary_fail=0

  if [[ "$early_abort" == 1 ]]; then
    sync_bg_phase_state 1
  fi
  if [[ "${ACORN_JOB_START_EPOCH:-}" =~ ^[0-9]+$ ]]; then
    now_epoch=$(date +%s 2>/dev/null || true)
    if [[ "$now_epoch" =~ ^[0-9]+$ ]] && (( now_epoch >= ACORN_JOB_START_EPOCH )); then
      workflow_elapsed_dur=$((now_epoch - ACORN_JOB_START_EPOCH))
    fi
  fi

  summary_phase_state s_prov "$provision_state" "$early_abort"
  summary_phase_state s_s1 "$stage1_state" "$early_abort"
  summary_phase_state s_s2 "$stage2_state" "$early_abort"
  summary_phase_state s_nca "$nc_admit_state" "$early_abort"
  summary_phase_state s_reg "$regula_state" "$early_abort"
  summary_phase_state s_int "$intent_state" "$early_abort"
  summary_phase_state s_frm "$frame_state" "$early_abort"
  summary_phase_state s_nc "$nc_state" "$early_abort"
  summary_phase_state s_post "$post_wall_state" "$early_abort"

  phase_elapsed_secs e_s1 "$s_s1" "$stage1_dur" "$stage1_start" "$now"
  phase_elapsed_secs e_s2 "$s_s2" "$stage2_dur" "$stage2_start" "$now"
  phase_elapsed_secs e_reg "$s_reg" "$regula_dur" "$regula_start" "$now"
  phase_elapsed_secs e_nc "$s_nc" "$nc_exec_dur" "$nc_start" "$now"

  if [[ -n "$e_s1" ]]; then
    verify_elapsed=$((e_s1 + ${e_s2:-0}))
    if (( verify_elapsed > verify_budget_s )); then
      if [[ "$s_s2" == 'not reached' || "$s_s2" == 'skipped' ]]; then
        s1_over=1
      else
        s2_over=1
      fi
      append_budget_warning warnings_body 'Verification stages 1+2' "$verify_elapsed" "$verify_budget_s"
    fi
  fi
  if [[ -n "$e_reg" ]] && (( e_reg > regula_budget_s )); then
    regula_over=1
    append_budget_warning warnings_body 'Regula audit' "$e_reg" "$regula_budget_s"
  fi
  if [[ -n "$e_nc" ]] && (( e_nc > nc_budget_s )); then
    nc_over=1
    append_budget_warning warnings_body 'no-comments check' "$e_nc" "$nc_budget_s"
  fi
  if (( gate_total_dur > gate_budget_s )); then
    gate_over=1
    append_budget_warning warnings_body 'Merge gate (scripts/gate.sh)' "$gate_total_dur" "$gate_budget_s"
  fi
  if [[ -n "$workflow_elapsed_dur" ]] && (( workflow_elapsed_dur > job_budget_s )); then
    job_over=1
    append_budget_warning warnings_body 'Workflow elapsed (commit check through gate)' "$workflow_elapsed_dur" "$job_budget_s"
  fi

  compute_gate_verdict "$early_abort"

  if [[ -n "$nc_jobs" && ( "$s_nc" =~ ^[0-9]+$ || "$s_nc" == 'interrupted / unfinished' ) ]]; then
    nc_label="no-comments check (--jobs $nc_jobs)"
  else
    nc_label='no-comments check'
  fi

  if [[ "$summary_table_written" == 0 && -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    if [[ ! -L "$GITHUB_STEP_SUMMARY" && ( ! -e "$GITHUB_STEP_SUMMARY" || -f "$GITHUB_STEP_SUMMARY" ) ]]; then
      summary_suitable=1
      summary_body=$'## Verify / gate phase timings\n\n| Phase | Duration | Target budget | Hard limit | Status |\n|---|---:|---:|---:|---|\n'
      if [[ "${ACORN_PROVISION_SECONDS:-}" =~ ^[0-9]+$ ]]; then
        if (( ACORN_PROVISION_SECONDS > provision_budget_s )); then
          prov_over=1
        fi
        format_duration f_dur "$ACORN_PROVISION_SECONDS"
        format_duration f_bud "$provision_budget_s"
        status_label f_st 0 "$prov_over"
        printf -v row '| Provision pinned dependencies | %s | <= %s | 12m | %s |\n' "$f_dur" "$f_bud" "$f_st"
        summary_body+="$row"
      fi
      summary_phase_dur f_dur "$s_prov" "$provision_dur" "$provision_start" "$now"
      status_label f_st "$s_prov" 0
      printf -v row '| Gate dependency re-check | %s | - | - | %s |\n' "$f_dur" "$f_st"
      summary_body+="$row"
      summary_phase_dur f_dur "$s_s1" "$stage1_dur" "$stage1_start" "$now"
      format_duration f_lim 360
      status_label f_st "$s_s1" "$s1_over"
      printf -v row '| Verification stage 1 (build-executing) | %s | - | %s | %s |\n' "$f_dur" "$f_lim" "$f_st"
      summary_body+="$row"
      summary_phase_dur f_dur "$s_s2" "$stage2_dur" "$stage2_start" "$now"
      format_duration f_bud "$verify_budget_s"
      status_label f_st "$s_s2" "$s2_over"
      printf -v row '| Verification stage 2 (verify.sh) | %s | <= %s (stages 1+2) | %s | %s |\n' "$f_dur" "$f_bud" "$f_lim" "$f_st"
      summary_body+="$row"
      summary_phase_dur f_dur "$s_nca" "$nc_admit_dur" "$nc_admit_start" "$now"
      format_duration f_lim "$nc_admit_timeout_s"
      status_label f_st "$s_nca" 0
      printf -v row '| no-comments admission (admit-no-comments) | %s | - | %s | %s |\n' "$f_dur" "$f_lim" "$f_st"
      summary_body+="$row"
      summary_phase_dur f_dur "$s_reg" "$regula_dur" "$regula_start" "$now"
      format_duration f_bud "$regula_budget_s"
      format_duration f_lim "$regula_timeout_s"
      status_label f_st "$s_reg" "$regula_over"
      printf -v row '| Regula audit (scripts/regula.sh) | %s | <= %s | %s | %s |\n' "$f_dur" "$f_bud" "$f_lim" "$f_st"
      summary_body+="$row"
      summary_phase_dur f_dur "$s_int" "$intent_dur" "$intent_start" "$now"
      format_duration f_lim "$intent_timeout_s"
      status_label f_st "$s_int" 0
      printf -v row '| lean-intent checks (intent-check) | %s | - | %s | %s |\n' "$f_dur" "$f_lim" "$f_st"
      summary_body+="$row"
      summary_phase_dur f_dur "$s_frm" "$frame_dur" "$frame_start" "$now"
      format_duration f_lim "$frame_timeout_s"
      status_label f_st "$s_frm" 0
      printf -v row '| Frame check (frame-check) | %s | - | %s | %s |\n' "$f_dur" "$f_lim" "$f_st"
      summary_body+="$row"
      summary_phase_dur f_dur "$s_nc" "$nc_exec_dur" "$nc_start" "$now"
      format_duration f_bud "$nc_budget_s"
      format_duration f_lim "$nc_timeout_s"
      status_label f_st "$s_nc" "$nc_over"
      printf -v row '| %s | %s | <= %s | %s | %s |\n' "$nc_label" "$f_dur" "$f_bud" "$f_lim" "$f_st"
      summary_body+="$row"
      summary_phase_dur f_dur "$s_post" "$post_wall_dur" "$post_start" "$now"
      printf -v row '| Post-verification wall (%s) | %s | - | - | - |\n' "$post_mode" "$f_dur"
      summary_body+="$row"
      format_duration f_dur "$gate_total_dur"
      format_duration f_bud "$gate_budget_s"
      status_label f_st "$gate_verdict_state" "$gate_over"
      printf -v row '| **Merge gate total (scripts/gate.sh)** | **%s** | **<= %s** | **18m** | **%s** |\n' "$f_dur" "$f_bud" "$f_st"
      summary_body+="$row"
      if [[ -n "$workflow_elapsed_dur" ]]; then
        format_duration f_dur "$workflow_elapsed_dur"
        format_duration f_bud "$job_budget_s"
        status_label f_st "$gate_verdict_state" "$job_over"
        printf -v row '| **Workflow elapsed (commit check through gate)** | **%s** | **<= %s** | **30m (job)** | **%s** |\n' "$f_dur" "$f_bud" "$f_st"
        summary_body+="$row"
      fi
      summary_body+=$'\n'
    fi
  fi

  if [[ "$timings_logged" == 0 ]]; then
    summary_phase_secs t_prov "$s_prov" "$provision_dur" "$provision_start" "$now"
    summary_phase_secs t_s1 "$s_s1" "$stage1_dur" "$stage1_start" "$now"
    summary_phase_secs t_s2 "$s_s2" "$stage2_dur" "$stage2_start" "$now"
    summary_phase_secs t_nca "$s_nca" "$nc_admit_dur" "$nc_admit_start" "$now"
    summary_phase_secs t_reg "$s_reg" "$regula_dur" "$regula_start" "$now"
    summary_phase_secs t_int "$s_int" "$intent_dur" "$intent_start" "$now"
    summary_phase_secs t_frm "$s_frm" "$frame_dur" "$frame_start" "$now"
    summary_phase_secs t_nc "$s_nc" "$nc_exec_dur" "$nc_start" "$now"
    summary_phase_secs t_post "$s_post" "$post_wall_dur" "$post_start" "$now"
    printf -v timings_line 'gate: phase timings (s): provision=%s stage1=%s stage2=%s nc-admit=%s regula=%s intent=%s frame=%s no-comments=%s post-wall=%s (%s, nc-jobs=%s) total=%d\n' \
      "$t_prov" "$t_s1" "$t_s2" "$t_nca" "$t_reg" "$t_int" "$t_frm" "$t_nc" "$t_post" \
      "$post_mode" "${nc_jobs:-none}" "$gate_total_dur"
  fi

  if [[ "$summary_table_written" == 0 && -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    if [[ "$summary_suitable" == 0 || -L "$GITHUB_STEP_SUMMARY" || ( -e "$GITHUB_STEP_SUMMARY" && ! -f "$GITHUB_STEP_SUMMARY" ) ]]; then
      echo "gate: refusing to write phase summary to unsuitable destination: $GITHUB_STEP_SUMMARY" >&2
      summary_fail=1
    elif printf '%s' "$summary_body" >> "$GITHUB_STEP_SUMMARY"; then
      summary_table_written=1
    else
      echo "gate: failed to write phase summary to $GITHUB_STEP_SUMMARY" >&2
      summary_fail=1
    fi
  fi

  if [[ "$warnings_emitted" == 0 ]]; then
    if [[ -n "$warnings_body" ]]; then
      printf '%s' "$warnings_body"
    fi
    warnings_emitted=1
  fi

  if [[ "$timings_logged" == 0 ]]; then
    printf '%s' "$timings_line"
    timings_logged=1
  fi

  summary_written=1

  if [[ "$summary_fail" != 0 && "$early_abort" == 0 ]]; then
    gate_passed=0
    return 1
  fi
}

# shellcheck disable=SC2317,SC2329
job_is_running() {
  local target_pid="$1" jobs_file="$2" line
  local re='^\[([0-9]+)\][+-]?[[:space:]]+([0-9]+)[[:space:]]+Running'
  [[ -n "$target_pid" && -n "$jobs_file" ]] || return 1
  jobs -rl > "$jobs_file" 2>/dev/null || return 1
  while IFS= read -r line; do
    if [[ "$line" =~ $re && "${BASH_REMATCH[2]}" == "$target_pid" ]]; then
      return 0
    fi
  done < "$jobs_file"
  return 1
}

spawn_pgid_reap_anchor() {
  local pgid_file="$1" read_fd="$2" mode="${3:-kill-only}" my_pgid='' cmd=''
  sh -c 'echo $PPID' > "$pgid_file"
  IFS= read -r my_pgid < "$pgid_file"
  rm -f "$pgid_file"
  if [[ "$mode" == 'term-then-kill' ]]; then
    (
      exec </dev/null >/dev/null 2>&1
      trap '' TERM
      while IFS= read -r cmd <&"$read_fd"; do
        case "$cmd" in
          term)
            if [[ "$my_pgid" =~ ^[0-9]+$ && "$my_pgid" -gt 1 && "$my_pgid" != "$$" ]]; then
              kill -TERM -- -"$my_pgid" 2>/dev/null || true
            fi ;;
        esac
      done
      if [[ "$my_pgid" =~ ^[0-9]+$ && "$my_pgid" -gt 1 && "$my_pgid" != "$$" ]]; then
        kill -KILL -- -"$my_pgid" 2>/dev/null || true
      fi
    ) &
  else
    (
      exec </dev/null >/dev/null 2>&1
      IFS= read -r _ <&"$read_fd" || true
      if [[ "$my_pgid" =~ ^[0-9]+$ && "$my_pgid" -gt 1 && "$my_pgid" != "$$" ]]; then
        kill -KILL -- -"$my_pgid" 2>/dev/null || true
      fi
    ) &
  fi
}

# shellcheck disable=SC2317,SC2329
reap_fg_group() {
  if [[ "$fg_reap_open" == 1 ]]; then
    exec 8>&- 9<&- 6>&-
    while IFS= read -r _ <&7; do :; done 2>/dev/null || true
    fg_reap_open=0
    exec 7<&-
  fi
}

# shellcheck disable=SC2317,SC2329
reap_sup_group() {
  if [[ "$sup_ctrl_open" == 1 ]]; then
    exec 4>&- 5<&- 6>&-
    while IFS= read -r _ <&3; do :; done 2>/dev/null || true
    sup_ctrl_open=0
    exec 3<&-
  fi
}

open_fg_reap_fifos() {
  local ctrl_fifo="$gate_scratch/fg.ctrl" done_fifo="$gate_scratch/fg.done"
  rm -f "$ctrl_fifo" "$done_fifo"
  mkfifo "$ctrl_fifo" "$done_fifo"
  exec 8<>"$ctrl_fifo"
  exec 9<"$ctrl_fifo"
  exec 6<>"$done_fifo"
  exec 7<"$done_fifo"
  rm -f "$ctrl_fifo" "$done_fifo"
  fg_reap_open=1
}

# Invoked by the EXIT/INT/TERM traps; older ShellCheck does not trace trap callbacks.
# shellcheck disable=SC2317,SC2329
cleanup_post_checks() {
  trap '' INT TERM
  local fg_pid="$fg_child_pid"
  local pid="$post_checks_pid"
  fg_child_pid=''
  post_checks_pid=''
  reap_fg_group
  if [[ -n "$fg_pid" ]]; then
    wait "$fg_pid" 2>/dev/null || true
  fi
  if [[ "$sup_ctrl_open" == 1 ]]; then
    if [[ -n "$pid" && -n "$gate_scratch" ]] && job_is_running "$pid" "$gate_scratch/jobs.tmp"; then
      printf 'term\n' >&4 2>/dev/null || true
      for _ in 1 2 3 4 5 6 7 8 9 10; do
        if ! job_is_running "$pid" "$gate_scratch/jobs.tmp"; then
          break
        fi
        sleep 0.1 3<&- 4>&-
      done
    fi
    reap_sup_group
  fi
  if [[ -n "$pid" ]]; then
    wait "$pid" 2>/dev/null || true
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
  local custom_tmpdir="$1"
  shift
  [[ -n "$custom_tmpdir" && ! -L "$custom_tmpdir" && -d "$custom_tmpdir" ]] || {
    echo 'gate: isolated TMPDIR missing for function phase' >&2
    return 1
  }
  local rc=0
  open_fg_reap_fifos
  set -m
  (
    set +m
    exec 3<&- 4>&- 7<&- 8>&-
    spawn_pgid_reap_anchor "$gate_scratch/fg.pgid" 9
    exec 6>&- 9<&-
    export TMPDIR="$custom_tmpdir"
    "$@"
  ) &
  fg_child_pid=$!
  set +m
  exec 6>&- 9<&-
  wait "$fg_child_pid" 2>/dev/null || rc=$?
  fg_child_pid=''
  reap_fg_group
  return "$rc"
}

# Run a foreground external command via exec in its own process group with isolated
# TMPDIR so tools that exec GNU timeout (notably scripts/verify.sh) keep PID == PGID ==
# fg_child_pid and cancellation signals reach and reap the timer and its descendants.
run_fg_exec() {
  local custom_tmpdir="$1"
  shift
  [[ -n "$custom_tmpdir" && ! -L "$custom_tmpdir" && -d "$custom_tmpdir" ]] || {
    echo 'gate: isolated TMPDIR missing for external phase' >&2
    return 1
  }
  local rc=0
  open_fg_reap_fifos
  set -m
  (
    set +m
    exec 3<&- 4>&- 7<&- 8>&-
    spawn_pgid_reap_anchor "$gate_scratch/fg.pgid" 9
    exec 6>&- 9<&-
    exec env TMPDIR="$custom_tmpdir" "$@"
  ) &
  fg_child_pid=$!
  set +m
  exec 6>&- 9<&-
  wait "$fg_child_pid" 2>/dev/null || rc=$?
  fg_child_pid=''
  reap_fg_group
  return "$rc"
}

run_fg_dep_bounded() {
  local limit_s="$1" custom_tmpdir="$2"
  shift 2
  [[ -n "$custom_tmpdir" && ! -L "$custom_tmpdir" && -d "$custom_tmpdir" ]] || {
    echo 'gate: isolated TMPDIR missing for bounded phase' >&2
    return 1
  }
  local rc=0
  open_fg_reap_fifos
  set -m
  (
    set +m
    exec 3<&- 4>&- 7<&- 8>&-
    spawn_pgid_reap_anchor "$gate_scratch/fg.pgid" 9
    exec 6>&- 9<&-
    dependency_git
    exec env TMPDIR="$custom_tmpdir" "$timeout_command" --signal=KILL "${limit_s}s" "$@"
  ) &
  fg_child_pid=$!
  set +m
  exec 6>&- 9<&-
  wait "$fg_child_pid" 2>/dev/null || rc=$?
  fg_child_pid=''
  reap_fg_group
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
  dependency_git
  cd site
  # Verso's modules and the shared library its documents load.
  lake -f lakefile.toml build verso/VersoManual verso/VersoManual:shared
}

provision_state='running'
provision_start="$SECONDS"
step 'provisioning the pinned dependencies'
run_fg_group "$gate_scratch/prov-tmp" provision_lean_workspace
run_fg_exec "$gate_scratch/prov-tmp" ./scripts/lean.sh provision-status
run_fg_exec "$gate_scratch/prov-tmp" ./scripts/tracked-files.sh admit-site --clean .
run_fg_group "$gate_scratch/prov-tmp" provision_site_workspace
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
  run_fg_exec "$nc_dl_dir" curl --fail --silent --show-error --location --proto '=https' --tlsv1.2 \
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
  rm -rf "$nc_dl_dir"
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
post_wall_state='running'
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
  bg_supervisor_launched=1
  sup_ctrl="$gate_scratch/sup.ctrl"
  sup_done="$gate_scratch/sup.done"
  rm -f "$sup_ctrl" "$sup_done"
  mkfifo "$sup_ctrl" "$sup_done"
  exec 4<>"$sup_ctrl"
  exec 5<"$sup_ctrl"
  exec 6<>"$sup_done"
  exec 3<"$sup_done"
  rm -f "$sup_ctrl" "$sup_done"
  sup_ctrl_open=1

  set -m
  (
    set +m
    exec 3<&- 4>&-
    spawn_pgid_reap_anchor "$gate_scratch/sup.pgid" 5 term-then-kill
    exec 5<&-
    bg_child_pid=''
    bg_reap_open=0
    # shellcheck disable=SC2317,SC2329
    reap_bg_group() {
      if [[ "$bg_reap_open" == 1 ]]; then
        exec 7>&- 8<&- 4>&-
        while IFS= read -r _ <&5; do :; done 2>/dev/null || true
        bg_reap_open=0
        exec 5<&-
      fi
    }
    # Invoked by the background subshell's EXIT/INT/TERM traps.
    # shellcheck disable=SC2317,SC2329
    cleanup_bg_child() {
      trap '' INT TERM
      local pid="$bg_child_pid"
      bg_child_pid=''
      reap_bg_group
      if [[ -n "$pid" ]]; then
        wait "$pid" 2>/dev/null || true
      fi
    }
    trap cleanup_bg_child EXIT
    trap 'cleanup_bg_child; exit 130' INT
    trap 'cleanup_bg_child; exit 143' TERM

    run_bg_bounded() {
      local limit_s="$1" custom_tmpdir="$2" prefix="$3"
      shift 3
      [[ -n "$custom_tmpdir" && ! -L "$custom_tmpdir" && -d "$custom_tmpdir" ]] || {
        echo "gate: isolated TMPDIR missing for background phase: $prefix" >&2
        return 1
      }
      local t0="$SECONDS" rc=0 ctrl_fifo="$gate_scratch/bg.ctrl" done_fifo="$gate_scratch/bg.done"
      printf '%d\n' "$t0" > "${prefix}.started.tmp"
      mv -f "${prefix}.started.tmp" "${prefix}.started"
      rm -f "$ctrl_fifo" "$done_fifo"
      mkfifo "$ctrl_fifo" "$done_fifo"
      exec 7<>"$ctrl_fifo"
      exec 8<"$ctrl_fifo"
      exec 4<>"$done_fifo"
      exec 5<"$done_fifo"
      rm -f "$ctrl_fifo" "$done_fifo"
      bg_reap_open=1
      set -m
      (
        set +m
        exec 5<&- 7>&-
        spawn_pgid_reap_anchor "$gate_scratch/bg.pgid" 8
        exec 4>&- 6>&- 8<&-
        dependency_git
        exec env TMPDIR="$custom_tmpdir" "$timeout_command" --signal=KILL "${limit_s}s" "$@"
      ) > "${prefix}.log" 2>&1 < /dev/null &
      bg_child_pid=$!
      set +m
      exec 4>&- 8<&-
      wait "$bg_child_pid" 2>/dev/null || rc=$?
      bg_child_pid=''
      reap_bg_group
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
  exec 5<&- 6>&-

  regula_state='running'
  regula_start="$SECONDS"
  audited=0
  run_fg_dep_bounded "$regula_timeout_s" "$gate_scratch/regula-tmp" ./scripts/regula.sh || audited=$?
  regula_dur=$((SECONDS - regula_start))
  regula_state="$audited"

  post_checks_status=0
  wait "$post_checks_pid" 2>/dev/null || post_checks_status=$?
  post_checks_pid=''
  reap_sup_group

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
post_wall_state='0'

if [[ "$post_checks_status" != 0 ]]; then
  echo "gate: background post-check supervisor exited $post_checks_status" >&2
fi
emit_gate_summary 0
[[ "$gate_passed" == 1 ]] || exit 1
step 'every merge check passed'
