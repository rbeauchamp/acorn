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
export -f admit_tracked_helper

# Invoked by the supervised child Bash through its exported definition.
# shellcheck disable=SC2329
acorn_verify_checks() {
  local admit_clean=1
  local sc_pin='scripts/shellcheck.pin'
  local sc_line1='' sc_line2='' sc_line3='' sc_line4='' sc_line5=''
  local sc_line6='' sc_line7='' sc_line8='' sc_line9='' sc_extra=''
  local sc_version='' sc_binary_sha256='' sc_actual_sha256=''
  local sc_dir='' sc_path='' sc_version_output='' sc_vline='' sc_found=''
  local sc_found_count=0 real_root='' real_dir='' dir=''
  local -a admit_args
  if [[ $("$2" --version) != *"GNU coreutils"* ]]; then
    echo "verification requires GNU coreutils timeout" >&2
    exit 127
  fi
  cd "$(dirname "$1")/.."
  if [[ ( "$#" == 4 && "$3" == "site" && "$4" == "write" ) ||
        ( "$#" == 3 && "$3" == "diagnostics" ) ]]; then
    admit_clean=0
  fi
  admit_tracked_helper . "$admit_clean" || {
    echo "verify.sh: scripts/tracked-files.sh failed pre-execution Git admission" >&2
    exit 1
  }
  admit_args=(admit-file)
  if [[ "$admit_clean" == 1 ]]; then
    admit_args+=(--clean)
  fi
  ./scripts/tracked-files.sh "${admit_args[@]}" . \
    scripts/tracked-files.sh scripts/verify.sh scripts/lean.sh scripts/start.sh scripts/gate.sh scripts/regula.sh "$sc_pin"
  git diff --check
  git diff --cached --check
  if [[ -L "$sc_pin" || ! -f "$sc_pin" ]]; then
    echo "verify.sh: missing or non-regular pin file: $sc_pin" >&2
    exit 1
  fi
  {
    IFS= read -r sc_line1 &&
      IFS= read -r sc_line2 &&
      IFS= read -r sc_line3 &&
      IFS= read -r sc_line4 &&
      IFS= read -r sc_line5 &&
      IFS= read -r sc_line6 &&
      IFS= read -r sc_line7 &&
      IFS= read -r sc_line8 &&
      IFS= read -r sc_line9 &&
      ! IFS= read -r sc_extra &&
      [[ -z "$sc_extra" ]]
  } < "$sc_pin" || {
    echo "verify.sh: malformed pin file: $sc_pin" >&2
    exit 1
  }
  if [[ ! $sc_line1 =~ ^VERSION=([0-9]+\.[0-9]+\.[0-9]+)$ ]] ||
      [[ ! $sc_line2 =~ ^DARWIN_ARM64_ARCHIVE_SHA256=([0-9a-f]{64})$ ]] ||
      [[ ! $sc_line3 =~ ^DARWIN_ARM64_BINARY_SHA256=([0-9a-f]{64})$ ]] ||
      [[ ! $sc_line4 =~ ^DARWIN_X86_64_ARCHIVE_SHA256=([0-9a-f]{64})$ ]] ||
      [[ ! $sc_line5 =~ ^DARWIN_X86_64_BINARY_SHA256=([0-9a-f]{64})$ ]] ||
      [[ ! $sc_line6 =~ ^LINUX_X86_64_ARCHIVE_SHA256=([0-9a-f]{64})$ ]] ||
      [[ ! $sc_line7 =~ ^LINUX_X86_64_BINARY_SHA256=([0-9a-f]{64})$ ]] ||
      [[ ! $sc_line8 =~ ^LINUX_ARM64_ARCHIVE_SHA256=([0-9a-f]{64})$ ]] ||
      [[ ! $sc_line9 =~ ^LINUX_ARM64_BINARY_SHA256=([0-9a-f]{64})$ ]]; then
    echo "verify.sh: malformed pin values in $sc_pin" >&2
    exit 1
  fi
  sc_version="${sc_line1#VERSION=}"
  case "$(uname -s)-$(uname -m)" in
    Darwin-arm64) sc_binary_sha256="${sc_line3#DARWIN_ARM64_BINARY_SHA256=}" ;;
    Darwin-x86_64) sc_binary_sha256="${sc_line5#DARWIN_X86_64_BINARY_SHA256=}" ;;
    Linux-x86_64) sc_binary_sha256="${sc_line7#LINUX_X86_64_BINARY_SHA256=}" ;;
    Linux-aarch64) sc_binary_sha256="${sc_line9#LINUX_ARM64_BINARY_SHA256=}" ;;
    *)
      echo "verify.sh: unsupported platform for pinned ShellCheck: $(uname -s)-$(uname -m)" >&2
      exit 1 ;;
  esac
  sc_dir="lean/.lake/packages/.shellcheck/$sc_version"
  sc_path="$sc_dir/shellcheck"
  real_root=$(pwd -P) || {
    echo "verify.sh: failed to resolve repository root" >&2
    exit 1
  }
  for dir in lean lean/.lake lean/.lake/packages lean/.lake/packages/.shellcheck "$sc_dir"; do
    if [[ -L "$dir" ]]; then
      echo "verify.sh: refusing symlinked ShellCheck cache directory: $dir" >&2
      exit 1
    elif [[ ! -e "$dir" ]]; then
      echo "verify.sh: pinned ShellCheck $sc_version is required at $sc_path (run ./scripts/gate.sh provision or see docs/verification.md#platform-setup)" >&2
      exit 127
    elif [[ ! -d "$dir" ]]; then
      echo "verify.sh: refusing non-directory ShellCheck cache path: $dir" >&2
      exit 1
    fi
  done
  real_dir=$(cd "$sc_dir" && pwd -P) || {
    echo "verify.sh: failed to resolve ShellCheck cache directory: $sc_dir" >&2
    exit 1
  }
  if [[ "$real_dir" != "$real_root/$sc_dir" ]]; then
    echo "verify.sh: ShellCheck cache directory resolves outside workspace: $sc_dir" >&2
    exit 1
  fi
  if [[ -L "$sc_path" ]]; then
    echo "verify.sh: refusing symlinked ShellCheck binary: $sc_path" >&2
    exit 1
  elif [[ ! -e "$sc_path" ]]; then
    echo "verify.sh: pinned ShellCheck $sc_version is required at $sc_path (run ./scripts/gate.sh provision or see docs/verification.md#platform-setup)" >&2
    exit 127
  elif [[ ! -f "$sc_path" || ! -x "$sc_path" ]]; then
    echo "verify.sh: pinned ShellCheck at $sc_path must be an executable regular file" >&2
    exit 1
  fi
  if ! command -v openssl >/dev/null 2>&1; then
    echo "verify.sh: OpenSSL is required for ShellCheck SHA-256 verification" >&2
    exit 127
  fi
  if ! sc_actual_sha256=$(openssl dgst -sha256 -r "$sc_path" | awk '{print $1}'); then
    echo "verify.sh: failed to compute SHA-256 for $sc_path" >&2
    exit 1
  fi
  if [[ "$sc_actual_sha256" != "$sc_binary_sha256" ]]; then
    echo "verify.sh: ShellCheck SHA-256 mismatch at $sc_path (found ${sc_actual_sha256:-unknown}, admitted $sc_binary_sha256)" >&2
    exit 1
  fi
  if ! sc_version_output=$(SHELLCHECK_OPTS='' "$sc_path" --version 2>&1); then
    echo "verify.sh: failed to query ShellCheck version at $sc_path (admitted $sc_version): $sc_version_output" >&2
    exit 1
  fi
  while IFS= read -r sc_vline; do
    sc_vline="${sc_vline%$'\r'}"
    if [[ "$sc_vline" =~ ^version:[[:space:]]*([^[:space:]]+)[[:space:]]*$ ]]; then
      sc_found="${BASH_REMATCH[1]}"
      sc_found_count=$((sc_found_count + 1))
    fi
  done <<< "$sc_version_output"
  if [[ "$sc_found_count" != 1 || "$sc_found" != "$sc_version" ]]; then
    echo "verify.sh: ShellCheck version mismatch at $sc_path (found ${sc_found:-unknown}, admitted $sc_version)" >&2
    exit 1
  fi
  SHELLCHECK_OPTS='' "$sc_path" --norc \
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
