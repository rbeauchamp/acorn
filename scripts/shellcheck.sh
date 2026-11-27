#!/bin/bash
# Single checked ShellCheck pin policy: provision into or execute from the
# dedicated workspace cache under lean/.lake/packages/.shellcheck.
set -euo pipefail

usage='usage: ./scripts/shellcheck.sh (provision|check <file>...)'
cmd="${1:-}"
case "$cmd" in
  provision|check) shift ;;
  *) echo "$usage" >&2; exit 2 ;;
esac

cd "$(dirname "$0")/.."
real_root=$(pwd -P) || {
  echo 'shellcheck.sh: failed to resolve repository root' >&2
  exit 1
}

sc_pin='scripts/shellcheck.pin'
if [[ -L scripts || ! -d scripts || -L "$sc_pin" || ! -f "$sc_pin" ]]; then
  echo "shellcheck.sh: missing or non-regular pin file: $sc_pin" >&2
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
  echo "shellcheck.sh: malformed pin file: $sc_pin" >&2
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
  echo "shellcheck.sh: malformed pin values in $sc_pin" >&2
  exit 1
fi

sc_version="${sc_line1#VERSION=}"
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    sc_platform='darwin.aarch64'
    sc_archive_sha256="${sc_line2#DARWIN_ARM64_ARCHIVE_SHA256=}"
    sc_binary_sha256="${sc_line3#DARWIN_ARM64_BINARY_SHA256=}" ;;
  Darwin-x86_64)
    sc_platform='darwin.x86_64'
    sc_archive_sha256="${sc_line4#DARWIN_X86_64_ARCHIVE_SHA256=}"
    sc_binary_sha256="${sc_line5#DARWIN_X86_64_BINARY_SHA256=}" ;;
  Linux-x86_64)
    sc_platform='linux.x86_64'
    sc_archive_sha256="${sc_line6#LINUX_X86_64_ARCHIVE_SHA256=}"
    sc_binary_sha256="${sc_line7#LINUX_X86_64_BINARY_SHA256=}" ;;
  Linux-aarch64)
    sc_platform='linux.aarch64'
    sc_archive_sha256="${sc_line8#LINUX_ARM64_ARCHIVE_SHA256=}"
    sc_binary_sha256="${sc_line9#LINUX_ARM64_BINARY_SHA256=}" ;;
  *)
    echo "shellcheck.sh: unsupported platform for pinned ShellCheck: $(uname -s)-$(uname -m)" >&2
    exit 1 ;;
esac

sc_pkg_dir='lean/.lake/packages'
sc_root="$sc_pkg_dir/.shellcheck"
sc_dir="$sc_root/$sc_version"
sc_bin="$sc_dir/shellcheck"

require_openssl() {
  if ! command -v openssl >/dev/null 2>&1; then
    echo 'shellcheck.sh: OpenSSL is required for ShellCheck SHA-256 verification' >&2
    exit 127
  fi
}

sha256_of() {
  local file="$1"
  [[ -f "$file" && ! -L "$file" ]] || return 1
  openssl dgst -sha256 -r "$file" | awk '{print $1}'
}

verify_shellcheck_version() {
  local bin="$1" expected="$2" out='' line='' found='' count=0
  if ! out=$(SHELLCHECK_OPTS='' "$bin" --version 2>&1); then
    echo "shellcheck.sh: failed to query ShellCheck version at $bin (admitted $expected): $out" >&2
    return 1
  fi
  while IFS= read -r line; do
    line="${line%$'\r'}"
    if [[ "$line" =~ ^version:[[:space:]]*([^[:space:]]+)[[:space:]]*$ ]]; then
      found="${BASH_REMATCH[1]}"
      count=$((count + 1))
    fi
  done <<< "$out"
  if [[ "$count" != 1 || "$found" != "$expected" ]]; then
    echo "shellcheck.sh: ShellCheck version mismatch at $bin (found ${found:-unknown}, admitted $expected)" >&2
    return 1
  fi
}

check_cache_dirs() {
  local mode="$1" dir real_dir
  if [[ -L lean || ! -d lean ]]; then
    echo 'shellcheck.sh: workspace directory lean must be a real directory' >&2
    return 1
  fi
  real_dir=$(cd lean && pwd -P) || return 1
  if [[ "$real_dir" != "$real_root/lean" ]]; then
    echo 'shellcheck.sh: workspace directory lean resolves outside repository' >&2
    return 1
  fi
  for dir in lean/.lake "$sc_pkg_dir" "$sc_root" "$sc_dir"; do
    if [[ -L "$dir" ]]; then
      echo "shellcheck.sh: refusing symlinked ShellCheck cache directory: $dir" >&2
      return 1
    elif [[ -e "$dir" && ! -d "$dir" ]]; then
      echo "shellcheck.sh: refusing non-directory ShellCheck cache path: $dir" >&2
      return 1
    elif [[ -d "$dir" ]]; then
      real_dir=$(cd "$dir" && pwd -P) || return 1
      if [[ "$real_dir" != "$real_root/$dir" ]]; then
        echo "shellcheck.sh: ShellCheck cache directory resolves outside workspace: $dir" >&2
        return 1
      fi
    elif [[ "$mode" != allow-missing ]]; then
      echo "shellcheck.sh: pinned ShellCheck $sc_version is required at $sc_bin (run ./scripts/shellcheck.sh provision or ./scripts/gate.sh provision)" >&2
      return 127
    fi
  done
}

ensure_cache_dirs() {
  local dir real_dir
  check_cache_dirs allow-missing || return 1
  for dir in lean/.lake "$sc_pkg_dir" "$sc_root" "$sc_dir"; do
    if [[ ! -e "$dir" ]]; then
      mkdir "$dir" || return 1
    fi
    if [[ -L "$dir" || ! -d "$dir" ]]; then
      echo "shellcheck.sh: refusing non-directory or symlinked ShellCheck cache path: $dir" >&2
      return 1
    fi
    real_dir=$(cd "$dir" && pwd -P) || return 1
    if [[ "$real_dir" != "$real_root/$dir" ]]; then
      echo "shellcheck.sh: ShellCheck cache directory resolves outside workspace: $dir" >&2
      return 1
    fi
  done
  check_cache_dirs require-present
}

case "$cmd" in
  check)
    if (( $# == 0 )); then
      echo "$usage" >&2
      exit 2
    fi
    rc=0
    check_cache_dirs require-present || rc=$?
    if [[ "$rc" != 0 ]]; then
      exit "$rc"
    fi
    if [[ -L "$sc_bin" ]]; then
      echo "shellcheck.sh: refusing symlinked ShellCheck binary: $sc_bin" >&2
      exit 1
    elif [[ ! -e "$sc_bin" ]]; then
      echo "shellcheck.sh: pinned ShellCheck $sc_version is required at $sc_bin (run ./scripts/shellcheck.sh provision or ./scripts/gate.sh provision)" >&2
      exit 127
    elif [[ ! -f "$sc_bin" || ! -x "$sc_bin" ]]; then
      echo "shellcheck.sh: pinned ShellCheck at $sc_bin must be an executable regular file" >&2
      exit 1
    fi
    require_openssl
    if ! sc_actual_sha256=$(sha256_of "$sc_bin"); then
      echo "shellcheck.sh: failed to compute SHA-256 for $sc_bin" >&2
      exit 1
    fi
    if [[ "$sc_actual_sha256" != "$sc_binary_sha256" ]]; then
      echo "shellcheck.sh: ShellCheck SHA-256 mismatch at $sc_bin (found ${sc_actual_sha256:-unknown}, admitted $sc_binary_sha256)" >&2
      exit 1
    fi
    verify_shellcheck_version "$sc_bin" "$sc_version"
    exec env SHELLCHECK_OPTS='' "$sc_bin" --norc "$@"
    ;;
  provision)
    if (( $# != 0 )); then
      echo "$usage" >&2
      exit 2
    fi
    check_cache_dirs allow-missing
    if [[ -L "$sc_bin" || ( -e "$sc_bin" && ! -f "$sc_bin" ) ]]; then
      echo "shellcheck.sh: refusing symlinked or non-regular cache entry: $sc_bin" >&2
      exit 1
    fi
    require_openssl
    if [[ -f "$sc_bin" ]]; then
      if sc_actual_sha256=$(sha256_of "$sc_bin") && [[ "$sc_actual_sha256" == "$sc_binary_sha256" ]]; then
        [[ -x "$sc_bin" ]] || chmod 755 "$sc_bin"
        verify_shellcheck_version "$sc_bin" "$sc_version"
        exit 0
      fi
      echo "shellcheck.sh: cached $sc_bin failed SHA-256 verification; re-downloading" >&2
    fi
    for tool in curl tar; do
      if ! command -v "$tool" >/dev/null 2>&1; then
        echo "shellcheck.sh: required tool is unavailable: $tool" >&2
        exit 127
      fi
    done
    sc_scratch=$(mktemp -d)
    sc_stage=''
    # shellcheck disable=SC2317,SC2329
    cleanup() {
      if [[ -n "$sc_stage" ]]; then
        rm -f -- "$sc_stage"
      fi
      rm -rf -- "$sc_scratch"
    }
    trap cleanup EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    sc_archive="$sc_scratch/shellcheck.tar.gz"
    sc_extract="$sc_scratch/extract"
    curl --fail --silent --show-error --location --proto '=https' --tlsv1.2 \
      --connect-timeout 10 --max-time 180 --retry 2 --retry-delay 2 --retry-max-time 300 \
      --output "$sc_archive" \
      "https://github.com/koalaman/shellcheck/releases/download/v${sc_version}/shellcheck-v${sc_version}.${sc_platform}.tar.gz"
    if ! sc_actual_sha256=$(sha256_of "$sc_archive") || [[ "$sc_actual_sha256" != "$sc_archive_sha256" ]]; then
      echo "shellcheck.sh: downloaded shellcheck-v${sc_version}.${sc_platform}.tar.gz failed SHA-256 verification" >&2
      exit 1
    fi
    mkdir -p "$sc_extract"
    tar -xzf "$sc_archive" -C "$sc_extract" "shellcheck-v${sc_version}/shellcheck"
    sc_extracted="$sc_extract/shellcheck-v${sc_version}/shellcheck"
    if ! sc_actual_sha256=$(sha256_of "$sc_extracted") || [[ "$sc_actual_sha256" != "$sc_binary_sha256" ]]; then
      echo 'shellcheck.sh: extracted ShellCheck binary failed SHA-256 verification' >&2
      exit 1
    fi
    chmod 755 "$sc_extracted"
    verify_shellcheck_version "$sc_extracted" "$sc_version"
    ensure_cache_dirs
    sc_stage=$(mktemp "$sc_dir/shellcheck.XXXXXX")
    if ! cp "$sc_extracted" "$sc_stage" || ! chmod 755 "$sc_stage"; then
      echo "shellcheck.sh: failed to stage ShellCheck binary in $sc_dir" >&2
      exit 1
    fi
    if [[ -L "$sc_bin" || ( -e "$sc_bin" && ! -f "$sc_bin" ) ]]; then
      echo "shellcheck.sh: refusing symlinked or non-regular cache entry: $sc_bin" >&2
      exit 1
    fi
    if ! mv -f "$sc_stage" "$sc_bin"; then
      echo "shellcheck.sh: failed to install ShellCheck binary at $sc_bin" >&2
      exit 1
    fi
    sc_stage=''
    ;;
esac
