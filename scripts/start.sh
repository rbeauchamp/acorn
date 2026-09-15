#!/bin/bash
# Prepare the pinned application and supervise one local viewer launch.
set -euo pipefail
umask 077

usage() {
  cat <<'HELP'
Usage: ./scripts/start.sh [--no-browser] [--prepare-only] [--run-dir DIR] [--port N]

With no options, prepare and build Acorn, open the browser, and start or resume
the continuous agent. Stop in the viewer, or press Ctrl-C here to finish the
current attempt and close the viewer. Saved learner state stays in acorn-run/.

  --no-browser    Print the viewer URL without opening a browser.
  --prepare-only  Install prerequisites and build, without starting a run.
  --run-dir DIR   Use another run directory (relative paths use the repo root).
  --port N        Use a specific port; the default selects an available port.
HELP
}

fail() { printf 'Acorn: %s\n' "$*" >&2; exit 1; }
root=$(cd "$(dirname "$0")/.." && pwd -P)
run_dir="$root/acorn-run"
port=0
open_browser=1
prepare_only=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --help|-h) usage; exit 0 ;;
    --no-browser) open_browser=0; shift ;;
    --prepare-only) prepare_only=1; shift ;;
    --run-dir|--port)
      [[ $# -ge 2 && -n "$2" && "$2" != --* ]] || fail "$1 needs a value."
      if [[ "$1" == --run-dir ]]; then run_dir=$2; else port=$2; fi
      shift 2 ;;
    *) fail "Unknown option $1. Run ./scripts/start.sh --help." ;;
  esac
done
if [[ ! "$port" =~ ^[0-9]{1,5}$ ]]; then fail 'Port must be between 0 and 65535.'; fi
if ((10#$port > 65535)); then fail 'Port must be between 0 and 65535.'; fi
[[ $EUID -ne 0 ]] || fail 'Run this script as your normal user, without sudo.'
cd "$root"

# This lock spans preparation and execution and survives whole-run Clear.
# A crash leaves a visible lock; an uncertain owner is never silently displaced.
lock="$root/.acorn-launch"
if ! mkdir "$lock" 2>/dev/null; then
  fail "Another launcher is active, or an interrupted launch left $lock. Use the original terminal; see docs/verification.md for interrupted-launch recovery."
fi
printf '%s\n' "$$" > "$lock/pid"
viewer_pid=
control_open=0
stopping=0
phase='preparation'

request_stop() {
  if [[ "$stopping" == 0 ]]; then
    stopping=1
    printf '\nStopping Acorn; finishing the current attempt and checkpoint before closing…\n'
    printf 'stop\n' >&3
  fi
}

# Invoked by the EXIT trap; older ShellCheck does not trace trap callbacks.
# shellcheck disable=SC2317,SC2329
cleanup() {
  local status=$?
  trap - EXIT
  if [[ -n "$viewer_pid" ]] && kill -0 "$viewer_pid" 2>/dev/null; then
    request_stop
    while kill -0 "$viewer_pid" 2>/dev/null; do wait "$viewer_pid" || true; done
  fi
  if [[ "$control_open" == 1 ]]; then exec 3>&-; fi
  rm -f "$lock/control" "$lock/pid" "$lock/installer.sh"
  rmdir "$lock"
  if [[ "$status" -ne 0 ]]; then
    printf 'Acorn stopped during %s. Resolve the diagnostic above, then run ./scripts/start.sh again.\n' "$phase" >&2
  fi
  exit "$status"
}
# Invoked by the INT/TERM traps; older ShellCheck does not trace trap callbacks.
# shellcheck disable=SC2317,SC2329
on_signal() {
  if [[ -n "$viewer_pid" ]]; then request_stop; else exit 130; fi
}
trap cleanup EXIT
trap on_signal INT TERM

export PATH="${ELAN_HOME:-$HOME/.elan}/bin:/opt/homebrew/bin:/usr/local/bin:$PATH"

install_macos() {
  # A usable installed CLT is sufficient even when an unrelated Xcode selection
  # is unavailable; the selection below is local to this launch, never global.
  if ! xcrun --find clang >/dev/null 2>&1 || ! git --version >/dev/null 2>&1; then
    if [[ -x /Library/Developer/CommandLineTools/usr/bin/clang ]]; then
      export DEVELOPER_DIR=/Library/Developer/CommandLineTools
      export SDKROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk
      export PATH="$DEVELOPER_DIR/usr/bin:$PATH"
    else
      xcode-select --install || true
      fail 'Finish the macOS command-line tools installation dialog, then run this script again.'
    fi
  fi
  if ! command -v brew >/dev/null 2>&1; then
    printf 'Installing Homebrew using its official installer; follow its system prompts.\n'
    curl --fail --location --retry 3 --connect-timeout 15 --max-time 300 \
      https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh -o "$lock/installer.sh"
    /bin/bash "$lock/installer.sh"
  fi
  command -v brew >/dev/null 2>&1 || fail 'Homebrew is unavailable after installation.'
  local packages=()
  command -v elan >/dev/null 2>&1 || packages+=(elan)
  command -v shellcheck >/dev/null 2>&1 || packages+=(shellcheck)
  command -v gtimeout >/dev/null 2>&1 || packages+=(coreutils)
  local openssl_prefix
  openssl_prefix=$(brew --prefix openssl@3)
  [[ -x "$openssl_prefix/bin/openssl" ]] || packages+=(openssl@3)
  if [[ ${#packages[@]} -gt 0 ]]; then brew install "${packages[@]}"; fi
  export PATH="$openssl_prefix/bin:$PATH"
}

install_linux() {
  command -v apt-get >/dev/null 2>&1 || fail 'Automatic Linux setup supports Ubuntu/Debian with apt-get; see docs/verification.md.'
  local packages=() package
  for package in build-essential curl git libgmp-dev openssl shellcheck coreutils elan; do
    if [[ $(dpkg-query -W -f='${Status}' "$package" 2>/dev/null || true) != 'install ok installed' ]]; then
      packages+=("$package")
    fi
  done
  if [[ "$open_browser" == 1 ]] && ! command -v xdg-open >/dev/null 2>&1; then packages+=(xdg-utils); fi
  if [[ ${#packages[@]} -gt 0 ]]; then
    printf 'Installing required system packages; sudo may ask for your password.\n'
    sudo apt-get update
    sudo apt-get install -y "${packages[@]}"
  fi
}

printf 'Preparing Acorn…\n'
case "$(uname -s)" in
  Darwin) install_macos ;;
  Linux) install_linux ;;
  *) fail 'This launcher supports macOS and Ubuntu/Debian Linux.' ;;
esac
for tool in git curl cc openssl elan lean lake; do
  command -v "$tool" >/dev/null 2>&1 || fail "Required tool is unavailable: $tool."
done
git --version >/dev/null

# Elan selects lean-toolchain without changing the user's global default.
# The existing offline bootstrap admits locally provisioned dependencies.
acorn_toolchain=$(cat lean/lean-toolchain)
export ELAN_TOOLCHAIN="$acorn_toolchain"
elan run --install "$acorn_toolchain" lean --version
dependency_status=0
./scripts/lean.sh provision-status || dependency_status=$?
case "$dependency_status" in
  0) ;;
  2)
    printf 'Downloading the pinned Lean and Mathlib dependencies (first run needs network access)…\n'
    (cd lean && lake exe cache get) ;;
  *) fail 'Dependency admission failed; the diagnostic above must be resolved before provisioning.' ;;
esac
phase='build'
printf 'Building Acorn (subsequent launches reuse unchanged build outputs)…\n'
./scripts/lean.sh build acorn-viewer
if [[ "$prepare_only" == 1 ]]; then
  printf 'Acorn is built. Run ./scripts/start.sh to open the viewer and start learning.\n'
  exit 0
fi

phase='viewer startup or execution'
arguments=(--research-profile ranked --start --control-stdin --port "$port" --run-dir "$run_dir")
if [[ "$open_browser" == 1 ]]; then arguments+=(--open-browser); fi
mkfifo "$lock/control"
# The parent keeps a writer while the native scoped reader owns shutdown.
exec 3<>"$lock/control"
control_open=1
printf '\nStarting Acorn. Use Stop in the browser, or Ctrl-C here to stop and close.\n'
interrupted=0
trap 'interrupted=1' INT TERM
(
  # Terminal interrupts belong to the launcher. The viewer and its descendants
  # receive the cooperative request through stdin instead of group SIGINT.
  trap '' INT
  exec lean/.lake/build/bin/acorn-viewer "${arguments[@]}" < "$lock/control" 3>&-
) &
viewer_pid=$!
trap on_signal INT TERM
if [[ "$interrupted" == 1 ]]; then request_stop; fi
status=0
while :; do
  wait "$viewer_pid" && status=0 || status=$?
  if ! kill -0 "$viewer_pid" 2>/dev/null; then break; fi
done
wait "$viewer_pid" && status=0 || status=$?
viewer_pid=
exit "$status"
