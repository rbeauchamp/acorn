#!/bin/bash
# The pinned Lean toolchain owns dependency admission and Lake invocation.
# `exe NAME ARGS` runs the Acorn program NAME. In work on a change, only an
# invocation on the closed list in the Test instructions of .no-mistakes.yaml is
# run without the owner's authorization (CONTRIBUTING.md, "Running a program").
set -euo pipefail
repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
[[ ! -L "$repo_root/scripts" && -d "$repo_root/scripts" && ! -L "$repo_root/scripts/tracked-files.sh" && -f "$repo_root/scripts/tracked-files.sh" ]] || {
  echo "lean.sh: missing non-symlink scripts/tracked-files.sh" >&2
  exit 1
}
"$repo_root/scripts/tracked-files.sh" admit-file "$repo_root" \
  scripts/tracked-files.sh scripts/lean.sh lean/Bootstrap.lean lean/lean-toolchain lean/lakefile.lean lean/lake-manifest.json
"$repo_root/scripts/tracked-files.sh" admit-lake-dirs "$repo_root"
cd "$repo_root/lean"
exec lean -DwarningAsError=true -DautoImplicit=false --run Bootstrap.lean "$@"
