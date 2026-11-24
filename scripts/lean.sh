#!/bin/bash
# The pinned Lean toolchain owns dependency admission and Lake invocation.
# `exe NAME ARGS` runs the Acorn program NAME. In work on a change, only an
# invocation on the closed list in the Test instructions of .no-mistakes.yaml is
# run without the owner's authorization (CONTRIBUTING.md, "Running a program").
set -euo pipefail
repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
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

admit_clean=0
if [[ "$#" -ge 1 && "$1" == "exe" ]] &&
    ! [[ "$#" == 4 && "$2" == "acorn-gates" && "$3" == "site" && "$4" == "write" ]]; then
  admit_clean=1
fi
admit_tracked_helper "$repo_root" "$admit_clean" || {
  echo "lean.sh: scripts/tracked-files.sh failed pre-execution Git admission" >&2
  exit 1
}
admit_file_args=(admit-file)
admit_dir_args=(admit-lake-dirs --workspace lean)
if [[ "$admit_clean" == 1 ]]; then
  admit_file_args+=(--clean)
  admit_dir_args+=(--clean)
fi
"$repo_root/scripts/tracked-files.sh" "${admit_file_args[@]}" "$repo_root" \
  scripts/tracked-files.sh scripts/lean.sh lean/Bootstrap.lean lean/lean-toolchain lean/lakefile.lean lean/lake-manifest.json
"$repo_root/scripts/tracked-files.sh" "${admit_dir_args[@]}" "$repo_root"
cd "$repo_root/lean"
exec lean -DwarningAsError=true -DautoImplicit=false --run Bootstrap.lean "$@"
