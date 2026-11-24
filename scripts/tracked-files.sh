#!/bin/bash
set -euo pipefail

fail() {
  echo "tracked-files: $1" >&2
  exit 1
}

verify_repo_root() {
  local root="$1" top prefix_dir real_root real_top
  [[ -n "$root" && ! -L "$root" && -d "$root" ]] || fail "repository root is not a directory: $root"
  top=$(git -C "$root" rev-parse --show-toplevel) || fail "not a git repository: $root"
  prefix_dir=$(git -C "$root" rev-parse --show-prefix) || fail "git rev-parse --show-prefix failed: $root"
  [[ -n "$top" && -z "$prefix_dir" ]] || fail "expected repository root, got prefix '$prefix_dir' in $root"
  real_root=$(cd "$root" && pwd -P)
  real_top=$(cd "$top" && pwd -P)
  [[ "$real_root" == "$real_top" ]] || fail "git root mismatch for $root"
}

check_rel_path() {
  local rel="$1"
  [[ -n "$rel" ]] || fail "empty tracked path"
  [[ "$rel" != /* && "$rel" != */ ]] || fail "unsupported leading/trailing slash in $rel"
  [[ "$rel" != :* && "$rel" != -* ]] || fail "unsupported path prefix in $rel"
  [[ "$rel" != *$'\n'* && "$rel" != *$'\r'* ]] || fail "newline in tracked path"
}

admit_one_file() {
  local root="$1" rel="$2" tmp rec line meta path mode oid stage extra cur part
  local -a parts
  local count=0 i last_idx
  check_rel_path "$rel"
  IFS='/' read -r -a parts <<< "$rel"
  cur=""
  last_idx=$(( ${#parts[@]} - 1 ))
  for (( i = 0; i < ${#parts[@]}; i++ )); do
    part="${parts[$i]}"
    [[ -n "$part" && "$part" != "." && "$part" != ".." ]] || fail "unsupported path component in $rel"
    if (( i < last_idx )); then
      cur="${cur:+$cur/}$part"
      [[ ! -L "$root/$cur" && -d "$root/$cur" ]] || fail "non-directory ancestor: $cur"
    fi
  done
  [[ ! -L "$root/$rel" && -f "$root/$rel" ]] || fail "path is not a regular file: $rel"

  tmp=$(mktemp "${TMPDIR:-/tmp}/acorn-lsfiles.XXXXXX")
  if ! git --literal-pathspecs -C "$root" -c core.quotePath=false ls-files --stage -z -- "$rel" > "$tmp"; then
    rm -f "$tmp"
    fail "git ls-files failed for $rel"
  fi
  rec=''
  while IFS= read -r -d '' line; do
    rec="$line"
    count=$((count + 1))
  done < "$tmp"
  rm -f "$tmp"
  (( count == 1 )) || fail "path is not uniquely tracked: $rel"

  meta="${rec%%$'\t'*}"
  path="${rec#*$'\t'}"
  [[ "$meta" != "$rec" ]] || fail "malformed git ls-files record for $rel"
  IFS=' ' read -r mode oid stage extra <<< "$meta"
  [[ -z "${extra:-}" && "$path" == "$rel" && "$stage" == "0" && ( "$mode" == "100644" || "$mode" == "100755" ) && "$oid" =~ ^[0-9a-f]{40}([0-9a-f]{24})?$ ]] ||
    fail "path is not a stage-0 tracked regular file: $rel"
}

admit_pkg_lake_containment() {
  local root="$1" pkg="$2" pkg_dir lake_dir config_dir f
  pkg_dir="$root/$pkg"
  [[ ! -L "$pkg_dir" && -d "$pkg_dir" ]] || fail "$pkg is not a real directory"
  lake_dir="$pkg_dir/.lake"
  if [[ -L "$lake_dir" ]]; then
    fail "refusing symlinked .lake directory: $pkg/.lake"
  fi
  if [[ -e "$lake_dir" ]]; then
    [[ -d "$lake_dir" ]] || fail "refusing non-directory .lake path: $pkg/.lake"
    if [[ -e "$lake_dir/package-overrides.json" || -L "$lake_dir/package-overrides.json" ]]; then
      fail "unbound $pkg/.lake/package-overrides.json; remove the ambient override"
    fi
    for f in "$lake_dir/acorn-path-packages.json" "$lake_dir/acorn-tracked-modules.z"; do
      if [[ -L "$f" ]] || { [[ -e "$f" ]] && [[ ! -f "$f" ]]; }; then
        fail "non-regular cache file: $f"
      fi
    done
    config_dir="$lake_dir/config"
    if [[ -L "$config_dir" ]]; then
      fail "refusing symlinked Lake config cache: $pkg/.lake/config"
    fi
    if [[ -e "$config_dir" ]]; then
      [[ -d "$config_dir" ]] || fail "refusing non-directory Lake config cache: $pkg/.lake/config"
    fi
  fi
}

admit_lake_dirs() {
  local root="$1"
  verify_repo_root "$root"
  admit_pkg_lake_containment "$root" lean
  admit_pkg_lake_containment "$root" site
  [[ ! -e "$root/lean/lakefile.toml" && ! -L "$root/lean/lakefile.toml" ]] ||
    fail "unexpected lean/lakefile.toml shadowing lean/lakefile.lean"
  [[ ! -e "$root/site/lakefile.lean" && ! -L "$root/site/lakefile.lean" ]] ||
    fail "unexpected site/lakefile.lean shadowing site/lakefile.toml"
}

clean_acorn_config_cache() {
  local lake_dir="$1" config_dir sub idx trace olean remove_entry
  config_dir="$lake_dir/config"
  [[ -d "$config_dir" && ! -L "$config_dir" ]] || return 0
  for sub in "$config_dir"/*; do
    [[ -e "$sub" || -L "$sub" ]] || continue
    [[ ! -L "$sub" && -d "$sub" ]] || fail "non-directory entry in $config_dir: $sub"
    idx="${sub##*/}"
    [[ "$idx" =~ ^[0-9]+$ ]] || continue
    trace="$sub/lakefile.olean.trace"
    olean="$sub/lakefile.olean"
    remove_entry=0
    if [[ -L "$trace" ]] || { [[ -e "$trace" ]] && [[ ! -f "$trace" ]]; }; then
      fail "non-regular trace entry: $trace"
    fi
    if [[ -L "$olean" ]] || { [[ -e "$olean" ]] && [[ ! -f "$olean" ]]; }; then
      fail "non-regular compiled config entry: $olean"
    fi
    if [[ ! -f "$trace" ]]; then
      remove_entry=1
    elif grep -Eq '"name"[[:space:]]*:[[:space:]]*"(\[anonymous\]|acorn)"' "$trace"; then
      remove_entry=1
    fi
    if (( remove_entry == 1 )); then
      rm -f "$olean" "$trace"
    fi
  done
}

sync_config() {
  local root="$1" tracked_tmp stamp
  verify_repo_root "$root"
  admit_one_file "$root" lean/lakefile.lean
  admit_one_file "$root" lean/lake-manifest.json
  admit_one_file "$root" lean/lean-toolchain
  admit_one_file "$root" site/lakefile.toml
  admit_one_file "$root" site/lake-manifest.json
  admit_one_file "$root" site/lean-toolchain
  admit_lake_dirs "$root"
  mkdir -p "$root/lean/.lake"
  stamp="$root/lean/.lake/acorn-tracked-modules.z"
  tracked_tmp=$(mktemp "$root/lean/.lake/acorn-tracked-modules.z.XXXXXX")
  if ! git -C "$root/lean" -c core.quotePath=false ls-files --stage -z -- '*.lean' > "$tracked_tmp" || [[ ! -s "$tracked_tmp" ]]; then
    rm -f "$tracked_tmp"
    fail "failed to enumerate tracked lean/*.lean modules"
  fi
  if [[ ! -f "$stamp" ]] || ! cmp -s "$tracked_tmp" "$stamp"; then
    clean_acorn_config_cache "$root/lean/.lake"
    clean_acorn_config_cache "$root/site/.lake"
    mv -f "$tracked_tmp" "$stamp"
  else
    rm -f "$tracked_tmp"
  fi
}

admit_site_manifests() {
  local root="$1" work status=0
  work=$(mktemp -d "${TMPDIR:-/tmp}/acorn-site-manifests.XXXXXX")
  cat > "$work/check.lean" <<'EOF'
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic

open Lean

def checkManifests (leanPath sitePath tomlPath : System.FilePath) : IO UInt32 := do
  let leanLock ← IO.ofExcept (Json.parse (← IO.FS.readFile leanPath))
  let siteLock ← IO.ofExcept (Json.parse (← IO.FS.readFile sitePath))
  unless (siteLock.getObjValAs? String "version").toOption == some "1.3.0" &&
      (siteLock.getObjValAs? String "packagesDir").toOption == some "../lean/.lake/packages" do
    IO.eprintln "tracked-files: unsupported site/lake-manifest.json layout"
    return 1
  let mut leanGit : Array (String × String × String) := #[]
  for entry in ← IO.ofExcept (leanLock.getObjValAs? (Array Json) "packages") do
    unless (← IO.ofExcept (entry.getObjValAs? String "type")) == "git" do
      IO.eprintln "tracked-files: unsupported non-git entry in lean/lake-manifest.json"
      return 1
    leanGit := leanGit.push (
      ← IO.ofExcept (entry.getObjValAs? String "name"),
      ← IO.ofExcept (entry.getObjValAs? String "url"),
      ← IO.ofExcept (entry.getObjValAs? String "rev"))
  let mut siteGit : Array (String × String × String) := #[]
  let mut sawAcorn := false
  for entry in ← IO.ofExcept (siteLock.getObjValAs? (Array Json) "packages") do
    let ty ← IO.ofExcept (entry.getObjValAs? String "type")
    let name ← IO.ofExcept (entry.getObjValAs? String "name")
    if ty == "git" then
      siteGit := siteGit.push (
        name,
        ← IO.ofExcept (entry.getObjValAs? String "url"),
        ← IO.ofExcept (entry.getObjValAs? String "rev"))
    else if ty == "path" && name == "acorn" && !sawAcorn then
      sawAcorn := true
      unless (entry.getObjValAs? String "dir").toOption == some "../lean" &&
          (entry.getObjValAs? String "configFile").toOption == some "lakefile.lean" &&
          (entry.getObjValAs? String "manifestFile").toOption == some "lake-manifest.json" &&
          (entry.getObjValAs? String "scope").toOption == some "" &&
          (entry.getObjValAs? Bool "inherited").toOption == some false &&
          (entry.getObjValAs? Bool "copy").toOption == some false do
        IO.eprintln "tracked-files: site/lake-manifest.json acorn path entry mismatch"
        return 1
    else
      IO.eprintln s!"tracked-files: unsupported site/lake-manifest.json package entry: {name}"
      return 1
  unless sawAcorn do
    IO.eprintln "tracked-files: site/lake-manifest.json missing acorn path entry"
    return 1
  for dep in leanGit do
    unless siteGit.contains dep do
      IO.eprintln s!"tracked-files: site/lake-manifest.json lock mismatch for {dep.1}"
      return 1
  let toml ← IO.FS.readFile tomlPath
  unless toml.contains "name = \"acorn\"\npath = \"../lean\"" do
    IO.eprintln "tracked-files: site/lakefile.toml must require acorn at ../lean"
    return 1
  return 0

def main (args : List String) : IO UInt32 := do
  let [leanPath, sitePath, tomlPath] := args | return 2
  try checkManifests leanPath sitePath tomlPath catch error =>
    IO.eprintln s!"tracked-files: {error}"
    return 1
EOF
  (cd "$root/site" && lean --run "$work/check.lean" ../lean/lake-manifest.json lake-manifest.json lakefile.toml) || status=$?
  rm -rf "$work"
  return "$status"
}

cmd="${1:-}"
[[ -n "$cmd" ]] || fail "usage: tracked-files.sh (admit-file|admit-lake-dirs|sync-config|admit-site) <root> [paths...]"
shift
root="${1:-}"
[[ -n "$root" ]] || fail "missing repository root argument"
shift

case "$cmd" in
  admit-file)
    (( $# > 0 )) || fail "missing file path(s)"
    verify_repo_root "$root"
    for rel in "$@"; do
      admit_one_file "$root" "$rel"
    done
    ;;
  admit-lake-dirs)
    (( $# == 0 )) || fail "unexpected extra arguments"
    admit_lake_dirs "$root"
    ;;
  sync-config)
    (( $# == 0 )) || fail "unexpected extra arguments"
    sync_config "$root"
    ;;
  admit-site)
    (( $# == 0 )) || fail "unexpected extra arguments"
    verify_repo_root "$root"
    for rel in site/lakefile.toml site/lake-manifest.json site/lean-toolchain site/Main.lean site/AcornSite.lean site/AcornSite/Markdown.lean site/AcornSite/Owners.lean site/AcornSite/Reference.lean site/AcornDocs.lean site/AcornDocs/Verification.lean docs/verification.md; do
      admit_one_file "$root" "$rel"
    done
    admit_lake_dirs "$root"
    admit_site_manifests "$root"
    ;;
  *)
    fail "unknown subcommand: $cmd"
    ;;
esac
