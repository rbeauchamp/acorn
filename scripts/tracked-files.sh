#!/bin/bash
set -euo pipefail

cleanup_paths=()
# Invoked by the EXIT trap; older ShellCheck does not trace trap callbacks.
# shellcheck disable=SC2317,SC2329
cleanup_temps() {
  local p
  if (( ${#cleanup_paths[@]} > 0 )); then
    for p in "${cleanup_paths[@]}"; do
      [[ -n "$p" ]] && rm -rf "$p"
    done
  fi
}
trap cleanup_temps EXIT

fail() {
  echo "tracked-files: $1" >&2
  exit 1
}

verify_git_dir() {
  local dir="$1" expected_prefix="$2" require_clean="${3:-0}" top prefix_dir expected_path real_dir real_expected tmp line
  [[ -n "$dir" && ! -L "$dir" && -d "$dir" ]] || fail "expected real directory: $dir"
  top=$(git --no-optional-locks -C "$dir" rev-parse --show-toplevel) || fail "not a git repository: $dir"
  prefix_dir=$(git --no-optional-locks -C "$dir" rev-parse --show-prefix) || fail "git rev-parse --show-prefix failed: $dir"
  [[ -n "$top" && "$prefix_dir" == "$expected_prefix" ]] ||
    fail "expected git prefix '$expected_prefix', got '$prefix_dir' in $dir"
  real_dir=$(cd "$dir" && pwd -P) || fail "failed to resolve directory: $dir"
  if [[ -z "$expected_prefix" ]]; then
    expected_path="$top"
  else
    expected_path="$top/${expected_prefix%/}"
  fi
  real_expected=$(cd "$expected_path" && pwd -P) || fail "failed to resolve expected git path: $expected_path"
  [[ "$real_dir" == "$real_expected" ]] || fail "git root mismatch for $dir"
  if [[ "$require_clean" == 1 ]]; then
    git --no-optional-locks -C "$top" rev-parse --verify -q HEAD >/dev/null ||
      fail "HEAD commit is unavailable in $top"
    git --no-optional-locks -C "$top" diff-index --cached --quiet --ignore-submodules=none HEAD -- ||
      fail "staged changes differ from HEAD; commit or revert tracked changes before verdict checks"
    git --no-optional-locks -C "$top" -c core.symlinks=true -c core.fsmonitor=false diff --no-ext-diff --no-textconv --quiet --ignore-submodules=none HEAD -- ||
      fail "working-copy tracked files differ from HEAD; commit or revert tracked changes before verdict checks"
    tmp=$(mktemp "${TMPDIR:-/tmp}/acorn-lsfiles-v.XXXXXX")
    cleanup_paths+=("$tmp")
    git --no-optional-locks -C "$top" -c core.quotePath=false ls-files -v -z > "$tmp" ||
      fail "git ls-files -v failed in $top"
    [[ -s "$tmp" ]] || fail "git ls-files -v returned no tracked files in $top"
    while IFS= read -r -d '' line; do
      [[ "$line" == "H "* ]] || fail "tracked entry has non-clean Git index flag: $line"
    done < "$tmp"
    rm -f "$tmp"
  fi
}

verify_repo_root() {
  verify_git_dir "$1" "" "${2:-0}"
}

check_rel_path() {
  local rel="$1"
  [[ -n "$rel" ]] || fail "empty tracked path"
  [[ "$rel" != /* && "$rel" != */ ]] || fail "unsupported leading/trailing slash in $rel"
  [[ "$rel" != :* && "$rel" != -* ]] || fail "unsupported path prefix in $rel"
  [[ "$rel" != *$'\n'* && "$rel" != *$'\r'* ]] || fail "newline in tracked path"
}

validate_stage_meta() {
  local meta="$1" label="$2" path="$3" mode oid stage extra
  IFS=' ' read -r mode oid stage extra <<< "$meta"
  [[ -z "${extra:-}" && "$stage" == "0" && ( "$mode" == "100644" || "$mode" == "100755" ) &&
    "$oid" =~ ^[0-9a-f]{40}([0-9a-f]{24})?$ ]] ||
    fail "unsupported tracked entry mode or stage in $label: $path"
}

validate_rel_entry() {
  local base_dir="$1" path="$2" label="$3" rest="$2" part cur=''
  [[ -n "$path" && "$path" != /* && "$path" != */ && "$path" != *$'\n'* && "$path" != *$'\r'* ]] ||
    fail "unsupported tracked path in $label: $path"
  while [[ "$rest" == */* ]]; do
    part="${rest%%/*}"
    rest="${rest#*/}"
    [[ -n "$part" && "$part" != "." && "$part" != ".." ]] ||
      fail "unsupported path component in $label/$path"
    cur="${cur:+$cur/}$part"
    case "$seen_dirs" in
      *$'\n'"$cur"$'\n'*) ;;
      *)
        [[ ! -L "$base_dir/$cur" && -d "$base_dir/$cur" ]] ||
          fail "non-directory ancestor in $label: $cur"
        seen_dirs="${seen_dirs}${cur}"$'\n'
        ;;
    esac
  done
  [[ -n "$rest" && "$rest" != "." && "$rest" != ".." ]] ||
    fail "unsupported path component in $label/$path"
  [[ ! -L "$base_dir/$path" && -f "$base_dir/$path" ]] ||
    fail "non-regular tracked entry in $label: $path"
}

admit_one_file() {
  local root="$1" rel="$2" tmp rec line meta path count=0 seen_dirs=$'\n'
  check_rel_path "$rel"
  validate_rel_entry "$root" "$rel" "repo"

  tmp=$(mktemp "${TMPDIR:-/tmp}/acorn-lsfiles.XXXXXX")
  cleanup_paths+=("$tmp")
  git --no-optional-locks --literal-pathspecs -C "$root" -c core.quotePath=false ls-files --stage -z -- "$rel" > "$tmp" ||
    fail "git ls-files failed for $rel"
  rec=''
  while IFS= read -r -d '' line; do
    rec="$line"
    count=$((count + 1))
  done < "$tmp"
  rm -f "$tmp"
  (( count == 1 )) || fail "path is not uniquely tracked: $rel"

  meta="${rec%%$'\t'*}"
  path="${rec#*$'\t'}"
  [[ "$meta" != "$rec" && "$path" == "$rel" ]] || fail "malformed git ls-files record for $rel"
  validate_stage_meta "$meta" "repo" "$rel"
}

admit_tracked_dir_prefix() {
  local root="$1" rel="$2" tmp line meta path rest="$2" part cur='' count=0 lean_count=0
  check_rel_path "$rel"
  while [[ "$rest" == */* ]]; do
    part="${rest%%/*}"
    rest="${rest#*/}"
    [[ -n "$part" && "$part" != "." && "$part" != ".." ]] ||
      fail "unsupported path component in repo/$rel"
    cur="${cur:+$cur/}$part"
    [[ ! -L "$root/$cur" && -d "$root/$cur" ]] ||
      fail "non-directory ancestor in repo: $cur"
  done
  [[ -n "$rest" && "$rest" != "." && "$rest" != ".." ]] ||
    fail "unsupported path component in repo/$rel"
  [[ ! -L "$root/$rel" && -d "$root/$rel" ]] ||
    fail "non-directory tracked prefix in repo: $rel"
  tmp=$(mktemp "${TMPDIR:-/tmp}/acorn-lsfiles-dir.XXXXXX")
  cleanup_paths+=("$tmp")
  git --no-optional-locks --literal-pathspecs -C "$root" -c core.quotePath=false ls-files --stage -z -- "$rel" > "$tmp" ||
    fail "git ls-files failed for $rel"
  while IFS= read -r -d '' line; do
    count=$((count + 1))
    meta="${line%%$'\t'*}"
    path="${line#*$'\t'}"
    [[ "$meta" != "$line" && "$path" == "$rel/"* ]] || fail "malformed git ls-files record for $rel"
    validate_stage_meta "$meta" "repo" "$path"
    if [[ "$path" == *.lean ]]; then
      lean_count=$((lean_count + 1))
    fi
  done < "$tmp"
  rm -f "$tmp"
  (( count > 0 && lean_count > 0 )) || fail "tracked directory prefix has no tracked Lean files: $rel"
}

admit_pkg_lake_containment() {
  local root="$1" pkg="$2" refuse_overrides="$3" check_packages="${4:-1}"
  local real_root pkg_dir real_pkg lake_dir real_lake pkgs_dir real_pkgs config_dir real_config sub real_sub sub_name f
  real_root=$(cd "$root" && pwd -P) || fail "failed to resolve repository root: $root"
  pkg_dir="$root/$pkg"
  [[ ! -L "$pkg_dir" && -d "$pkg_dir" ]] || fail "$pkg is not a real directory"
  real_pkg=$(cd "$pkg_dir" && pwd -P) || fail "failed to resolve $pkg directory"
  [[ "$real_pkg" == "$real_root/$pkg" ]] || fail "$pkg resolves outside workspace: $real_pkg"
  lake_dir="$pkg_dir/.lake"
  if [[ -L "$lake_dir" ]]; then
    fail "refusing symlinked .lake directory: $pkg/.lake"
  fi
  if [[ -e "$lake_dir" ]]; then
    [[ -d "$lake_dir" ]] || fail "refusing non-directory .lake path: $pkg/.lake"
    real_lake=$(cd "$lake_dir" && pwd -P) || fail "failed to resolve $pkg/.lake"
    [[ "$real_lake" == "$real_pkg/.lake" ]] || fail "$pkg/.lake resolves outside workspace: $real_lake"
    if [[ "$refuse_overrides" == 1 ]] && { [[ -e "$lake_dir/package-overrides.json" || -L "$lake_dir/package-overrides.json" ]]; }; then
      fail "unbound $pkg/.lake/package-overrides.json; remove the ambient override"
    fi
    for f in "$lake_dir/acorn-path-packages.json" "$lake_dir/acorn-tracked-modules.z"; do
      if [[ -L "$f" ]] || { [[ -e "$f" ]] && [[ ! -f "$f" ]]; }; then
        fail "non-regular cache file: $f"
      fi
    done
    if [[ "$check_packages" == 1 ]]; then
      pkgs_dir="$lake_dir/packages"
      if [[ -L "$pkgs_dir" ]]; then
        fail "refusing symlinked packages directory: $pkg/.lake/packages"
      fi
      if [[ -e "$pkgs_dir" ]]; then
        [[ -d "$pkgs_dir" ]] || fail "refusing non-directory packages path: $pkg/.lake/packages"
        real_pkgs=$(cd "$pkgs_dir" && pwd -P) || fail "failed to resolve $pkg/.lake/packages"
        [[ "$real_pkgs" == "$real_lake/packages" ]] || fail "$pkg/.lake/packages resolves outside workspace: $real_pkgs"
      fi
    fi
    config_dir="$lake_dir/config"
    if [[ -L "$config_dir" ]]; then
      fail "refusing symlinked Lake config cache: $pkg/.lake/config"
    fi
    if [[ -e "$config_dir" ]]; then
      [[ -d "$config_dir" ]] || fail "refusing non-directory Lake config cache: $pkg/.lake/config"
      real_config=$(cd "$config_dir" && pwd -P) || fail "failed to resolve $pkg/.lake/config"
      [[ "$real_config" == "$real_lake/config" ]] || fail "$pkg/.lake/config resolves outside workspace: $real_config"
      (
        shopt -s nullglob
        for sub in "$config_dir"/*; do
          sub_name="${sub##*/}"
          [[ "$sub_name" =~ ^[0-9]+$ ]] || continue
          [[ ! -L "$sub" && -d "$sub" ]] || {
            echo "tracked-files: non-directory package cache entry in $pkg/.lake/config: $sub" >&2
            exit 1
          }
          real_sub=$(cd "$sub" && pwd -P) || exit 1
          [[ "$real_sub" == "$real_config/$sub_name" ]] || {
            echo "tracked-files: Lake config entry resolves outside workspace: $sub" >&2
            exit 1
          }
          for f in "$sub/lakefile.olean" "$sub/lakefile.olean.trace" "$sub/lakefile.olean.lock"; do
            if [[ -L "$f" ]] || { [[ -e "$f" ]] && [[ ! -f "$f" ]]; }; then
              echo "tracked-files: non-regular Lake config cache destination: $f" >&2
              exit 1
            fi
          done
        done
      ) || exit 1
    fi
  fi
}

admit_lake_dirs() {
  local root="$1" require_clean="$2" workspace="$3"
  verify_repo_root "$root" "$require_clean"
  case "$workspace" in
    lean)
      admit_pkg_lake_containment "$root" lean 1 ;;
    site)
      admit_pkg_lake_containment "$root" site 1 ;;
    both)
      admit_pkg_lake_containment "$root" lean 1
      admit_pkg_lake_containment "$root" site 1 ;;
    *)
      fail "unsupported workspace selector: $workspace" ;;
  esac
}

validate_tracked_subtree() {
  local base_dir="$1" label="$2" out_lean_stage="${3:-}" require_lean="${4:-1}" emit_paths="${5:-0}"
  local tmp out_paths='' line meta path seen_dirs=$'\n' count=0 lean_count=0
  tmp=$(mktemp "${TMPDIR:-/tmp}/acorn-subtree.XXXXXX")
  cleanup_paths+=("$tmp")
  git --no-optional-locks -C "$base_dir" -c core.quotePath=false ls-files --stage -z > "$tmp" ||
    fail "git ls-files failed in $label"
  [[ -s "$tmp" ]] || fail "git ls-files returned no tracked entries in $label"
  if [[ -n "$out_lean_stage" ]]; then
    : > "$out_lean_stage"
  fi
  if [[ "$emit_paths" == 1 ]]; then
    out_paths=$(mktemp "${TMPDIR:-/tmp}/acorn-paths.XXXXXX")
    cleanup_paths+=("$out_paths")
  fi
  while IFS= read -r -d '' line; do
    count=$((count + 1))
    meta="${line%%$'\t'*}"
    path="${line#*$'\t'}"
    [[ "$meta" != "$line" ]] || fail "malformed git ls-files record in $label"
    validate_stage_meta "$meta" "$label" "$path"
    validate_rel_entry "$base_dir" "$path" "$label"
    if [[ "$path" == *.lean ]]; then
      lean_count=$((lean_count + 1))
      if [[ -n "$out_lean_stage" ]]; then
        printf '%s\0' "$line" >> "$out_lean_stage"
      fi
    fi
    if [[ "$emit_paths" == 1 ]]; then
      printf '%s\0' "$path" >> "$out_paths"
    fi
  done < "$tmp"
  rm -f "$tmp"
  (( count > 0 )) || fail "no tracked entries in $label"
  if [[ "$require_lean" == 1 ]]; then
    (( lean_count > 0 )) || fail "no tracked Lean modules in $label"
  fi
  if [[ "$emit_paths" == 1 ]]; then
    cat "$out_paths"
    rm -f "$out_paths"
  fi
}

clean_acorn_config_cache() {
  local root="$1" pkg="$2" real_root config_dir sub idx trace olean work status=0 line
  local -a candidates
  real_root=$(cd "$root" && pwd -P) || fail "failed to resolve repository root: $root"
  config_dir="$real_root/$pkg/.lake/config"
  [[ -d "$config_dir" && ! -L "$config_dir" ]] || return 0
  candidates=()
  while IFS= read -r -d '' sub; do
    idx="${sub##*/}"
    [[ "$idx" =~ ^[0-9]+$ ]] || continue
    trace="$sub/lakefile.olean.trace"
    [[ -f "$trace" && ! -L "$trace" ]] || continue
    candidates+=("$idx" "$trace")
  done < <(
    shopt -s nullglob
    for sub in "$config_dir"/*; do
      printf '%s\0' "$sub"
    done
  )
  (( ${#candidates[@]} > 0 )) || return 0
  work=$(mktemp -d "${TMPDIR:-/tmp}/acorn-trace-check.XXXXXX")
  cleanup_paths+=("$work")
  work=$(cd "$work" && pwd -P)
  cat > "$work/check_traces.lean" <<'EOF'
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic

open Lean

def checkPair (pkg : String) (idxStr : String) (tracePath : System.FilePath) : IO Bool := do
  let some idx := idxStr.toNat? | return false
  let content ← try IO.FS.readFile tracePath catch _ => return false
  let .ok json := Json.parse content | return false
  let some traceIdx := (json.getObjValAs? Nat "idx").toOption | return false
  let some traceName := (json.getObjValAs? String "name").toOption | return false
  if traceIdx != idx then return false
  if pkg == "lean" then
    return idx == 0 && (traceName == "[anonymous]" || traceName == "acorn")
  else
    return idx > 0 && traceName == "acorn"

def checkAll (pkg : String) : List String → IO Unit
  | idxStr :: path :: tail => do
    if ← checkPair pkg idxStr path then
      IO.println idxStr
    checkAll pkg tail
  | _ => pure ()

def main (args : List String) : IO UInt32 := do
  let pkg :: rest := args | return 2
  checkAll pkg rest
  return 0
EOF
  (cd "$real_root/lean" && lean -DwarningAsError=true -DautoImplicit=false --run "$work/check_traces.lean" "$pkg" "${candidates[@]}") > "$work/matches.txt" || status=$?
  if [[ "$status" == 0 ]]; then
    while IFS= read -r line; do
      [[ "$line" =~ ^[0-9]+$ ]] || continue
      olean="$config_dir/$line/lakefile.olean"
      trace="$config_dir/$line/lakefile.olean.trace"
      rm -f "$olean" "$trace"
    done < "$work/matches.txt"
  fi
  rm -rf "$work"
  return "$status"
}

sync_config() {
  local root="$1" require_clean="$2" for_regula="$3" admit_manifest="${4:-0}" real_root tracked_tmp stamp
  verify_repo_root "$root" "$require_clean"
  real_root=$(cd "$root" && pwd -P) || fail "failed to resolve repository root: $root"
  admit_one_file "$real_root" lean/lakefile.lean
  admit_one_file "$real_root" lean/lake-manifest.json
  admit_one_file "$real_root" lean/lean-toolchain
  admit_pkg_lake_containment "$real_root" lean 1 1
  if [[ "$for_regula" == 1 ]]; then
    [[ ! -e "$real_root/lean/lakefile.toml" && ! -L "$real_root/lean/lakefile.toml" ]] ||
      fail "unexpected lean/lakefile.toml shadowing lean/lakefile.lean"
  fi
  mkdir -p "$real_root/lean/.lake"
  admit_pkg_lake_containment "$real_root" lean 1 1
  stamp="$real_root/lean/.lake/acorn-tracked-modules.z"
  tracked_tmp=$(mktemp "$real_root/lean/.lake/acorn-tracked-modules.z.XXXXXX")
  cleanup_paths+=("$tracked_tmp")
  validate_tracked_subtree "$real_root/lean" "lean" "$tracked_tmp" 1 0
  if [[ ! -f "$stamp" ]] || ! cmp -s "$tracked_tmp" "$stamp"; then
    clean_acorn_config_cache "$real_root" lean
    if [[ -e "$real_root/site/.lake" || -L "$real_root/site/.lake" ]]; then
      admit_pkg_lake_containment "$real_root" site 0 0
      clean_acorn_config_cache "$real_root" site
    fi
    mv -f "$tracked_tmp" "$stamp"
  else
    rm -f "$tracked_tmp"
  fi
  if [[ "$admit_manifest" == 1 ]]; then
    admit_manifests_and_site "$real_root" lean
  fi
}

admit_manifests_and_site() {
  local root="$1" mode="$2" site_stage="${3:-}" overrides_out="${4:-}" work prefix lib status=0 run_dir
  work=$(mktemp -d "${TMPDIR:-/tmp}/acorn-manifest-admit.XXXXXX")
  cleanup_paths+=("$work")
  work=$(cd "$work" && pwd -P)
  cat > "$work/admit_manifest.lean" <<'EOF'
import Lake.CLI.Main
import Lake.Load.Toml
import Lake.Load.Manifest

open Lean Lake

def safeComponent (value : String) : Bool :=
  !value.isEmpty && value != "." && value != ".." &&
    value.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.')

def isHex40 (value : String) : Bool :=
  value.length == 40 && value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

def symlinkMetadata? (path : System.FilePath) : IO (Option IO.FS.Metadata) :=
  try some <$> path.symlinkMetadata catch error =>
    if error matches .noFileOrDirectory .. then pure none else throw error

def checkManifestEntries (manifest : Manifest) (allowAcornPath : Bool) :
    IO (Std.HashMap Name PackageEntry) := do
  if manifest.packages.isEmpty then
    throw (IO.userError "empty manifest package inventory")
  let mut byName : Std.HashMap Name PackageEntry := {}
  let mut seenDirs : Std.HashSet String := {}
  let mut sawAcorn := false
  for entry in manifest.packages do
    if byName.contains entry.name then
      throw (IO.userError s!"duplicate manifest package name: {entry.name}")
    let dirName := entry.dirName
    if !safeComponent dirName || seenDirs.contains dirName then
      throw (IO.userError s!"duplicate or unsafe manifest package directory: {dirName}")
    byName := byName.insert entry.name entry
    seenDirs := seenDirs.insert dirName
    let cfgStr := entry.configFile.toString
    let some manPath := entry.manifestFile?
      | throw (IO.userError s!"missing manifestFile for {entry.name}")
    let manStr := manPath.toString
    unless safeComponent cfgStr && safeComponent manStr do
      throw (IO.userError s!"unsafe configFile or manifestFile for {entry.name}")
    match entry.src with
    | .git url rev _ subDir? =>
      unless !url.isEmpty do
        throw (IO.userError s!"empty git URL for {entry.name}")
      unless isHex40 rev do
        throw (IO.userError s!"invalid git revision for {entry.name}")
      unless subDir?.isNone do
        throw (IO.userError s!"unsupported subDir for git dependency {entry.name}")
    | .path dir copy =>
      unless allowAcornPath && entry.name == `acorn && !sawAcorn &&
          dir == "../lean" && !copy &&
          cfgStr == "lakefile.lean" && manStr == "lake-manifest.json" &&
          entry.scope == "" && !entry.inherited do
        throw (IO.userError s!"unsupported path package entry: {entry.name}")
      sawAcorn := true
  if allowAcornPath && !sawAcorn then
    throw (IO.userError "site/lake-manifest.json missing acorn path entry")
  return byName

def checkDepCheckouts (lakeDir pkgsRoot : System.FilePath) (manifest : Manifest)
    (requireProvisioned : Bool) : IO Unit := do
  match ← symlinkMetadata? pkgsRoot with
  | none =>
    if requireProvisioned then
      throw (IO.userError s!"missing pinned documentation dependencies ({pkgsRoot}); see docs/verification.md#platform-setup")
    return
  | some m =>
    unless m.type == .dir do
      throw (IO.userError s!"non-directory packages path: {pkgsRoot}")
    let realLake ← IO.FS.realPath lakeDir
    let realPkgs ← IO.FS.realPath pkgsRoot
    unless realPkgs == realLake / "packages" do
      throw (IO.userError s!"packages directory resolves outside workspace: {pkgsRoot}")
    for entry in manifest.packages do
      match entry.src with
      | .path .. => pure ()
      | .git .. =>
        let dirName := entry.dirName
        let depDir := pkgsRoot / dirName
        match ← symlinkMetadata? depDir with
        | none =>
          if requireProvisioned then
            throw (IO.userError s!"missing pinned documentation dependencies ({entry.name}); see docs/verification.md#platform-setup")
        | some dm =>
          unless dm.type == .dir do
            throw (IO.userError s!"non-directory package checkout: {depDir}")
          let realDep ← IO.FS.realPath depDir
          unless realDep == realPkgs / dirName do
            throw (IO.userError s!"package checkout resolves outside workspace: {depDir}")
          if let some gm ← symlinkMetadata? (depDir / ".git") then
            unless gm.type == .dir || gm.type == .file do
              throw (IO.userError s!"non-regular .git in package checkout: {depDir}")
          let cfgPath := depDir / entry.configFile
          match ← symlinkMetadata? cfgPath with
          | none =>
            if requireProvisioned then
              throw (IO.userError s!"missing pinned documentation dependencies ({entry.name}); see docs/verification.md#platform-setup")
          | some cm =>
            unless cm.type == .file do
              throw (IO.userError s!"non-regular package configFile: {cfgPath}")
          if let some mf := entry.manifestFile? then
            if let some mm ← symlinkMetadata? (depDir / mf) then
              unless mm.type == .file do
                throw (IO.userError s!"non-regular package manifestFile: {depDir / mf}")

def checkLeanManifest (leanManifestPath lakeDir pkgsRoot : System.FilePath) : IO (Std.HashMap Name PackageEntry) := do
  let leanManifest ← Manifest.load leanManifestPath
  unless leanManifest.name == `acorn &&
      leanManifest.packagesDir? == some ".lake/packages" &&
      leanManifest.lakeDir == ".lake" do
    throw (IO.userError "unsupported parsed lean/lake-manifest.json header")
  let leanPkgs ← checkManifestEntries leanManifest false
  checkDepCheckouts lakeDir pkgsRoot leanManifest false
  return leanPkgs

def checkSite (leanManifestPath siteManifestPath leanLakeDir pkgsRoot trackedStagePath : System.FilePath)
    (overridesOut? : Option System.FilePath) : IO Unit := do
  let leanPkgs ← checkLeanManifest leanManifestPath leanLakeDir pkgsRoot
  let siteManifest ← Manifest.load siteManifestPath
  unless siteManifest.name == `acorn_site &&
      siteManifest.packagesDir? == some "../lean/.lake/packages" &&
      siteManifest.lakeDir == ".lake" do
    throw (IO.userError "unsupported parsed site/lake-manifest.json header")
  let sitePkgs ← checkManifestEntries siteManifest true
  for (name, leanEntry) in leanPkgs.toList do
    let some siteEntry := sitePkgs[name]?
      | throw (IO.userError s!"site/lake-manifest.json missing shared dependency {name}")
    match leanEntry.src, siteEntry.src with
    | .git lUrl lRev _ lSub, .git sUrl sRev _ sSub =>
      unless lUrl == sUrl && lRev == sRev && lSub == sSub &&
          leanEntry.scope == siteEntry.scope &&
          leanEntry.configFile == siteEntry.configFile &&
          leanEntry.manifestFile? == siteEntry.manifestFile? do
        throw (IO.userError s!"site/lake-manifest.json lock mismatch for {name}")
    | _, _ =>
      throw (IO.userError s!"site/lake-manifest.json source kind mismatch for {name}")
  checkDepCheckouts leanLakeDir pkgsRoot siteManifest overridesOut?.isSome

  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let opts : LakeOptions := { elanInstall?, leanInstall?, lakeInstall?, configFile := "lakefile.toml" }
  let cfg ← match ← opts.mkLoadConfig.toBaseIO with
    | .ok cfg => pure cfg
    | .error e => throw (IO.userError (toString e))
  let some tomlCfg ← (loadTomlConfig cfg).toBaseIO { out := .stderr }
    | throw (IO.userError "failed to load site/lakefile.toml via Lake")
  unless tomlCfg.pkgDecl.origName == `acorn_site &&
      tomlCfg.pkgDecl.config.packagesDir == "../lean/.lake/packages" &&
      tomlCfg.pkgDecl.config.srcDir == "." &&
      tomlCfg.pkgDecl.config.buildDir == defaultBuildDir &&
      tomlCfg.pkgDecl.config.leanLibDir == defaultLeanLibDir &&
      tomlCfg.pkgDecl.config.extraDepTargets.isEmpty &&
      tomlCfg.pkgDecl.config.testDriver.isEmpty &&
      tomlCfg.pkgDecl.config.lintDriver.isEmpty &&
      tomlCfg.scripts.isEmpty &&
      tomlCfg.postUpdateHooks.isEmpty do
    throw (IO.userError "unsupported site/lakefile.toml package configuration")

  let mut seenReq : Std.HashSet Name := {}
  let mut sawAcornReq := false
  for dep in tomlCfg.depConfigs do
    if seenReq.contains dep.name then
      throw (IO.userError s!"duplicate require in site/lakefile.toml: {dep.name}")
    seenReq := seenReq.insert dep.name
    let some manifestEntry := sitePkgs[dep.name]?
      | throw (IO.userError s!"site/lakefile.toml require missing from site/lake-manifest.json: {dep.name}")
    if dep.name == `acorn then
      match dep.src? with
      | some (.path dir copy) =>
        unless dir == "../lean" && !copy && dep.scope == "" do
          throw (IO.userError "site/lakefile.toml acorn require must point to ../lean without copy")
        sawAcornReq := true
      | _ => throw (IO.userError "site/lakefile.toml acorn require must be a path dependency")
    else
      match dep.src?, manifestEntry.src with
      | some (.git url rev? subDir?), .git mUrl mRev mInputRev? mSubDir? =>
        unless dep.scope == manifestEntry.scope &&
            subDir?.isNone && mSubDir?.isNone && url == mUrl do
          throw (IO.userError s!"site/lakefile.toml git require mismatch for {dep.name}")
        if let some r := rev? then
          unless r == mRev || some r == mInputRev? do
            throw (IO.userError s!"site/lakefile.toml revision mismatch for {dep.name}")
      | _, _ => throw (IO.userError s!"unsupported require in site/lakefile.toml: {dep.name}")
  unless sawAcornReq do
    throw (IO.userError "site/lakefile.toml missing acorn path require")

  let mut libNames : Std.HashSet Name := {}
  let mut configuredModules : Std.HashSet Name := {}
  for decl in tomlCfg.targetDecls do
    let some libCfg := decl.config? LeanLib.configKind
      | throw (IO.userError s!"unsupported non-library target in site/lakefile.toml: {decl.name}")
    unless libCfg.srcDir == "." && libCfg.extraDepTargets.isEmpty && libCfg.needs.isEmpty do
      throw (IO.userError s!"unsupported library configuration in site/lakefile.toml: {decl.name}")
    unless libCfg.roots.isEmpty do
      throw (IO.userError s!"site/lakefile.toml library {decl.name} must set roots = []")
    if libCfg.globs.isEmpty then
      throw (IO.userError s!"site/lakefile.toml library {decl.name} has empty globs")
    libNames := libNames.insert decl.name
    for glob in libCfg.globs do
      match glob with
      | .one mod =>
        if mod == `Main || configuredModules.contains mod then
          throw (IO.userError s!"duplicate or reserved configured site module {mod}")
        configuredModules := configuredModules.insert mod
      | _ =>
        throw (IO.userError s!"open glob {glob} is forbidden in site/lakefile.toml library {decl.name}")
  for target in tomlCfg.defaultTargets do
    unless libNames.contains target do
      throw (IO.userError s!"unknown defaultTarget in site/lakefile.toml: {target}")
  unless libNames.contains `AcornSite && libNames.contains `AcornDocs do
    throw (IO.userError "site/lakefile.toml missing AcornSite or AcornDocs library")

  let expectedModules := configuredModules.insert `Main
  let stageData ← IO.FS.readFile trackedStagePath
  let records := (stageData.splitOn (String.singleton (Char.ofNat 0))).filter (!·.isEmpty)
  let mut trackedModules : Std.HashSet Name := {}
  for rec in records do
    let [_, path] := rec.splitOn "\t"
      | throw (IO.userError s!"malformed tracked stage record: {rec}")
    let parts := path.splitOn "/"
    if parts.head?.any (fun h => h == ".lake" || h == "_out" || h == ".DS_Store") then continue
    let stem := ((System.FilePath.mk (parts.getLastD "")).withExtension "").toString
    let modParts := parts.dropLast ++ [stem]
    if modParts.any (·.isEmpty) then
      throw (IO.userError s!"empty site module component in {path}")
    let mod := modParts.foldl Name.str .anonymous
    trackedModules := trackedModules.insert mod
  for mod in expectedModules do
    unless trackedModules.contains mod do
      throw (IO.userError s!"configured site module is not a tracked regular file: {mod}")
  for mod in trackedModules do
    unless expectedModules.contains mod do
      throw (IO.userError s!"tracked site module is not configured in site/lakefile.toml: {mod}")

  if let some outPath := overridesOut? then
    let mut overrideEntries : Array PackageEntry := #[]
    for entry in siteManifest.packages do
      match entry.src with
      | .git .. =>
        overrideEntries := overrideEntries.push
          { entry with src := .path s!"../lean/.lake/packages/{entry.dirName}" false }
      | .path .. => pure ()
    if overrideEntries.isEmpty then
      throw (IO.userError "incomplete documentation manifest package inventory")
    let payload := Json.mkObj [
      ("version", toJson Manifest.version),
      ("packages", toJson overrideEntries)
    ]
    IO.FS.writeFile outPath (payload.compress ++ "\n")

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["lean", leanManifestPath, lakeDir, pkgsRoot] =>
      discard (checkLeanManifest leanManifestPath lakeDir pkgsRoot)
    | ["site", leanManifestPath, siteManifestPath, leanLakeDir, pkgsRoot, stagePath] =>
      checkSite leanManifestPath siteManifestPath leanLakeDir pkgsRoot stagePath none
    | ["site-overrides", leanManifestPath, siteManifestPath, leanLakeDir, pkgsRoot, stagePath, outPath] =>
      checkSite leanManifestPath siteManifestPath leanLakeDir pkgsRoot stagePath (some outPath)
    | _ => return 2
    return 0
  catch error =>
    IO.eprintln s!"tracked-files: {error}"
    return 1
EOF
  if [[ "$mode" == lean ]]; then
    run_dir="$root/lean"
  else
    run_dir="$root/site"
  fi
  (
    cd "$run_dir"
    prefix=$(lean --print-prefix)
    lib="$prefix/lib/lean/libLake_shared.dylib"
    [[ -e "$lib" ]] || lib="$prefix/lib/lean/libLake_shared.so"
    [[ -f "$lib" ]] || {
      echo "tracked-files: missing Lake shared library in Lean sysroot" >&2
      exit 1
    }
    if [[ "$mode" == lean ]]; then
      lean -DwarningAsError=true -DautoImplicit=false --load-dynlib="$lib" --run "$work/admit_manifest.lean" \
        lean lake-manifest.json .lake .lake/packages
    elif [[ "$mode" == site ]]; then
      lean -DwarningAsError=true -DautoImplicit=false --load-dynlib="$lib" --run "$work/admit_manifest.lean" \
        site ../lean/lake-manifest.json lake-manifest.json ../lean/.lake ../lean/.lake/packages "$site_stage"
    else
      lean -DwarningAsError=true -DautoImplicit=false --load-dynlib="$lib" --run "$work/admit_manifest.lean" \
        site-overrides ../lean/lake-manifest.json lake-manifest.json ../lean/.lake ../lean/.lake/packages "$site_stage" "$overrides_out"
    fi
  ) || status=$?
  rm -rf "$work"
  return "$status"
}

admit_site() {
  local root="$1" require_clean="$2" emit_overrides="${3:-0}" real_root site_stage abs_stage overrides_tmp abs_out='' mode='site' status=0
  sync_config "$root" "$require_clean" 0 0
  real_root=$(cd "$root" && pwd -P) || fail "failed to resolve repository root: $root"
  admit_pkg_lake_containment "$real_root" site 1 1
  for rel in site/lakefile.toml site/lake-manifest.json site/lean-toolchain site/Main.lean docs/verification.md; do
    admit_one_file "$real_root" "$rel"
  done
  site_stage=$(mktemp "${TMPDIR:-/tmp}/acorn-site-stage.XXXXXX")
  cleanup_paths+=("$site_stage")
  abs_stage="$(cd "$(dirname "$site_stage")" && pwd -P)/$(basename "$site_stage")"
  validate_tracked_subtree "$real_root/site" "site" "$abs_stage" 1 0
  if [[ "$emit_overrides" == 1 ]]; then
    mode='site-overrides'
    overrides_tmp=$(mktemp "${TMPDIR:-/tmp}/acorn-site-overrides.XXXXXX")
    cleanup_paths+=("$overrides_tmp")
    abs_out="$(cd "$(dirname "$overrides_tmp")" && pwd -P)/$(basename "$overrides_tmp")"
  fi
  admit_manifests_and_site "$real_root" "$mode" "$abs_stage" "$abs_out" || status=$?
  rm -f "$abs_stage"
  if [[ "$status" == 0 && "$emit_overrides" == 1 ]]; then
    cat "$abs_out"
  fi
  if [[ -n "$abs_out" ]]; then
    rm -f "$abs_out"
  fi
  return "$status"
}

admit_no_comments() {
  local root="$1" require_clean="$2" real_root work out_file status=0 ratchet_count=0 line kind value dir
  verify_repo_root "$root" "$require_clean"
  real_root=$(cd "$root" && pwd -P) || fail "failed to resolve repository root: $root"
  admit_one_file "$real_root" .no-comments.json
  admit_one_file "$real_root" lean/no-comments.pin
  admit_site "$real_root" "$require_clean" 0
  work=$(mktemp -d "${TMPDIR:-/tmp}/acorn-nc-admit.XXXXXX")
  cleanup_paths+=("$work")
  work=$(cd "$work" && pwd -P)
  out_file="$work/nc-paths.txt"
  cat > "$work/check_nc.lean" <<'EOF'
import Lean.Data.Json

open Lean

def hasControlOrSlashIssue (s : String) : Bool :=
  s.any fun c => c == '\n' || c == '\r' || c == '\t' || c == '\x00' || c == '\\'

def stripLeadingDotSlashChars : List Char → List Char
  | '.' :: '/' :: rest => stripLeadingDotSlashChars rest
  | cs => cs

def stripLeadingDotSlash (s : String) : String :=
  String.ofList (stripLeadingDotSlashChars s.toList)

def stripTrailingSlashRev : List Char → List Char
  | '/' :: rest@(_ :: _) => stripTrailingSlashRev rest
  | cs => cs

def stripTrailingSlashes (s : String) : String :=
  String.ofList (stripTrailingSlashRev s.toList.reverse).reverse

def validateSegments (context raw : String) (segs : List String) : Except String Unit := do
  for seg in segs do
    if seg == "" || seg == "." || seg == ".." then
      throw s!"{context} '{raw}' contains invalid path segment '{seg}'"

def normalizeRelDir (context raw : String) : Except String String := do
  if raw == "" then throw s!"{context} must not be empty"
  if hasControlOrSlashIssue raw || raw.startsWith "/" then
    throw s!"{context} '{raw}' must be a clean repo-relative directory path"
  let cleaned := stripTrailingSlashes (stripLeadingDotSlash raw)
  if cleaned == "." || cleaned == "" then return "."
  validateSegments context raw (cleaned.splitOn "/")
  return cleaned

def normalizeRelFile (context raw : String) : Except String String := do
  if raw == "" then throw s!"{context} must not be empty"
  if hasControlOrSlashIssue raw || raw.startsWith "/" || raw.endsWith "/" then
    throw s!"{context} '{raw}' must be a clean relative file path"
  let cleaned := stripLeadingDotSlash raw
  if cleaned == "" || cleaned == "." then throw s!"{context} '{raw}' must name a file"
  validateSegments context raw (cleaned.splitOn "/")
  return cleaned

def normalizePrefix (context raw : String) : Except String String := do
  if raw == "" then throw s!"{context} must not be empty"
  if hasControlOrSlashIssue raw || raw.startsWith "/" then
    throw s!"{context} '{raw}' must be a clean relative prefix"
  let cleaned := stripLeadingDotSlash raw
  if cleaned == "" || cleaned == "." || cleaned == "./" then
    throw s!"{context} '{raw}' must not match the entire root"
  let trailingSlash := cleaned.endsWith "/"
  let body := if trailingSlash then (cleaned.dropEnd 1).toString else cleaned
  if body == "" then throw s!"{context} '{raw}' must not be empty"
  validateSegments context raw (body.splitOn "/")
  return if trailingSlash then body ++ "/" else body

def checkAllowedKeys (context : String) (obj : Std.TreeMap.Raw String Json compare)
    (allowed : Array String) : Except String Unit := do
  for (k, _) in obj.toList do
    unless allowed.contains k do
      throw s!"unknown key '{k}' in {context}"

def getRequiredField (context : String) (obj : Std.TreeMap.Raw String Json compare)
    (key : String) : Except String Json :=
  match obj.get? key with
  | some v => .ok v
  | none => .error s!"missing required field '{key}' in {context}"

def parseStringArray (context : String) (j : Json) : Except String (Array String) := do
  let arr ← j.getArr?
  arr.mapM fun item => do
    let s ← item.getStr?
    if hasControlOrSlashIssue s then
      throw s!"invalid control character in {context} entry"
    return s

def checkLakeArgs (wsDir : String) (expectedCfg : String) (lakeArgs : Array String) :
    Except String Unit := do
  let mut i : Nat := 0
  let mut sawCfg := false
  let mut sawOffline := false
  let mut sawNoCache := false
  while h : i < lakeArgs.size do
    let arg := lakeArgs[i]
    if arg == "-f" || arg == "--file" then
      let nextIdx := i + 1
      if hNext : nextIdx < lakeArgs.size then
        let cfgVal := lakeArgs[nextIdx]
        if sawCfg || cfgVal != expectedCfg then
          throw s!"{wsDir}.lakeArgs must pin only '{expectedCfg}', got '{cfgVal}'"
        sawCfg := true
        i := nextIdx + 1
      else
        throw s!"missing value after '{arg}' in {wsDir}.lakeArgs"
    else if arg.startsWith "--file=" then
      let cfgVal := (arg.drop 7).toString
      if sawCfg || cfgVal != expectedCfg then
        throw s!"{wsDir}.lakeArgs must pin only '{expectedCfg}', got '{cfgVal}'"
      sawCfg := true
      i := i + 1
    else if arg == "--offline" then
      sawOffline := true
      i := i + 1
    else if arg == "--no-cache" then
      sawNoCache := true
      i := i + 1
    else if #["--wfail", "--iofail", "-q", "--quiet", "-v", "--verbose",
        "--old", "--rehash", "-R", "--reconfigure"].contains arg then
      i := i + 1
    else
      throw s!"disallowed Lake argument '{arg}' in {wsDir}.lakeArgs"
  unless sawCfg && sawOffline && sawNoCache do
    throw s!"{wsDir}.lakeArgs must specify -f {expectedCfg}, --offline, and --no-cache"

def validateConfig (text : String) : Except String (String × Array String) := do
  let json ← Json.parse text
  let obj ← json.getObj?
  checkAllowedKeys "config" obj #["workspaces", "exclude", "ratchet"]
  let wsArr ← (← getRequiredField "config" obj "workspaces").getArr?
  let mut seenLean := false
  let mut seenSite := false
  for h : idx in [:wsArr.size] do
    let ctx := s!"workspaces[{idx}]"
    let wsObj ← wsArr[idx].getObj?
    checkAllowedKeys ctx wsObj #["dir", "srcDir", "lakeArgs", "toolPrefixes", "excludePrefixes"]
    let dir ← normalizeRelDir s!"{ctx}.dir" (← (← getRequiredField ctx wsObj "dir").getStr?)
    let srcDir ← match wsObj.get? "srcDir" with
      | some v => normalizeRelDir s!"{ctx}.srcDir" (← v.getStr?)
      | none => pure "."
    unless srcDir == "." do
      throw s!"{ctx}.srcDir must be '.', got '{srcDir}'"
    if let some v := wsObj.get? "toolPrefixes" then
      let arr ← parseStringArray s!"{ctx}.toolPrefixes" v
      unless arr.isEmpty do
        throw s!"{ctx}.toolPrefixes must be empty"
    if let some v := wsObj.get? "excludePrefixes" then
      let arr ← parseStringArray s!"{ctx}.excludePrefixes" v
      unless arr.isEmpty do
        throw s!"{ctx}.excludePrefixes must be empty"
    let lakeArgs ← match wsObj.get? "lakeArgs" with
      | some v => parseStringArray s!"{ctx}.lakeArgs" v
      | none => pure #[]
    if dir == "lean" then
      if seenLean then throw "duplicate workspace 'lean'"
      seenLean := true
      checkLakeArgs "lean" "lakefile.lean" lakeArgs
    else if dir == "site" then
      if seenSite then throw "duplicate workspace 'site'"
      seenSite := true
      checkLakeArgs "site" "lakefile.toml" lakeArgs
    else
      throw s!"unadmitted workspace dir '{dir}' in .no-comments.json"
  unless seenLean && seenSite do
    throw ".no-comments.json must configure both 'lean' and 'site' workspaces"
  let mut excludes : Array String := #[]
  if let some v := obj.get? "exclude" then
    let arr ← v.getArr?
    for h : idx in [:arr.size] do
      let ctx := s!"exclude[{idx}]"
      let eObj ← arr[idx].getObj?
      checkAllowedKeys ctx eObj #["prefix", "reason"]
      let pfx ← normalizePrefix s!"{ctx}.prefix" (← (← getRequiredField ctx eObj "prefix").getStr?)
      let reason := (← (← getRequiredField ctx eObj "reason").getStr?).trimAscii.toString
      if reason.isEmpty then throw s!"{ctx}.reason must not be empty"
      unless pfx == "site/AcornDocs.lean" || pfx == "site/AcornDocs/" ||
          pfx.startsWith "site/AcornDocs/" do
        throw s!"unadmitted exclude prefix '{pfx}' outside Verso documentation scope"
      excludes := excludes.push pfx
  let ratchet ← normalizeRelFile "config.ratchet"
    (← (← getRequiredField "config" obj "ratchet").getStr?)
  return (ratchet, excludes)

def main (args : List String) : IO UInt32 := do
  let [cfgPath, outPath] := args | return 2
  try
    let text ← IO.FS.readFile cfgPath
    let (ratchet, excludes) ← IO.ofExcept (validateConfig text)
    let mut lines := s!"RATCHET\t{ratchet}\n"
    for pfx in excludes do
      lines := lines ++ s!"EXCLUDE\t{pfx}\n"
    IO.FS.writeFile outPath lines
    return 0
  catch error =>
    IO.eprintln s!"tracked-files: {error}"
    return 1
EOF
  (cd "$real_root/lean" && lean -DwarningAsError=true -DautoImplicit=false --run "$work/check_nc.lean" "$real_root/.no-comments.json" "$out_file") || status=$?
  if [[ "$status" != 0 ]]; then
    rm -rf "$work"
    return "$status"
  fi
  while IFS= read -r line; do
    [[ -n "$line" ]] || continue
    kind="${line%%$'\t'*}"
    value="${line#*$'\t'}"
    case "$kind" in
      RATCHET)
        ratchet_count=$((ratchet_count + 1))
        admit_one_file "$real_root" "$value" ;;
      EXCLUDE)
        if [[ "$value" == */ ]]; then
          dir="${value%/}"
          admit_tracked_dir_prefix "$real_root" "$dir"
        else
          admit_one_file "$real_root" "$value"
        fi ;;
      *)
        rm -rf "$work"
        fail "malformed no-comments validation output: $line" ;;
    esac
  done < "$out_file"
  rm -rf "$work"
  (( ratchet_count == 1 )) || fail "missing ratchet path from .no-comments.json"
}

cmd="${1:-}"
[[ -n "$cmd" ]] || fail "usage: tracked-files.sh (admit-file|list-tracked|admit-lake-dirs|sync-config|admit-site|admit-no-comments) [options] <root> [paths...]"
shift

require_clean=0
for_regula=0
admit_manifest=0
emit_overrides=0
require_lean=0
has_prefix=0
expected_prefix=''
workspace=''
while (( $# > 0 )); do
  case "$1" in
    --clean) require_clean=1; shift ;;
    --for-regula) for_regula=1; shift ;;
    --admit-manifest) admit_manifest=1; shift ;;
    --emit-overrides) emit_overrides=1; shift ;;
    --require-lean) require_lean=1; shift ;;
    --prefix)
      (( $# >= 2 )) || fail "--prefix requires an argument"
      has_prefix=1
      expected_prefix="$2"
      shift 2 ;;
    --workspace)
      (( $# >= 2 )) || fail "--workspace requires an argument"
      workspace="$2"
      shift 2 ;;
    *) break ;;
  esac
done

root="${1:-}"
[[ -n "$root" ]] || fail "missing repository root argument"
shift

case "$cmd" in
  admit-file)
    (( for_regula == 0 && admit_manifest == 0 && emit_overrides == 0 && require_lean == 0 && has_prefix == 0 )) && [[ -z "$workspace" ]] ||
      fail "unsupported option for admit-file"
    (( $# > 0 )) || fail "missing file path(s)"
    verify_repo_root "$root" "$require_clean"
    for rel in "$@"; do
      admit_one_file "$root" "$rel"
    done
    ;;
  list-tracked)
    (( for_regula == 0 && admit_manifest == 0 && emit_overrides == 0 && has_prefix == 1 )) && [[ -z "$workspace" ]] ||
      fail "list-tracked requires --prefix and rejects --for-regula/--admit-manifest/--emit-overrides/--workspace"
    (( $# == 0 )) || fail "unexpected extra arguments"
    verify_git_dir "$root" "$expected_prefix" "$require_clean"
    validate_tracked_subtree "$root" "${expected_prefix:-repo}" "" "$require_lean" 1
    ;;
  admit-lake-dirs)
    (( for_regula == 0 && admit_manifest == 0 && emit_overrides == 0 && require_lean == 0 && has_prefix == 0 )) && [[ -n "$workspace" ]] ||
      fail "admit-lake-dirs requires --workspace and rejects unsupported options"
    (( $# == 0 )) || fail "unexpected extra arguments"
    admit_lake_dirs "$root" "$require_clean" "$workspace"
    ;;
  sync-config)
    (( emit_overrides == 0 && require_lean == 0 && has_prefix == 0 )) && [[ -z "$workspace" ]] ||
      fail "unsupported option for sync-config"
    (( $# == 0 )) || fail "unexpected extra arguments"
    sync_config "$root" "$require_clean" "$for_regula" "$admit_manifest"
    ;;
  admit-site)
    (( for_regula == 0 && admit_manifest == 0 && require_lean == 0 && has_prefix == 0 )) && [[ -z "$workspace" ]] ||
      fail "unsupported option for admit-site"
    (( $# == 0 )) || fail "unexpected extra arguments"
    admit_site "$root" "$require_clean" "$emit_overrides"
    ;;
  admit-no-comments)
    (( for_regula == 0 && admit_manifest == 0 && emit_overrides == 0 && require_lean == 0 && has_prefix == 0 )) && [[ -z "$workspace" ]] ||
      fail "unsupported option for admit-no-comments"
    (( $# == 0 )) || fail "unexpected extra arguments"
    admit_no_comments "$root" "$require_clean"
    ;;
  *)
    fail "unknown subcommand: $cmd"
    ;;
esac
