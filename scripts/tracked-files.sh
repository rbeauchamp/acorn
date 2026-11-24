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

verify_repo_root() {
  local root="$1" require_clean="${2:-0}" top prefix_dir real_root real_top tmp line
  [[ -n "$root" && ! -L "$root" && -d "$root" ]] || fail "repository root is not a directory: $root"
  top=$(git --no-optional-locks -C "$root" rev-parse --show-toplevel) || fail "not a git repository: $root"
  prefix_dir=$(git --no-optional-locks -C "$root" rev-parse --show-prefix) || fail "git rev-parse --show-prefix failed: $root"
  [[ -n "$top" && -z "$prefix_dir" ]] || fail "expected repository root, got prefix '$prefix_dir' in $root"
  real_root=$(cd "$root" && pwd -P) || fail "failed to resolve repository root: $root"
  real_top=$(cd "$top" && pwd -P) || fail "failed to resolve git root: $top"
  [[ "$real_root" == "$real_top" ]] || fail "git root mismatch for $root"
  if [[ "$require_clean" == 1 ]]; then
    git --no-optional-locks -C "$root" rev-parse --verify -q HEAD >/dev/null ||
      fail "HEAD commit is unavailable in $root"
    git --no-optional-locks -C "$root" diff-index --cached --quiet --ignore-submodules=none HEAD -- ||
      fail "staged changes differ from HEAD; commit or revert tracked changes before verdict checks"
    git --no-optional-locks -C "$root" -c core.symlinks=true -c core.fsmonitor=false diff --no-ext-diff --no-textconv --quiet --ignore-submodules=none HEAD -- ||
      fail "working-copy tracked files differ from HEAD; commit or revert tracked changes before verdict checks"
    tmp=$(mktemp "${TMPDIR:-/tmp}/acorn-lsfiles-v.XXXXXX")
    cleanup_paths+=("$tmp")
    git --no-optional-locks -C "$root" -c core.quotePath=false ls-files -v -z > "$tmp" ||
      fail "git ls-files -v failed in $root"
    [[ -s "$tmp" ]] || fail "git ls-files -v returned no tracked files in $root"
    while IFS= read -r -d '' line; do
      [[ "$line" == "H "* ]] || fail "tracked entry has non-clean Git index flag: $line"
    done < "$tmp"
    rm -f "$tmp"
  fi
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
  if ! git --no-optional-locks --literal-pathspecs -C "$root" -c core.quotePath=false ls-files --stage -z -- "$rel" > "$tmp"; then
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
  local root="$1" pkg="$2" refuse_overrides="$3"
  local real_root pkg_dir real_pkg lake_dir real_lake config_dir real_config sub real_sub sub_name entry f
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
    config_dir="$lake_dir/config"
    if [[ -L "$config_dir" ]]; then
      fail "refusing symlinked Lake config cache: $pkg/.lake/config"
    fi
    if [[ -e "$config_dir" ]]; then
      [[ -d "$config_dir" ]] || fail "refusing non-directory Lake config cache: $pkg/.lake/config"
      real_config=$(cd "$config_dir" && pwd -P) || fail "failed to resolve $pkg/.lake/config"
      [[ "$real_config" == "$real_lake/config" ]] || fail "$pkg/.lake/config resolves outside workspace: $real_config"
      (
        shopt -s dotglob nullglob
        for sub in "$config_dir"/*; do
          [[ ! -L "$sub" && -d "$sub" ]] || {
            echo "tracked-files: non-directory entry in $pkg/.lake/config: $sub" >&2
            exit 1
          }
          sub_name="${sub##*/}"
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
          for entry in "$sub"/*; do
            if [[ -L "$entry" || ! -f "$entry" ]]; then
              echo "tracked-files: non-regular entry in Lake config cache directory: $entry" >&2
              exit 1
            fi
          done
        done
      ) || exit 1
    fi
  fi
}

admit_lake_dirs() {
  local root="$1" require_clean="$2" for_regula="$3" workspace="$4"
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
  if [[ "$for_regula" == 1 ]]; then
    [[ ! -e "$root/lean/lakefile.toml" && ! -L "$root/lean/lakefile.toml" ]] ||
      fail "unexpected lean/lakefile.toml shadowing lean/lakefile.lean"
  fi
}

validate_tracked_subtree() {
  local base_dir="$1" label="$2" out_lean_stage="${3:-}"
  local tmp line meta path mode oid stage extra seen_dirs=$'\n' cur part i last_idx count=0 lean_count=0
  local -a parts
  tmp=$(mktemp "${TMPDIR:-/tmp}/acorn-subtree.XXXXXX")
  cleanup_paths+=("$tmp")
  git --no-optional-locks -C "$base_dir" -c core.quotePath=false ls-files --stage -z > "$tmp" ||
    fail "git ls-files failed in $label"
  [[ -s "$tmp" ]] || fail "git ls-files returned no tracked entries in $label"
  if [[ -n "$out_lean_stage" ]]; then
    : > "$out_lean_stage"
  fi
  while IFS= read -r -d '' line; do
    count=$((count + 1))
    meta="${line%%$'\t'*}"
    path="${line#*$'\t'}"
    [[ "$meta" != "$line" ]] || fail "malformed git ls-files record in $label"
    IFS=' ' read -r mode oid stage extra <<< "$meta"
    [[ -z "${extra:-}" && "$stage" == "0" && ( "$mode" == "100644" || "$mode" == "100755" ) &&
      "$oid" =~ ^[0-9a-f]{40}([0-9a-f]{24})?$ ]] ||
      fail "unsupported tracked entry mode or stage in $label: $path"
    [[ -n "$path" && "$path" != /* && "$path" != */ && "$path" != *$'\n'* && "$path" != *$'\r'* ]] ||
      fail "unsupported tracked path in $label: $path"
    IFS='/' read -r -a parts <<< "$path"
    cur=''
    last_idx=$(( ${#parts[@]} - 1 ))
    for (( i = 0; i < ${#parts[@]}; i++ )); do
      part="${parts[$i]}"
      [[ -n "$part" && "$part" != "." && "$part" != ".." ]] ||
        fail "unsupported path component in $label/$path"
      if (( i < last_idx )); then
        cur="${cur:+$cur/}$part"
        if [[ "$seen_dirs" != *$'\n'"$cur"$'\n'* ]]; then
          [[ ! -L "$base_dir/$cur" && -d "$base_dir/$cur" ]] ||
            fail "non-directory ancestor in $label: $cur"
          seen_dirs="${seen_dirs}${cur}"$'\n'
        fi
      fi
    done
    [[ ! -L "$base_dir/$path" && -f "$base_dir/$path" ]] ||
      fail "non-regular tracked entry in $label: $path"
    if [[ "$path" == *.lean ]]; then
      lean_count=$((lean_count + 1))
      if [[ -n "$out_lean_stage" ]]; then
        printf '%s\0' "$line" >> "$out_lean_stage"
      fi
    fi
  done < "$tmp"
  rm -f "$tmp"
  (( count > 0 && lean_count > 0 )) || fail "no tracked Lean modules in $label"
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
    shopt -s dotglob nullglob
    for sub in "$config_dir"/*; do
      printf '%s\0' "$sub"
    done
  )
  (( ${#candidates[@]} > 0 )) || return 0
  work=$(mktemp -d "${TMPDIR:-/tmp}/acorn-trace-check.XXXXXX")
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
    return (idx == 0 && traceName == "[anonymous]") || traceName == "acorn"
  else
    return traceName == "acorn"

def main (args : List String) : IO UInt32 := do
  let pkg :: rest := args | return 2
  let mut remaining := rest
  while h : remaining.length >= 2 do
    match remaining with
    | idxStr :: path :: tail =>
      if ← checkPair pkg idxStr path then
        IO.println idxStr
      remaining := tail
    | _ => break
  return 0
EOF
  (cd "$real_root/lean" && lean --run "$work/check_traces.lean" "$pkg" "${candidates[@]}") > "$work/matches.txt" || status=$?
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
  local root="$1" require_clean="$2" for_regula="$3" tracked_tmp stamp
  verify_repo_root "$root" "$require_clean"
  admit_one_file "$root" lean/lakefile.lean
  admit_one_file "$root" lean/lake-manifest.json
  admit_one_file "$root" lean/lean-toolchain
  admit_pkg_lake_containment "$root" lean 1
  if [[ "$for_regula" == 1 ]]; then
    [[ ! -e "$root/lean/lakefile.toml" && ! -L "$root/lean/lakefile.toml" ]] ||
      fail "unexpected lean/lakefile.toml shadowing lean/lakefile.lean"
  fi
  mkdir -p "$root/lean/.lake"
  admit_pkg_lake_containment "$root" lean 1
  stamp="$root/lean/.lake/acorn-tracked-modules.z"
  tracked_tmp=$(mktemp "$root/lean/.lake/acorn-tracked-modules.z.XXXXXX")
  if ! validate_tracked_subtree "$root/lean" "lean" "$tracked_tmp"; then
    rm -f "$tracked_tmp"
    exit 1
  fi
  if [[ ! -f "$stamp" ]] || ! cmp -s "$tracked_tmp" "$stamp"; then
    clean_acorn_config_cache "$root" lean
    if [[ -e "$root/site/.lake" || -L "$root/site/.lake" ]]; then
      admit_pkg_lake_containment "$root" site 0
      clean_acorn_config_cache "$root" site
    fi
    mv -f "$tracked_tmp" "$stamp"
  else
    rm -f "$tracked_tmp"
  fi
}

admit_site_config_and_manifests() {
  local root="$1" site_stage="$2" work prefix lib status=0
  work=$(mktemp -d "${TMPDIR:-/tmp}/acorn-site-admit.XXXXXX")
  work=$(cd "$work" && pwd -P)
  cat > "$work/admit_site.lean" <<'EOF'
import Lake.CLI.Main
import Lake.Load.Toml
import Lake.Load.Manifest
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic

open Lean Lake

def safeComponent (value : String) : Bool :=
  !value.isEmpty && value != "." && value != ".." &&
    value.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.')

def isHex40 (value : String) : Bool :=
  value.length == 40 && value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

def checkRawManifestHeader (path : System.FilePath) (expectedPkgsDir : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  unless (json.getObjValAs? String "version").toOption == some "1.3.0" &&
      (json.getObjValAs? String "packagesDir").toOption == some expectedPkgsDir &&
      (json.getObjValAs? String "lakeDir").toOption == some ".lake" do
    throw (IO.userError s!"unsupported manifest header layout: {path}")

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
    | .git _ rev _ subDir? =>
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

def checkSite (leanManifestPath siteManifestPath trackedLeanStagePath : System.FilePath) : IO Unit := do
  checkRawManifestHeader leanManifestPath ".lake/packages"
  checkRawManifestHeader siteManifestPath "../lean/.lake/packages"
  let leanManifest ← Manifest.load leanManifestPath
  let siteManifest ← Manifest.load siteManifestPath
  let leanPkgs ← checkManifestEntries leanManifest false
  let sitePkgs ← checkManifestEntries siteManifest true
  for (name, leanEntry) in leanPkgs.toList do
    let some siteEntry := sitePkgs[name]?
      | throw (IO.userError s!"site/lake-manifest.json missing shared dependency {name}")
    match leanEntry.src, siteEntry.src with
    | .git lUrl lRev _ lSub, .git sUrl sRev _ sSub =>
      unless lUrl == sUrl && lRev == sRev && lSub == sSub &&
          leanEntry.configFile == siteEntry.configFile &&
          leanEntry.manifestFile? == siteEntry.manifestFile? do
        throw (IO.userError s!"site/lake-manifest.json lock mismatch for {name}")
    | _, _ =>
      throw (IO.userError s!"site/lake-manifest.json source kind mismatch for {name}")

  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let opts : LakeOptions := { elanInstall?, leanInstall?, lakeInstall?, configFile := "lakefile.toml" }
  let cfg ← match ← opts.mkLoadConfig.toBaseIO with
    | .ok cfg => pure cfg
    | .error e => throw (IO.userError (toString e))
  let some tomlCfg ← (loadTomlConfig cfg).toBaseIO { out := .stderr }
    | throw (IO.userError "failed to load site/lakefile.toml via Lake")
  unless tomlCfg.pkgDecl.origName == `acorn_site &&
      tomlCfg.pkgDecl.config.packagesDir == "../lean/.lake/packages" &&
      tomlCfg.pkgDecl.config.srcDir == "." do
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
        unless subDir?.isNone && mSubDir?.isNone && url == mUrl do
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
    unless libCfg.srcDir == "." do
      throw (IO.userError s!"unsupported srcDir in site/lakefile.toml library {decl.name}")
    unless libCfg.roots.isEmpty do
      throw (IO.userError s!"site/lakefile.toml library {decl.name} must set roots = []")
    if libCfg.globs.isEmpty then
      throw (IO.userError s!"site/lakefile.toml library {decl.name} has empty globs")
    libNames := libNames.insert decl.name
    for glob in libCfg.globs do
      match glob with
      | .one mod =>
        if configuredModules.contains mod then
          throw (IO.userError s!"duplicate configured site module {mod}")
        configuredModules := configuredModules.insert mod
      | _ =>
        throw (IO.userError s!"open glob {glob} is forbidden in site/lakefile.toml library {decl.name}")
  for target in tomlCfg.defaultTargets do
    unless libNames.contains target do
      throw (IO.userError s!"unknown defaultTarget in site/lakefile.toml: {target}")
  unless libNames.contains `AcornSite && libNames.contains `AcornDocs do
    throw (IO.userError "site/lakefile.toml missing AcornSite or AcornDocs library")

  let expectedModules := configuredModules.insert `Main
  let stageData ← IO.FS.readFile trackedLeanStagePath
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

def main (args : List String) : IO UInt32 := do
  let [leanPath, sitePath, stagePath] := args | return 2
  try
    checkSite leanPath sitePath stagePath
    return 0
  catch error =>
    IO.eprintln s!"tracked-files: {error}"
    return 1
EOF
  (
    cd "$root/site"
    prefix=$(lean --print-prefix)
    lib="$prefix/lib/lean/libLake_shared.dylib"
    [[ -e "$lib" ]] || lib="$prefix/lib/lean/libLake_shared.so"
    [[ -f "$lib" ]] || {
      echo "tracked-files: missing Lake shared library in Lean sysroot" >&2
      exit 1
    }
    lean --load-dynlib="$lib" --run "$work/admit_site.lean" ../lean/lake-manifest.json lake-manifest.json "$site_stage"
  ) || status=$?
  rm -rf "$work"
  return "$status"
}

admit_site() {
  local root="$1" require_clean="$2" real_root site_stage abs_stage status=0
  sync_config "$root" "$require_clean" 0
  real_root=$(cd "$root" && pwd -P) || fail "failed to resolve repository root: $root"
  admit_pkg_lake_containment "$real_root" site 1
  for rel in site/lakefile.toml site/lake-manifest.json site/lean-toolchain site/Main.lean docs/verification.md; do
    admit_one_file "$real_root" "$rel"
  done
  site_stage=$(mktemp "${TMPDIR:-/tmp}/acorn-site-stage.XXXXXX")
  abs_stage="$(cd "$(dirname "$site_stage")" && pwd -P)/$(basename "$site_stage")"
  if ! validate_tracked_subtree "$real_root/site" "site" "$abs_stage"; then
    rm -f "$abs_stage"
    exit 1
  fi
  admit_site_config_and_manifests "$real_root" "$abs_stage" || status=$?
  rm -f "$abs_stage"
  return "$status"
}

cmd="${1:-}"
[[ -n "$cmd" ]] || fail "usage: tracked-files.sh (admit-file|admit-lake-dirs|sync-config|admit-site) [options] <root> [paths...]"
shift

require_clean=0
for_regula=0
workspace="lean"
while (( $# > 0 )); do
  case "$1" in
    --clean) require_clean=1; shift ;;
    --for-regula) for_regula=1; shift ;;
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
    (( $# > 0 )) || fail "missing file path(s)"
    verify_repo_root "$root" "$require_clean"
    for rel in "$@"; do
      admit_one_file "$root" "$rel"
    done
    ;;
  admit-lake-dirs)
    (( $# == 0 )) || fail "unexpected extra arguments"
    admit_lake_dirs "$root" "$require_clean" "$for_regula" "$workspace"
    ;;
  sync-config)
    (( $# == 0 )) || fail "unexpected extra arguments"
    sync_config "$root" "$require_clean" "$for_regula"
    ;;
  admit-site)
    (( $# == 0 )) || fail "unexpected extra arguments"
    admit_site "$root" "$require_clean"
    ;;
  *)
    fail "unknown subcommand: $cmd"
    ;;
esac
