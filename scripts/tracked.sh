#!/bin/bash
# What the checkout tracks where the gate trusts what it finds, checked before the first Lake
# call of the gate (scripts/gate.sh) and of verification (scripts/verify.sh). Git's index is the
# authority: a commit carries tracked files only.
#
# 1. Lake's build directories and the site's output directory track nothing. Lake trusts an
#    output whose trace matches, and the renderer writes through what the output directory
#    holds, so a tracked file there could hand the gate a compiled module, a tool, a compiled
#    configuration or a link that no run made.
# 2. The site tracks only its Lean sources, its Lake configuration, its two lock files and its
#    ignore file. Verso's renderer reads a remote configuration from the site's directory when
#    one is present (verso-sources.json); none is tracked. The ownership inventory then holds
#    the Lean sources to the registered site modules.
# 3. No tracked path differs only by letter case from a path at or under an owner path, a path
#    .github/CODEOWNERS names. On a file system that ignores case, such a path is the same file
#    or directory as the owner's while Git and CODEOWNERS take it for another: a change could
#    add Lake's configuration under another spelling, or replace an owner's file at checkout.
#    For the owner paths themselves the guard on owner paths refuses the same from the commit a
#    change starts from, where the gate has that guard; this check is the one that covers the
#    build directories. CODEOWNERS is read in the closed form the boundary audit reads
#    (lean/AcornTools/Boundary/Audit.lean): an empty line, a line that starts with `#`, or
#    `/path @owner`; any other line fails.
set -euo pipefail
cd "$(dirname "$0")/.."

refuse() { printf 'tracked paths: %s\n' "$1" >&2; exit 1; }

for directory in lean/.lake site/.lake site/_out; do
  tracked=$(git ls-files -- ":(icase)$directory")
  [[ -z "$tracked" ]] || refuse "the checkout tracks files under $directory, which only a run writes:
$tracked"
done

site=$(git ls-files -- ':(icase)site')
while IFS= read -r path; do
  [[ -z "$path" ]] && continue
  [[ "$path" =~ ^site/(\.gitignore|lakefile\.toml|lake-manifest\.json|lean-toolchain|[A-Za-z0-9_/]+\.lean)$ ]] ||
    refuse "the site tracks $path, which is none of its Lean sources, its Lake configuration, its lock files and its ignore file"
done <<< "$site"

owners=0
while IFS= read -r line || [[ -n "$line" ]]; do
  case "$line" in
    '' | '#'*) continue ;;
  esac
  [[ "$line" =~ ^/([A-Za-z0-9._/-]+)\ @[A-Za-z0-9-]+$ ]] ||
    refuse ".github/CODEOWNERS holds a line that is not '/path @owner': $line"
  path=${BASH_REMATCH[1]}
  owners=$((owners + 1))
  exact=$(git ls-files -- "$path")
  folded=$(git ls-files -- ":(icase)$path")
  [[ "$exact" == "$folded" ]] ||
    refuse "a tracked path differs only by letter case from the owner path /$path:
$(comm -13 <(printf '%s\n' "$exact" | LC_ALL=C sort) <(printf '%s\n' "$folded" | LC_ALL=C sort))"
done < .github/CODEOWNERS
(( owners > 0 )) || refuse '.github/CODEOWNERS names no path'
