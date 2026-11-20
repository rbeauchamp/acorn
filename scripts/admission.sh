#!/bin/bash
# The admission check of the owner's trusted base. It refuses a change that touches a path
# `.github/CODEOWNERS` names unless an admission of that change is on record outside the change.
#
# The merge gate does not run this file from the tree it checks. It runs the copy held by the
# commit the change starts from (scripts/gate.sh, and the Test command of .no-mistakes.yaml on the
# default branch), so a change that edits this file is checked by the copy it started from. Only
# where that commit holds no copy does scripts/gate.sh run this tree's own, and then this check
# still requires an admission: it never passes for want of a rule.
#
#   ./scripts/admission.sh            check the change at HEAD
#   ./scripts/admission.sh describe   print the owner paths the change touches and the form of
#                                     the record that would admit it, and check nothing
#
# What it reads, each through its owner:
#  - The default branch: the tip of refs/heads/main of the canonical repository below, fetched
#    without writing a ref. Only when that repository cannot be reached does it use
#    refs/remotes/origin/main, and it says so: that copy may be stale or another repository's.
#  - The starting commit: Git's merge base of HEAD and that tip. A shallow repository and
#    unrelated histories are refused.
#  - The owner: the account that owns the canonical repository, the first part of its name
#    below. It is the only code owner this check accepts.
#  - The owner paths: `.github/CODEOWNERS` of the starting commit, in a closed subset of GitHub's
#    syntax: empty lines, lines that start with `#`, and `/path @owner` where the path uses only
#    letters, digits, `.`, `_`, `-` and `/` and the owner is that one account. Any other line is
#    refused, and so are a missing file, a file that names no path and a file of 3,000,000 bytes
#    or more, which GitHub does not load. GitHub skips a line it cannot read and assigns no owner
#    for a login it does not know (GitHub Docs, "About code owners", CODEOWNERS syntax and file
#    size); either would read a protected path as free. A path matches a pattern when it is the
#    pattern's path or lies under it, compared byte for byte: GitHub's paths are case sensitive
#    (the same page), and this is the reading of the gitignore rules that page refers to for a
#    rooted path without wildcards. It is argued from those rules, not observed against GitHub's
#    own evaluation.
#  - The proposed owner paths: `.github/CODEOWNERS` at HEAD must be readable in the same subset
#    and must name this guard's files. Otherwise an admitted change could leave a file that
#    every later run of this check refuses, with no change able to repair it.
#  - The change: Git's own list of the entries that differ between the starting commit and HEAD,
#    with rename detection off, so a file moved out of an owner path counts as deleted there.
#    An uncommitted or untracked file under an owner path is refused: the gate would run it.
#    A change that adds or modifies a path which is no owner path and differs from one only in
#    letter case is refused: on a file system that ignores case, Git writes both to one place,
#    so the unowned file can replace the owned one in a working tree. Ownership itself stays
#    byte for byte.
#  - A pull request, when ACORN_ADMISSION_PULL names one of the canonical repository: its
#    author, head and base, read from GitHub with gh before anything else can pass. Its head
#    must be the commit at HEAD and its base the default branch of the canonical repository.
#  - A record: the commit at refs/admissions/<change> of the canonical repository, where
#    <change> is the SHA-256 of, for each touched owner path, its mode and blob at the starting
#    commit, its mode and blob at HEAD, and its path. So a record admits one transition: it does
#    not admit the reverse change or another change that ends in the same content. Its message
#    is exactly these seven lines, each field one of the values listed and nothing else:
#        acorn-admission 2
#        change <change>
#        form delegation | owner
#        effect keeps-or-tightens | loosens
#        admitted-by the agent supervising the work        (form delegation)
#        admitted-by the owner                             (form owner)
#        delegation the owner's delegation of 2026-11-20   (form delegation)
#        words <a link>                                    (form owner)
#        date <a day of the calendar, YYYY-MM-DD>
#    The link is https://github.com/<canonical>/issues/<n>, or that or .../pull/<n> followed by
#    #issuecomment-<n>: an issue, or a comment on an issue or a pull request.
#    A record of form delegation whose effect is loosens admits nothing. A record admits a run
#    that names no pull request, or a pull request whose author is the owner's account.
#  - A review, for a pull request by any other author: GitHub's list of its reviews. The
#    owner's last APPROVED, CHANGES_REQUESTED or DISMISSED review must be APPROVED on the
#    commit at HEAD. A record does not count for such a pull request. A run that names no pull
#    request cannot know the author and reads a record only.
#
# What a pass establishes: no owner path of the starting commit is touched, or a record or a
# review of the kinds above exists for exactly what the change does to those paths. It does not
# establish that a record's `effect` is true, that whoever admitted the change read it or is
# someone other than its author, or that the owner and not an agent holding the owner's account
# wrote the record: Acorn lists these in its trusted base (docs/verification.md).
# Every failure exits non-zero; callers read only zero or non-zero.
set -euo pipefail
export LC_ALL=C

canonical_slug='rbeauchamp/acorn'
canonical_url="https://github.com/$canonical_slug.git"
owner=${canonical_slug%%/*}
# The closed values of a record's fields.
delegation_role='the agent supervising the work'
owner_role='the owner'
delegation_named="the owner's delegation of 2026-11-20"
issue_form="^https://github\\.com/$canonical_slug/issues/[0-9]+\$"
comment_form="^https://github\\.com/$canonical_slug/(issues|pull)/[0-9]+#issuecomment-[0-9]+\$"
default_branch='main'
local_ref="refs/remotes/origin/$default_branch"
# The files that carry this guard. CODEOWNERS must name each one.
guard_files=(.github/CODEOWNERS .github/workflows/verify.yml .no-mistakes.yaml
  scripts/admission.sh scripts/gate.sh)

say() { printf 'admission: %s\n' "$*"; }
refuse() { say "$*" >&2; exit 1; }

case "$*" in
  '') describe=0 ;;
  describe) describe=1 ;;
  *) echo 'usage: ./scripts/admission.sh [describe]' >&2; exit 2 ;;
esac
cd "$(git rev-parse --show-toplevel)"
work=$(mktemp -d "${TMPDIR:-/tmp}/acorn-admission.XXXXXX")
trap 'rm -rf "$work"' EXIT

# The default branch's tip and the starting commit.
[[ $(git rev-parse --is-shallow-repository) == false ]] ||
  refuse 'this repository is shallow, so the commit the change starts from cannot be determined'
tip=''
if listing=$(git ls-remote "$canonical_url" "refs/heads/$default_branch" 2> /dev/null) &&
    [[ $listing =~ ^([0-9a-f]{40})[[:space:]] ]]; then
  tip=${BASH_REMATCH[1]}
  git fetch --quiet --no-tags --no-write-fetch-head "$canonical_url" \
    "refs/heads/$default_branch" 2> /dev/null || tip=''
fi
if [[ -z $tip ]]; then
  tip=$(git rev-parse --verify --quiet "$local_ref^{commit}") ||
    refuse "could not reach $canonical_url and the checkout holds no $local_ref"
  say "could not reach $canonical_url, so the default branch is read from $local_ref, which \
may be stale or another repository's: this result convinces only whoever ran it"
fi
start=$(git merge-base HEAD "$tip") ||
  refuse "HEAD and the default branch share no commit, so the change has no starting commit"
head=$(git rev-parse --verify 'HEAD^{commit}')
installed=1
git cat-file -e "$start:scripts/admission.sh" 2> /dev/null || installed=0

# A named pull request's identity, before anything can pass: its head is the checked commit and
# its base is the default branch of the canonical repository.
author=''
if [[ -n ${ACORN_ADMISSION_PULL:-} ]]; then
  [[ $ACORN_ADMISSION_PULL =~ ^[0-9]+$ ]] || refuse 'ACORN_ADMISSION_PULL is not a number'
  pull="repos/$canonical_slug/pulls/$ACORN_ADMISSION_PULL"
  gh api "$pull" --jq '[.user.login, .head.sha, .base.ref, .base.repo.full_name] | @tsv' \
    > "$work/pull" 2> "$work/api" ||
    refuse "could not read pull request $ACORN_ADMISSION_PULL: $(tr '\n' ' ' < "$work/api")"
  IFS=$'\t' read -r author pull_head pull_base pull_repository < "$work/pull" ||
    refuse "GitHub's answer for pull request $ACORN_ADMISSION_PULL has no author, head and base"
  [[ -n $author ]] || refuse "pull request $ACORN_ADMISSION_PULL has no author"
  [[ $pull_head == "$head" ]] ||
    refuse "pull request $ACORN_ADMISSION_PULL has head $pull_head, not the checked commit $head"
  [[ $pull_base == "$default_branch" && $pull_repository == "$canonical_slug" ]] ||
    refuse "pull request $ACORN_ADMISSION_PULL targets $pull_base of $pull_repository, not \
$default_branch of $canonical_slug"
fi

# The owner paths a commit's CODEOWNERS names, into `patterns`. The one owner a line may name
# is the owner's account, and the file is smaller than the size GitHub stops loading at.
line_form="^/([A-Za-z0-9._/-]+) +@$owner\$"
read_owner_paths() {
  local commit=$1 whose=$2 entry size line pattern
  entry=$(git ls-tree "$commit" -- .github/CODEOWNERS) ||
    refuse "could not read the tree of $whose"
  [[ $entry == '100644 blob '* ]] || refuse "$whose holds no regular file .github/CODEOWNERS"
  size=$(git cat-file -s "$commit:.github/CODEOWNERS") ||
    refuse "could not read the size of the CODEOWNERS of $whose"
  (( size < 3000000 )) || refuse "the CODEOWNERS of $whose has $size bytes, and GitHub does \
not load one of 3 MB or more"
  git show "$commit:.github/CODEOWNERS" > "$work/codeowners" ||
    refuse "could not read the CODEOWNERS of $whose"
  patterns=()
  while IFS= read -r line || [[ -n $line ]]; do
    [[ -z $line || $line == '#'* ]] && continue
    [[ $line =~ $line_form ]] || refuse "a line of the CODEOWNERS of $whose is outside the \
admitted subset, a rooted path and the one owner @$owner: $line"
    pattern=${BASH_REMATCH[1]}
    patterns+=("$pattern")
    case "/${pattern%/}/" in
      *//* | */./* | */../*)
        refuse "a CODEOWNERS path of $whose has an empty or dot component: $line" ;;
    esac
  done < "$work/codeowners"
  (( ${#patterns[@]} > 0 )) || refuse "the CODEOWNERS of $whose names no path"
}

# Whether a path is an owner path: some pattern matches it. A pattern that ends in `/` matches
# what lies under it; any other matches the path itself and what lies under it. Bytes are
# compared as they are.
owned() {
  local pattern
  for pattern in "${patterns[@]}"; do
    if [[ $pattern == */ ]]; then
      [[ $1 == "$pattern"* ]] && return 0
    else
      [[ $1 == "$pattern" || $1 == "$pattern"/* ]] && return 0
    fi
  done
  return 1
}

# Whether a path that is no owner path would be one if letter case were ignored. On a file
# system that ignores case, such a path is written to the same place as the owner path it
# differs from, so it can replace an owned file in a working tree without being owned.
twin() {
  local pattern found=1
  shopt -s nocasematch
  for pattern in "${patterns[@]}"; do
    if [[ $pattern == */ ]]; then
      if [[ $1 == "$pattern"* ]]; then found=0; fi
    else
      if [[ $1 == "$pattern" || $1 == "$pattern"/* ]]; then found=0; fi
    fi
  done
  shopt -u nocasematch
  return "$found"
}

# The proposed CODEOWNERS first: what the next change will be checked against.
read_owner_paths "$head" "the commit at HEAD"
for file in "${guard_files[@]}"; do
  owned "$file" || refuse "the CODEOWNERS of the commit at HEAD does not name $file, a file of \
this guard"
done

# Then the starting commit's, which decides this change. A starting commit that holds this
# check names the guard's files; one that predates the check is read as it is.
read_owner_paths "$start" "the starting commit $start"
if (( installed )); then
  for file in "${guard_files[@]}"; do
    owned "$file" || refuse "the starting commit's CODEOWNERS does not name $file, a file of \
this guard"
  done
else
  say "the starting commit $start holds no admission check: this change installs it or starts \
before it, and is checked against that commit's CODEOWNERS as it is"
fi

# Uncommitted and untracked files under an owner path.
git diff --no-renames --name-only -z HEAD -- > "$work/uncommitted"
git ls-files --others --exclude-standard -z >> "$work/uncommitted"
while IFS= read -r -d '' path; do
  owned "$path" && refuse "$path is under an owner path and is not committed: the check reads \
the commit at HEAD, and the gate would run this file"
done < "$work/uncommitted"

# The change: every entry that differs between the starting commit and HEAD.
git diff --no-renames --raw -z --no-abbrev "$start" "$head" -- > "$work/change"
touched=()
touched_entries=()
while IFS= read -r -d '' meta && IFS= read -r -d '' path; do
  read -r old_mode mode old_blob blob status <<< "${meta#:}"
  if ! owned "$path"; then
    if [[ $status != D ]] && twin "$path"; then
      refuse "$path differs from an owner path of the starting commit only in letter case: on \
a file system that ignores case it would replace the owned file, so no change may add or modify it"
    fi
    continue
  fi
  touched+=("$path")
  touched_entries+=("$old_mode $old_blob $mode $blob")
done < "$work/change"
if (( ${#touched[@]} == 0 )); then
  say "the change from $start touches no path its CODEOWNERS names"
  exit 0
fi
change=$(for index in "${!touched[@]}"; do
  printf '%s\0%s\0' "${touched_entries[$index]}" "${touched[$index]}"
done | openssl dgst -sha256 -r) || refuse 'openssl could not take the SHA-256 of the change'
change=${change%% *}
[[ $change =~ ^[0-9a-f]{64}$ ]] || refuse "openssl printed no SHA-256: $change"
say "the change from $start touches ${#touched[@]} owner paths:"
for path in "${touched[@]}"; do printf 'admission:   %q\n' "$path"; done
say "change $change"
record_ref="refs/admissions/$change"
if (( describe )); then
  cat <<EOF
admission: a record that admits it is a commit at $record_ref of $canonical_url
admission: whose message is these seven lines (form delegation; the header of this script gives
admission: the values of form owner):
acorn-admission 2
change $change
form delegation
effect keeps-or-tightens
admitted-by $delegation_role
delegation $delegation_named
date $(date -u +%F)
EOF
  exit 0
fi

# Whether a year, a month and a day, each in digits, name a day of the calendar.
calendar_day() {
  local year=$((10#$1)) month=$((10#$2)) day=$((10#$3)) days=31
  (( month >= 1 && month <= 12 && day >= 1 )) || return 1
  case "$month" in
    4 | 6 | 9 | 11) days=30 ;;
    2)
      days=28
      if (( (year % 4 == 0 && year % 100 != 0) || year % 400 == 0 )); then days=29; fi ;;
  esac
  (( day <= days ))
}

# A record outside the change: whether its message is an admission of this change in the closed
# form. Every field is compared with the values this script holds, so free text admits nothing.
record_form() {
  local body=$1 lines=() line link
  while IFS= read -r line; do lines+=("$line"); done <<< "$body"
  (( ${#lines[@]} == 7 )) ||
    { say "the record at $record_ref has ${#lines[@]} lines, not 7"; return 1; }
  [[ ${lines[0]} == 'acorn-admission 2' && ${lines[1]} == "change $change" ]] ||
    { say "the record at $record_ref is not an admission of change $change"; return 1; }
  case "${lines[2]}/${lines[3]}" in
    'form delegation/effect keeps-or-tightens')
      [[ ${lines[4]} == "admitted-by $delegation_role" ]] ||
        { say "a record by delegation is admitted by $delegation_role: ${lines[4]}"; return 1; }
      [[ ${lines[5]} == "delegation $delegation_named" ]] ||
        { say "the record does not name $delegation_named: ${lines[5]}"; return 1; } ;;
    'form delegation/effect loosens')
      say 'the record is by delegation and says the change loosens a protection or removes a'
      say "check: only a record of the owner's own words admits such a change"
      return 1 ;;
    'form owner/effect keeps-or-tightens' | 'form owner/effect loosens')
      [[ ${lines[4]} == "admitted-by $owner_role" ]] ||
        { say "a record of the owner's words is admitted by $owner_role: ${lines[4]}"; return 1; }
      link=${lines[5]#words }
      [[ ${lines[5]} == 'words '* ]] && [[ $link =~ $issue_form || $link =~ $comment_form ]] || {
        say "the record does not say where the owner's words are, as a link to an issue of"
        say "$canonical_slug or to a comment on one of its issues or pull requests: ${lines[5]}"
        return 1
      } ;;
    *)
      say "the record's form and effect are none of this check's: ${lines[2]}, ${lines[3]}"
      return 1 ;;
  esac
  if ! { [[ ${lines[6]} =~ ^date\ ([0-9]{4})-([0-9]{2})-([0-9]{2})$ ]] &&
      calendar_day "${BASH_REMATCH[1]}" "${BASH_REMATCH[2]}" "${BASH_REMATCH[3]}"; }; then
    say "the record's last line is no date of the calendar: ${lines[6]}"
    return 1
  fi
  recorded="${lines[2]}, ${lines[3]}, ${lines[4]}, ${lines[6]}"
}
recorded=''
if listing=$(git ls-remote "$canonical_url" "$record_ref" 2> "$work/remote"); then
  if [[ -n $listing ]]; then
    record=${listing%%[[:space:]]*}
    git fetch --quiet --no-tags --no-write-fetch-head "$canonical_url" "$record_ref" ||
      refuse "could not fetch the record at $record_ref"
    [[ $(git cat-file -t "$record") == commit ]] || refuse "$record_ref is not a commit"
    body=$(git show -s --format=%B "$record") || refuse "could not read the record at $record_ref"
    record_form "$body" || recorded=''
  else
    say "no record at $record_ref of $canonical_url"
  fi
else
  say "could not read $canonical_url, so no record was read: $(tr '\n' ' ' < "$work/remote")"
fi

# Whether two logins are one account. GitHub compares logins without regard to case.
same_account() {
  local same=1
  shopt -s nocasematch
  if [[ $1 == "$2" ]]; then same=0; fi
  shopt -u nocasematch
  return "$same"
}

if [[ -z $author ]]; then
  # No pull request is named, so the author is not known and only a record is read.
  if [[ -n $recorded ]]; then
    say "admitted by the record at $record_ref: $recorded"
    exit 0
  fi
  say 'ACORN_ADMISSION_PULL names no pull request, so no review was read'
elif same_account "$author" "$owner"; then
  # The owner's account cannot review its own pull request: only a record admits it.
  if [[ -n $recorded ]]; then
    say "admitted by the record at $record_ref: $recorded (pull request \
$ACORN_ADMISSION_PULL is by the owner's account)"
    exit 0
  fi
  say "pull request $ACORN_ADMISSION_PULL is by the owner's account, which only a record admits"
else
  # Any other author: only the owner's approving review on the commit at HEAD admits. GitHub
  # lists a pull request's reviews in chronological order (GitHub Docs, REST, "List reviews
  # for a pull request").
  if [[ -n $recorded ]]; then
    say "the record does not count: pull request $ACORN_ADMISSION_PULL is by $author, not by \
the owner's account, so the owner's approving review is required"
  fi
  gh api --paginate "$pull/reviews" --jq '.[] | [.user.login, .state, .commit_id] | @tsv' \
    > "$work/reviews" 2> "$work/api" ||
    refuse "could not read the reviews of pull request $ACORN_ADMISSION_PULL: \
$(tr '\n' ' ' < "$work/api")"
  last=''
  last_commit=''
  while IFS=$'\t' read -r login state commit; do
    same_account "$login" "$owner" || continue
    case "$state" in
      APPROVED | CHANGES_REQUESTED | DISMISSED) last=$state; last_commit=$commit ;;
    esac
  done < "$work/reviews"
  if [[ $last == APPROVED && $last_commit == "$head" ]]; then
    say "admitted by the approving review of @$owner on $head (pull request $ACORN_ADMISSION_PULL)"
    exit 0
  fi
  say "@$owner has no approving review on $head as the last deciding one"
fi
say "REFUSED: the change touches the owner's trusted base and no admission of it is on record."
say 'No edit to the change clears this. It is admitted by a record outside the change'
say "(./scripts/admission.sh describe prints its form) or by the owner's approving review"
say 'on this exact commit (CONTRIBUTING.md, "Changes to the trusted base").'
exit 1
