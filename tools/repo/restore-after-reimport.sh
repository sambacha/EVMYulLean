#!/usr/bin/env bash
# Restore the repository after a re-import that replaced `.gitignore` and committed generated files.
#
#   tools/repo/restore-after-reimport.sh [REPO_DIR]
#
# 1. Appends to REPO_DIR/.gitignore every pattern of tools/repo/generated-paths.gitignore that is
#    not already one of its lines (existing lines are kept, in order).
# 2. Stops tracking (git rm --cached) every tracked file that the resulting ignore rules match.
#    Files stay on disk.
# 3. Deletes every zero-byte `*.lean` file that git does not ignore. A re-import turns each file that
#    was moved or deleted since the previous export into an empty file at its old path; such a stub
#    is a second, empty module of the old name (it builds, so nothing else notices it). No
#    hand-written Lean file of this repository is empty: parent files carry a docstring (L3).
# 4. Sets the executable bit on every file git does not ignore that starts with `#!` and lacks it.
#    The fourth re-import also cleared the mode of all 13 scripts (K28); in this repository a file
#    is executable exactly when it starts with `#!`.
#    Nothing is committed.
#
# Idempotent: a second run changes nothing. Exit status 0 on success, 1 on a usage or git error.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
list="$here/generated-paths.gitignore"
repo="${1:-$here/../..}"
[ -r "$list" ] || { echo "restore: cannot read $list" >&2; exit 1; }
cd "$repo"
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || {
  echo "restore: $repo is not a git work tree" >&2; exit 1; }
touch .gitignore
added=0
while IFS= read -r pat || [ -n "$pat" ]; do
  case "$pat" in ''|'#'*) continue ;; esac
  if ! grep -qxF -- "$pat" .gitignore; then
    if [ "$added" -eq 0 ]; then
      # make sure the appended block starts on its own line
      if [ -s .gitignore ] && [ -n "$(tail -c1 .gitignore)" ]; then echo >> .gitignore; fi
      echo "# generated or fetched paths (tools/repo/generated-paths.gitignore)" >> .gitignore
    fi
    echo "$pat" >> .gitignore
    added=$((added + 1))
  fi
done < "$list"
files=()
while IFS= read -r -d '' f; do
  files+=("$f")
done < <(git ls-files -z --cached --ignored --exclude-standard)
untracked=${#files[@]}
if [ "$untracked" -gt 0 ]; then git rm -r --cached --quiet -- "${files[@]}"; fi
stubs=0
while IFS= read -r -d '' f; do
  if [ -f "$f" ] && [ ! -s "$f" ]; then rm -f -- "$f"; stubs=$((stubs + 1)); fi
done < <(git ls-files -z --cached --others --exclude-standard -- '*.lean')
modes=0
while IFS= read -r -d '' f; do
  if [ -f "$f" ] && [ ! -x "$f" ] && [ "$(head -c2 -- "$f" | tr -d '\000')" = '#!' ]; then
    chmod +x -- "$f"; modes=$((modes + 1))
  fi
done < <(git ls-files -z --cached --others --exclude-standard)
echo "restore: $added pattern(s) added to .gitignore, $untracked file(s) no longer tracked, \
$stubs empty .lean stub(s) deleted, $modes executable bit(s) restored"
