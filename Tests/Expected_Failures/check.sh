#!/usr/bin/env bash
# Builds the session Expected_Failures and checks that it fails exactly at the
# commands marked (* EXPECTED FAILURE *): every error lies on a marked line, and
# every marked line has an error.
#
# Usage: Tests/Expected_Failures/check.sh ISABELLE [BUILD OPTIONS]
set -u
ISABELLE=${1:?usage: $0 ISABELLE [BUILD OPTIONS]}
shift
DIR=$(cd "$(dirname "$0")" && pwd)
cd "$DIR/../.."

out=$("$ISABELLE" build "$@" -d . -d "$DIR" Expected_Failures 2>&1)
rc=$?
printf '%s\n' "$out"
if [ "$rc" -eq 0 ]; then
  echo "Expected_Failures: the session succeeded, but every theory in it must fail"
  exit 1
fi
if ! printf '%s\n' "$out" | grep -q "^Expected_Failures FAILED"; then
  echo "Expected_Failures: the session did not run"
  exit 1
fi

# Positions as DIRECTORY/FILE:LINE
expected=$(grep -n "(\* EXPECTED FAILURE \*)" "$DIR"/*/*.thy \
  | sed -E 's|^.*/([^/]+/[^/]+\.thy):([0-9]+):.*$|\1:\2|' | sort -u)
actual=$("$ISABELLE" build_log -H Error Expected_Failures \
  | grep -oE 'line [0-9]+ of "[^"]+"' \
  | sed -E 's|^line ([0-9]+) of ".*/([^/]+/[^/"]+)"$|\2:\1|' | sort -u)

if [ "$expected" != "$actual" ]; then
  echo "Expected_Failures: the errors do not match the marked commands"
  echo "Marked commands without an error:"
  comm -23 <(printf '%s\n' "$expected") <(printf '%s\n' "$actual")
  echo "Errors outside of marked commands:"
  comm -13 <(printf '%s\n' "$expected") <(printf '%s\n' "$actual")
  exit 1
fi
echo "Expected_Failures: all $(printf '%s\n' "$expected" | wc -l) marked commands fail, and nothing else does"
