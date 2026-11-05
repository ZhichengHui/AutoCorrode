#!/usr/bin/env bash
# Builds the session Expected_Failures and checks that it fails exactly as marked.
# A command marked (* EXPECTED FAILURE: TEXT *) must fail with an error message
# starting with TEXT. Every error must belong to a marked command, and every
# marked command must fail.
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

# Marked commands, as DIRECTORY/FILE:LINE <tab> expected start of the error message
expected=$(grep -n "(\* EXPECTED FAILURE: .* \*)" "$DIR"/*/*.thy \
  | sed -E 's|^.*/([^/]+/[^/]+\.thy):([0-9]+):.*\(\* EXPECTED FAILURE: (.*) \*\).*$|\1:\2\t\3|')

# Error messages, as DIRECTORY/FILE:LINE <tab> first line of the message. A message ends with
# the line naming its command; a message without such a line has position "-".
actual=$("$ISABELLE" build_log -H Error Expected_Failures | awk '
  /^\*\*\* / {
    text = substr($0, 5)
    if (head == "") head = text
    if (text ~ /^At command /) {
      pos = text
      sub(/^.*\(line /, "", pos)
      line = pos; sub(/ of .*$/, "", line)
      file = pos; sub(/^[0-9]+ of "/, "", file); sub(/"\)$/, "", file)
      n = split(file, parts, "/")
      printf "%s/%s:%s\t%s\n", parts[n-1], parts[n], line, head
      head = ""
    }
  }
  END { if (head != "") printf "-\t%s\n", head }')

printf '%s\n' "$expected" > "${TMPDIR:-/tmp}/expected_failures.$$"
printf '%s\n' "$actual" | awk -F'\t' -v exp_file="${TMPDIR:-/tmp}/expected_failures.$$" '
  BEGIN { while ((getline l < exp_file) > 0) { split(l, f, "\t"); want[f[1]] = f[2] } }
  $1 == "-" { print "Error without a position: " $2; bad = 1; next }
  !($1 in want) { print "Error at an unmarked command " $1 ": " $2; bad = 1; next }
  index($2, want[$1]) != 1 { print "Error of another kind at " $1 ": " $2; bad = 1; next }
  { seen[$1] = 1 }
  END {
    for (p in want) if (!(p in seen)) { print "Marked command without the expected error: " p; bad = 1 }
    exit bad
  }'
ok=$?
rm -f "${TMPDIR:-/tmp}/expected_failures.$$"
if [ "$ok" -ne 0 ]; then
  echo "Expected_Failures: the errors do not match the marked commands"
  exit 1
fi
echo "Expected_Failures: all $(printf '%s\n' "$expected" | wc -l) marked commands fail as expected, and nothing else fails"
