#!/bin/sh
# Static tests of zip's types. Each package under tests/static/accept/ must
# pass `bats check`; each under tests/static/reject/ must fail it exactly as
# its `expect` says (as process's, sha256's, array's and arith's): the
# function, the line of its src/bin/<name>.bats and patsopt's error word for
# word, and no other error. expect.py decides, and compares patsopt's
# variable numbers as "_" (only those: S2EVar(7788), s(1234) of a static
# variable, $1234); expect_test.py tests it and runs first.
# Fixtures depend on this checkout, which is uploaded to a scratch copy
# of the repository first.
#
# Last, every match in src/ and tests/ must be case+.
#
# usage: tests/static/run.sh <repository-dir>   (bats must be on PATH)
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
python3 -B -I "$ROOT/tests/static/expect_test.py"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
cp -R "$1" "$TMP/repo"
(cd "$ROOT" && bats upload --repository "$TMP/repo" >/dev/null)
# Keep only the archive just uploaded, so lock cannot pick a published
# version instead (an uncommitted checkout uploads as <version>dev1,
# which sorts below a release of the same commit).
PKG=$(sed -n 's/^name *= *"\(.*\)"/\1/p' "$ROOT/bats.toml" | head -1)
NEW=$(ls -t "$TMP/repo/$PKG"/*.bats | head -1)
for a in "$TMP/repo/$PKG"/*.bats; do
  [ "$a" = "$NEW" ] || rm -f "$a" "$a.sha256"
done

fail=0
for kind in accept reject; do
  for d in "$ROOT"/tests/static/$kind/*/; do
    [ -f "$d/bats.toml" ] || continue
    n=$(basename "$d"); w="$TMP/w-$kind-$n"
    cp -R "$d" "$w"
    log="$TMP/$kind-$n.log"
    if (cd "$w" && bats lock --dev --repository "$TMP/repo" && bats check --repository "$TMP/repo") > "$log" 2>&1; then
      status=pass
    else
      status=fail
    fi
    if [ "$kind" = accept ] && [ "$status" = pass ]; then
      echo "ok   accept/$n"
    elif [ "$kind" = reject ] && [ "$status" = fail ] \
         && python3 -B -I "$ROOT/tests/static/expect.py" "$d" "$log" > "$TMP/$n.expect" 2>&1; then
      echo "ok   reject/$n"
    elif [ "$kind" = reject ] && [ "$status" = fail ]; then
      echo "FAIL reject/$n: rejected, but not as its expect says: $(cat "$TMP/$n.expect")"; tail -8 "$log"; fail=1
    else
      echo "FAIL $kind/$n ($status)"; tail -8 "$log"; fail=1
    fi
  done
done
# Every match is `case+`: a plain `case` (or `case-`) is not checked
# for exhaustiveness, so a choice could lose a case unseen. Comments,
# strings and inline C (%{ ... %}, whose switch has its own `case`) are
# skipped.
plain_cases=$(python3 - "$ROOT" <<'PY'
import pathlib, re, sys
root = pathlib.Path(sys.argv[1])
for path in sorted(root.glob("src/**/*.bats")) + sorted(root.glob("tests/**/*.bats")):
    text = path.read_text()
    kept, i, depth, line = [], 0, 0, 1
    while i < len(text):
        two = text[i:i + 2]
        if depth == 0 and two == "%{":
            end = text.find("%}", i + 2)
            end = len(text) if end < 0 else end + 2
            kept.append("\n" * text.count("\n", i, end)); i = end; continue
        if two == "(*":
            depth += 1; i += 2; continue
        if depth and two == "*)":
            depth -= 1; i += 2; continue
        if depth:
            kept.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if two == "//":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end; continue
        if text[i] == '"':
            end = i + 1
            while end < len(text) and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            kept.append("\n" * text.count("\n", i, end)); i = end + 1; continue
        kept.append(text[i]); i += 1
    for number, source in enumerate("".join(kept).split("\n"), 1):
        if re.search(r"(?<![\w$])case(?![\w+])", source):
            print(f"{path.relative_to(root)}:{number}: {source.strip()}")
PY
)
if [ -n "$plain_cases" ]; then
  echo "FAIL case+: a match without + is not checked for exhaustiveness:"
  echo "$plain_cases"; fail=1
else echo "ok   every match is case+"; fi
exit $fail
