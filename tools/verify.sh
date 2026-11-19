#!/bin/bash
# The whole verification, to be run before a commit.
#
#     bash tools/verify.sh
#
# Builds the core and then each example, one at a time, each with a time
# limit and a memory limit; then the tests of the type checker, the full
# build, and the recorded results (`lake test`). It prints a line for
# anything that fails, the number of cases each suite ran, and at the end
# ALL-GREEN or NOT-GREEN. It is green only if everything built, every suite
# passed, and no file of the type system, the tests or the examples gave a
# warning. Takes about five minutes.
cd "$(dirname "$0")/.." || exit 1
RUN="python3 tools/run.py"
OUT=$(mktemp -d)
EX=$(ls -d examples/*/ | xargs -n1 basename | tr '\n' ' ')
ok=1
for t in TypedAsm $EX; do
  RUN_CAP_GB=12 $RUN 300 lake build $t > $OUT/b_$t.out 2>&1
  if ! tail -1 $OUT/b_$t.out | grep -q "exit 0"; then
    ok=0; echo "FAILED $t: $(tail -1 $OUT/b_$t.out | cut -c1-60)"
    grep -E "^error" -A10 $OUT/b_$t.out | cut -c1-180 | head -14
  fi
done
RUN_CAP_GB=5 $RUN 300 lake build Tests.Typed.Cross > $OUT/u.out 2>&1
tail -1 $OUT/u.out | grep -q "exit 0" || {
  ok=0; echo "FAILED tests: $(tail -1 $OUT/u.out | cut -c1-60)"
  grep -E "error|warning" -A8 $OUT/u.out | cut -c1-180 | head -14; }
$RUN 300 lake build > $OUT/b.out 2>&1
tail -1 $OUT/b.out | grep -q "exit 0" || { ok=0; echo "FAILED full build: $(tail -1 $OUT/b.out | cut -c1-70)"; }
pat="warning: (core/TypedAsm/U|tests/|examples/)"
W=$(cat $OUT/*.out | grep -cE "$pat")
[ "$W" = "0" ] || { ok=0; echo "WARNINGS: $W"; cat $OUT/*.out | grep -E "$pat" -A4 | cut -c1-160 | head -12; }
$RUN 200 lake test > $OUT/t.out 2>&1
tail -1 $OUT/t.out | grep -q "exit 0" || { ok=0; echo "FAILED suites"; }
grep -E "cases" $OUT/t.out | cut -c1-60 | tr '\n' ' '; echo
[ $ok = 1 ] && echo ALL-GREEN && exit 0
echo "NOT-GREEN (output kept in $OUT)"; exit 1
