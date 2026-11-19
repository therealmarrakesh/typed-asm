#!/bin/bash
# Build the files of the type system one at a time, in the order they
# import one another, and stop at the first that fails.
#
#     bash tools/build-in-order.sh
#
# For use after an edit: the first error is shown, with some lines after it,
# without every file that depends on the edited one being built at once.
# Warnings are shown for each file that gives any. Ends with DONE, or with
# the name of the file that failed. Each build has a time limit and a memory
# limit. CTX sets how many lines are shown after an error (16).
cd "$(dirname "$0")/.." || exit 1
OUT=$(mktemp)
ORDER=$(python3 - <<'PY'
import os, re
d = 'core/TypedAsm/U'
deps = {}
for f in sorted(os.listdir(d)):
    if f.endswith('.lean'):
        m = f[:-5]
        deps[m] = re.findall(r'^import TypedAsm\.U\.(\w+)', open(os.path.join(d, f)).read(), re.M)
done, order = set(), []
def visit(m):
    if m in done or m not in deps: return
    done.add(m)
    for x in deps[m]: visit(x)
    order.append(m)
for m in deps: visit(m)
print(' '.join(order))
PY
)
for m in $ORDER; do
  RUN_CAP_GB=6 python3 tools/run.py 400 lake build TypedAsm.U.$m > $OUT 2>&1
  if ! tail -1 $OUT | grep -q "exit 0"; then
    echo "FAILED $m: $(tail -1 $OUT | cut -c1-40)"
    grep -E "^error" -A${CTX:-16} $OUT | grep -v "^error: build failed\|Some required" | cut -c1-260 | head -70
    rm -f $OUT; exit 1
  fi
  if grep -q "^warning" $OUT; then echo "WARNING in $m"; grep "^warning" -A4 $OUT | cut -c1-190 | head -12; fi
done
rm -f $OUT
echo DONE
