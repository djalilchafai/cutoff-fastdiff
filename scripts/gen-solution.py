#!/usr/bin/env python3
"""Generate Solution.lean from Challenge.lean: each advertised theorem `T` is proved by the
development lemma `T'` with the identical statement.  Use `--check` in CI."""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
text = (root / "Challenge.lean").read_text(encoding="utf-8")
blocks = re.split(r"\n\n+", text)
out = ['''module

public import Cutfast

@[expose] public section

/-!
# Proved solution

This module imports the full proof development. Comparator checks that each declaration below
has exactly the same statement as its counterpart in `Challenge.lean` (the definitions are
those of `Cutfast.Defs`, generated verbatim from the Challenge) and uses only the permitted
axioms.
-/

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

-- The generated proofs `apply T'; all_goals assumption` may leave nothing for `assumption`.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Cutfast''']
for block in blocks:
    body = re.sub(r"^(open .* in\n)?/--.*?-/\n", "", block, flags=re.S)
    if body.startswith("theorem "):
        name = body.split()[1]
        assert body.rstrip().endswith(":= by\n  sorry"), name
        out.append(block.rstrip()[: -len("sorry")] + f"apply {name}'\n  all_goals assumption")
out.append("end Cutfast\n")
result = "\n\n".join(out)
target = root / "Solution.lean"
if "--check" in sys.argv:
    if target.read_text(encoding="utf-8") != result:
        print("Solution.lean is out of sync with Challenge.lean")
        sys.exit(1)
else:
    target.write_text(result, encoding="utf-8")
