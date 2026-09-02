#!/usr/bin/env python3
"""Validate the reading-layer axiom report.

Fails when the declaration set differs from the frozen list, a name repeats, the
split between axiom-carrying and axiom-free declarations is not the one the paper
states, or any declaration reports axioms outside {propext, Quot.sound}.

★A count alone is not enough: swapping one declaration for another keeps the count
at 104 while changing what was audited, so the names are frozen as a set in
`tools/reading_layer_names.txt` and compared in both directions.  The two that
report no axioms are pinned by name for the same reason.
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NAMES_FILE = ROOT / "tools" / "reading_layer_names.txt"
AXIOM_FREE_NAMES = {"BishopCheng.ComplementedSet", "BishopCheng.boolPts"}

EXPECTED = 104
# ★The paper states the split, so the checker must pin it: a 100/4 run would
# otherwise pass while the paper still claimed 102/2.
EXPECTED_WITH_AXIOMS = 102
EXPECTED_AXIOM_FREE = 2
ALLOWED = "[propext, Quot.sound]"

def main(path):
    lines = [l.rstrip("\n") for l in open(path, encoding="utf-8") if l.startswith("'")]
    names, bad = [], []
    for l in lines:
        m = re.match(r"^'([^']+)' (depends on axioms: (.*)|does not depend on any axioms)$", l)
        if not m:
            bad.append(("unparsed", l)); continue
        names.append(m.group(1))
        if m.group(3) is not None and m.group(3).strip() != ALLOWED:
            bad.append(("axioms", l))
    dup = {n for n in names if names.count(n) > 1}
    ok = True
    print(f"reading_layer_declarations={len(names)} expected={EXPECTED}")
    if len(names) != EXPECTED:
        print(f"FAIL: declaration count {len(names)} != {EXPECTED}", file=sys.stderr); ok = False
    if dup:
        print(f"FAIL: duplicate names {sorted(dup)}", file=sys.stderr); ok = False
    with_ax = sum(1 for l in lines if "depends on axioms:" in l)
    no_ax = sum(1 for l in lines if "does not depend on any axioms" in l)
    print(f"reading_layer_with_axioms={with_ax} expected={EXPECTED_WITH_AXIOMS}")
    print(f"reading_layer_axiom_free={no_ax} expected={EXPECTED_AXIOM_FREE}")
    if with_ax != EXPECTED_WITH_AXIOMS or no_ax != EXPECTED_AXIOM_FREE:
        print(f"FAIL: split {with_ax}/{no_ax} != "
              f"{EXPECTED_WITH_AXIOMS}/{EXPECTED_AXIOM_FREE}", file=sys.stderr); ok = False
    if NAMES_FILE.exists():
        frozen = {x.strip() for x in NAMES_FILE.read_text(encoding="utf-8").splitlines() if x.strip()}
        got = set(names)
        missing, extra = sorted(frozen - got), sorted(got - frozen)
        print(f"reading_layer_frozen_names={len(frozen)} missing={len(missing)} extra={len(extra)}")
        if missing:
            print(f"FAIL: frozen declarations absent from the report: {missing}", file=sys.stderr); ok = False
        if extra:
            print(f"FAIL: report names not in the frozen list: {extra}", file=sys.stderr); ok = False
    else:
        print(f"FAIL: frozen name list missing: {NAMES_FILE}", file=sys.stderr); ok = False
    got_free = {re.match(r"^'([^']+)'", l).group(1) for l in lines
                if "does not depend on any axioms" in l}
    if got_free != AXIOM_FREE_NAMES:
        print(f"FAIL: axiom-free declarations are {sorted(got_free)}, "
              f"expected {sorted(AXIOM_FREE_NAMES)}", file=sys.stderr); ok = False
    for kind, l in bad:
        print(f"FAIL ({kind}): {l}", file=sys.stderr); ok = False
    print("READING LAYER AXIOM CHECK " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
