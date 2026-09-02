#!/usr/bin/env python3
"""Generate a Lean check file printing the axiom footprint of every public
declaration in the reading-layer modules.

The generated file is written outside the tracked Lean closure so that the
audited closure of the artifact is preserved.
"""
import argparse, re, sys

MODULES = [
    ("Mathdemo/MathematicalInterface.lean", "Mathdemo.MathematicalInterface"),
    ("Mathdemo/SourceIntegrationSpaceDef11.lean", "Mathdemo.SourceIntegrationSpaceDef11"),
    ("Mathdemo/DiracIntegrationSpace.lean", "Mathdemo.DiracIntegrationSpace"),
    ("Mathdemo/FiniteWeightedIntegrationSpace.lean", "Mathdemo.FiniteWeightedIntegrationSpace"),
]
DECL = re.compile(r"^(noncomputable )?(theorem|def|lemma|structure|abbrev|instance) "
                  r"([A-Za-z_][A-Za-z0-9_'.]*)")

def collect(path):
    names, ns = [], []
    for line in open(path, encoding="utf-8"):
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            ns.append(m.group(1)); continue
        if re.match(r"^end\s+\S+", line):
            if ns: ns.pop()
            continue
        if line.startswith("private "):
            continue
        d = DECL.match(line)
        if d:
            names.append(".".join(ns + [d.group(3)]))
    return names

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True)
    a = ap.parse_args()
    names, seen = [], set()
    for path, _ in MODULES:
        for n in collect(path):
            if n in seen:
                print(f"duplicate declaration name: {n}", file=sys.stderr); return 1
            seen.add(n); names.append(n)
    with open(a.output, "w", encoding="utf-8") as f:
        for _, mod in MODULES:
            f.write(f"import {mod}\n")
        f.write("\n")
        for n in names:
            f.write(f"#print axioms {n}\n")
    print(f"reading_layer_declarations={len(names)}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
