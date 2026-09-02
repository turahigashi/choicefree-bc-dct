#!/usr/bin/env python3
"""check_paper_against_logs.py --- the paper's figures must match the shipped logs.

    python3 tools/check_paper_against_logs.py

Every number the paper states about the artifact is produced by a run recorded in
`logs/`.  Stating one by hand invites the two to drift, and a paper whose subject is
auditing cannot afford that.  This script reads the figure out of the log and checks
that the paper contains it.  It does not edit the paper; it fails.
"""
from __future__ import annotations
from pathlib import Path
import re, sys

ROOT = Path(__file__).resolve().parents[1]

def read(p: Path) -> str:
    return p.read_text(encoding='utf-8', errors='replace')

def grab(text: str, pattern: str, what: str) -> str:
    m = re.search(pattern, text)
    if not m:
        print(f"MISSING IN LOG: {what} (pattern {pattern!r})")
        sys.exit(2)
    return m.group(1)

def main() -> int:
    paper = ROOT / 'paper' / 'paper.tex'
    if not paper.exists():
        print("paper/paper.tex absent; nothing to check")
        return 0
    tex = read(paper).replace('{,}', ',')
    build = read(ROOT / 'logs' / 'build_audit.txt')
    rl    = read(ROOT / 'logs' / 'reading_layer_axioms.txt')
    lean  = [p for p in ROOT.rglob('*.lean')
             if '.lake' not in p.parts and 'tools' not in p.parts]
    decl  = re.compile(r'(?m)^(private )?(noncomputable )?(theorem|def|lemma|structure|abbrev|instance) ')

    checks = [
        ("artifact version",        grab(build, r'artifact_version=([\d.]+)', 'artifact_version')),
        ("static-audit closure",    grab(build, r'closure_files: (\d+)', 'closure_files')),
        ("tracked Lean files",      grab(build, r'tracked_lean_files: (\d+)', 'tracked_lean_files')),
        ("reading-layer count",     grab(build, r'reading_layer_declarations=(\d+)', 'reading_layer_declarations')),
        ("reading layer [propext, Quot.sound]", str(rl.count('propext, Quot.sound'))),
        ("reading layer no axioms", str(rl.count('does not depend on any axioms'))),
        ("Lean files in the tree",  f"{len(lean):,}"),
        ("lines in the tree",       f"{sum(len(read(p).splitlines()) for p in lean):,}"),
        ("declarations in the tree",f"{sum(len(decl.findall(read(p))) for p in lean):,}"),
        ("frozen names",            str(len([l for l in read(ROOT/'tools'/'frozen_names.txt').splitlines()
                                             if l.strip() and not l.startswith('#')]))),
    ]
    # ★The frozen-name list is a window on the paper; a stale window passes while the
    # claim it checks has become false.  Compare it with what the paper names now.
    frozen_path = ROOT / 'tools' / 'frozen_names.txt'
    stale = []
    if frozen_path.exists():
        frozen = {l.strip().split(None, 1)[1].strip() for l in read(frozen_path).splitlines()
                  if l.strip() and not l.startswith('#')}
        EXCL = {'DominatedConvergence','MeasureTheory','_autoC','admit','extern','simp',
                'thm_4_15_dominated_convergence','ContinuousOn','lemma33_lt_of_not_le',
                'lemma34_out_exists_cell','fatou_type_stub_not_source_4_14','partialFuncLe',
                'sorry','sorryAx','native_decide','unsafe','implemented_by','private',
                'Classical.choice','Classical.choose','Quot.out','Quotient.out',
                'ofReduceBool','ConstructiveReals','CR_cv','CRuncountable','CvMeasure',
                'DominatedMeasureCvZero','mathlib','SHA256SUMS','debug.skipKernelTC',
                # ordinary words and keywords the prose prints in \texttt: not identifiers
                'classical','ring','axiom','noncomputable','lemma','structure','instance',
                # a banned-token spelling in the static audit, not an identifier
                'Classical.'}
        named = set()
        for m in re.findall(r'\\(?:path|texttt)\{([^}]*)\}', read(paper)):
            t = m.replace('\\_', '_').strip()
            if '/' in t or ' ' in t or not t:
                continue
            if t.endswith(('.lean', '.txt', '.sh', '.py', '.md', '.cff', '.toml')):
                continue
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", t) and len(t) > 3:
                named.add(t)
        src = '\n'.join(read(p) for p in lean)
        # The paper may print a short form of a name the list records in full.
        # Treat "X" as listed when some entry ends with ".X" or "/X".
        def listed(t):
            return t in frozen or any(f.endswith('.' + t) or f.endswith('/' + t)
                                      for f in frozen)
        for t in sorted(n for n in named - EXCL if not listed(n)):
            short = t.split('.')[-1]
            if re.search(r'\b' + re.escape(short) + r'\b', src):
                stale.append(t)

    bad = 0
    for label, value in checks:
        ok = value in tex
        print(f"{'ok  ' if ok else 'MISS'} {label}: {value}")
        if not ok:
            bad += 1
    for t in stale:
        print(f"MISS frozen_names.txt does not list an identifier the paper names: {t}")
    bad += len(stale)
    print(f"figures_checked: {len(checks)}")
    print(f"frozen_names_stale: {len(stale)}")
    print(f"missing_from_paper: {bad}")
    if bad:
        print("PAPER/LOG CONSISTENCY CHECK FAILED")
        return 1
    print("PAPER/LOG CONSISTENCY CHECK PASSED")
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
