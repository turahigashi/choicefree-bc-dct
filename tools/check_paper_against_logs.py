#!/usr/bin/env python3
"""check_paper_against_logs.py --- selected numeric invariants and frozen-name coverage.

    python3 tools/check_paper_against_logs.py [paper/paper.tex]

Numbers the paper states about the artifact are produced by runs recorded in `logs/`.
Stating one by hand invites the two to drift, and a paper whose subject is auditing
cannot afford that.  This script reads a fixed set of figures out of the logs and
checks that each appears somewhere in the TeX, and that the frozen-name list has not
gone stale.  It does not edit the paper; it fails.

Its scope is deliberately narrow, and the reader should not take a pass for more than
it is.  It checks that a value occurs, not that it occurs in the right sentence, and
it covers only the figures enumerated in `checks()` below.  Numbers stated in the
paper but outside that list --- the reachability split, the source-item count, the
public-alias closure, the reading-layer breakdown, the file-placement table --- are
not compared here, and a passing run is no evidence about them.  Extending the list
is the way to bring one under machine check.
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


# ★The kernel prints two forms.  Counting only "depends on axioms" silently drops
# the declarations that depend on no axiom at all -- the best ones in the tree --
# and that is exactly how the figure in the paper went wrong once.
# ★Lean names may contain an apostrophe (BishopSec1P.IntSpaceC.I_mono'), so a
# character class that excludes ' truncates the name and loses one declaration.
# Match lazily up to the literal suffix instead.
AXIOM_LINE = re.compile(r"'(.+?)' (?:depends on axioms|does not depend on any axioms)")


def axiom_log_names() -> int:
    """Distinct declaration names carrying kernel axiom output in the shipped logs."""
    names = set()
    for path in sorted((ROOT / 'logs').glob('*.txt')):
        if 'rerun' in path.name:
            continue
        text = re.sub(r"\n\s+", " ", read(path))   # the logs wrap long names
        names.update(AXIOM_LINE.findall(text))
    return len(names)


def main() -> int:
    # ★Accept the paper's location: a review bundle may place paper/ beside the
    # artifact rather than inside it.  Absence must FAIL -- a checker that
    # succeeds because it found nothing to check is worse than no checker, and
    # this one had exactly that behaviour (it returned 0 with "nothing to check").
    argv = [a for a in sys.argv[1:] if not a.startswith('-')]
    candidates = ([Path(argv[0])] if argv else
                  [ROOT / 'paper' / 'paper.tex', ROOT.parent / 'paper' / 'paper.tex'])
    paper = next((c for c in candidates if c.exists()), None)
    if paper is None:
        print("PAPER NOT FOUND: " + ", ".join(str(c) for c in candidates), file=sys.stderr)
        print("PAPER/LOG CONSISTENCY CHECK FAILED")
        return 1
    tex = read(paper).replace('{,}', ',')
    build = read(ROOT / 'logs' / 'build_audit.txt')
    rl    = read(ROOT / 'logs' / 'reading_layer_axioms.txt')
    lean  = [p for p in ROOT.rglob('*.lean')
             if '.lake' not in p.parts and 'tools' not in p.parts]
    decl  = re.compile(r'(?m)^(private )?(noncomputable )?(theorem|def|lemma|structure|abbrev|instance) ')

    # ★Each figure is anchored to the sentence that states it.  Without an anchor the
    # test is only that the value occurs somewhere in the TeX, and a stale figure in one
    # sentence passes because the same number is correct in another: changing "traverses
    # 513 Lean files" to 999 left the run green, because 513 still appeared elsewhere.
    # `{v}` in an anchor is replaced by the value, written the way TeX writes it.
    checks = [
        ("artifact version",        grab(build, r'artifact_version=([\d.]+)', 'artifact_version'),
                                    r'artifact\\_version={v}'),
        ("static-audit closure",    grab(build, r'closure_files: (\d+)', 'closure_files'),
                                    r'closure\\_files: {v}'),
        ("tracked Lean files",      grab(build, r'tracked_lean_files: (\d+)', 'tracked_lean_files'),
                                    r'tracked\\_lean\\_files: {v}'),
        ("reading-layer count",     grab(build, r'reading_layer_declarations=(\d+)', 'reading_layer_declarations'),
                                    r'all \${v}\$ reading-layer declarations'),
        ("reading layer [propext, Quot.sound]", str(rl.count('propext, Quot.sound')),
                                    r'verifies that \${v}\$ report'),
        ("reading layer no axioms", str(rl.count('does not depend on any axioms')),
                                    r'the (?:{w}|\${v}\$) which report no axioms'),
        ("Lean files in the tree",  f"{len(lean):,}",
                                    r'traverses \${v}\$ Lean files'),
        ("lines in the tree",       f"{sum(len(read(p).splitlines()) for p in lean):,}",
                                    r'\${v}\$ lines'),
        ("declarations in the tree",f"{sum(len(decl.findall(read(p))) for p in lean):,}",
                                    r'\${v}\$ declarations by the lexical count'),
        ("frozen names",            str(len([l for l in read(ROOT/'tools'/'frozen_names.txt').splitlines()
                                             if l.strip() and not l.startswith('#')])),
                                    r'\${v}\$ entries of'),
        ("distinct names in the axiom logs", f"{axiom_log_names():,}",
                                    r'for \${v}\$ distinct names'),
    ]
    # ★The frozen-name list is a window on the paper; a stale window passes while the
    # claim it checks has become false.  Compare it with what the paper names now.
    frozen_path = ROOT / 'tools' / 'frozen_names.txt'
    stale = []
    if frozen_path.exists():
        # A frozen line is `<type>\t<name>[\t...]`; take the name, which for a binder
        # is followed by the file and declaration it lives in.
        frozen = {l.split('\t')[1].strip() if '\t' in l else l.strip().split(None, 1)[1].strip()
                  for l in read(frozen_path).splitlines()
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
    # ★A bare substring test lets a short figure match inside a longer number
    # (``114`` inside ``1,148``), so a stale figure can pass.  Require that the
    # value not be flanked by a digit, a comma between digits, or a decimal point.
    WORDS = {'0':'no','1':'one','2':'two','3':'three','4':'four','5':'five','6':'six',
             '7':'seven','8':'eight','9':'nine','10':'ten','11':'eleven','12':'twelve'}

    def at_claim_site(v: str, anchor: str) -> bool:
        """Is the value written where the paper makes the claim about it?

        The TeX has already had ``{,}`` folded to ``,`` when it was read, so an anchor
        spells a thousands separator as a plain comma.  ``{w}`` expands to the English
        numeral for small counts, because the paper says "the two which report no
        axioms" rather than printing a digit."""
        pat = anchor.replace('{v}', re.escape(v))
        pat = pat.replace('{w}', re.escape(WORDS.get(v, v)))
        return re.search(pat, tex) is not None

    def present(v: str) -> bool:
        return re.search(r'(?<![\d.,])' + re.escape(v) + r'(?![\d.,]*\d)', tex) is not None

    for label, value, anchor in checks:
        ok = at_claim_site(value, anchor)
        note = ''
        if not ok and present(value):
            note = '  (the value occurs elsewhere in the paper, but not at its claim site)'
        print(f"{'ok  ' if ok else 'MISS'} {label}: {value}{note}")
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
