#!/usr/bin/env python3
"""check_displayed_definitions.py --- the definitions shown in the paper must be the ones in the source.

    python3 tools/check_displayed_definitions.py [paper/paper.tex]

Section "The definitions the theorem is stated over" reproduces Lean definitions so
that a reader can audit the correspondence the kernel does not check.  A displayed
definition that has drifted from the source would defeat the point of showing it, and
the drift would be invisible: the paper still compiles, and the audit still passes.

So compare them.  Doc-strings are stripped from the display -- they are commentary,
and reproducing them would triple the length -- so they are stripped from the source
before comparison too; everything else must agree token for token.

★Written after three attempts to display these by hand went wrong.  The first
paraphrased Lean's Unicode into words that are not Lean syntax (`in`, `subset`); the
second replaced ASCII spellings with Unicode ones in definitions whose source uses
ASCII; the third looked right and still differed.  The source is the only reliable
copy, and the only way to know a display matches it is to check.
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SEC = r'\subsection{The definitions the theorem is stated over}'
END = r'\subsection{Three-layer public interface}'

def strip_docstrings(t):
    return re.sub(r'(?ms)^\s*/--.*?-/\n', '', t)

def norm(t):
    return re.sub(r'\s+', ' ', t).strip()

def main(argv):
    paper = Path(argv[1]) if len(argv) > 1 else ROOT / 'paper' / 'paper.tex'
    if not paper.exists():
        for c in (ROOT / 'paper' / 'paper.tex', ROOT.parent / 'paper' / 'paper.tex'):
            if c.exists(): paper = c; break
    if not paper.exists():
        print("DISPLAYED DEFINITION CHECK SKIPPED: no paper source in this deposit")
        return 0
    tex = paper.read_text(encoding='utf-8')
    if SEC not in tex:
        print(f"FAIL: the paper has no section displaying definitions", file=sys.stderr); return 1
    body = tex[tex.index(SEC):tex.index(END)]

    lean = "\n".join(strip_docstrings(p.read_text(encoding='utf-8'))
                     for p in sorted(ROOT.rglob('*.lean'))
                     if '.lake' not in p.parts and 'tools' not in p.parts)
    lean_n = norm(lean)

    shown, bad = 0, []
    for m in re.finditer(r'\\begin\{verbatim\}(.*?)\\end\{verbatim\}', body, re.S):
        for part in m.group(1).strip().split('\n\n'):
            name = re.match(r'(?:structure|def|theorem)\s+(\w+)', part.strip())
            if not name:
                continue
            shown += 1
            if norm(part) not in lean_n:
                bad.append(name.group(1))
    print(f"displayed_definitions={shown} matching_source={shown - len(bad)}")
    for n in bad:
        print(f"FAIL: the displayed {n} is not in the source verbatim (doc-strings aside)",
              file=sys.stderr)
    if shown == 0:
        print("FAIL: the section displays no definitions", file=sys.stderr); return 1
    print("DISPLAYED DEFINITION CHECK " + ("PASSED" if not bad else "FAILED"))
    return 0 if not bad else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv))
