#!/usr/bin/env python3
"""check_release_consistency.py --- the four documents must agree about the release.

    python3 tools/check_release_consistency.py [paper/paper.tex]

The version, the concept DOI and the release status are written by hand in the
paper, the README, the artifact manifest and `CITATION.cff`.  Four hand-maintained
copies drift, and they did: a review found the paper saying the artifact "is tagged
v0.6.0" and the manifest saying `Git tag: v0.6.0` while no such tag existed
anywhere, next to a README that already said the version DOI was not yet assigned.
Nothing in the audit noticed, because no check compared the four.

This script compares them and fails on disagreement.  It also refuses the one
combination that is a claim rather than a slip: calling the tree released while the
version DOI is still unassigned.  It is deliberately textual; it cannot see a Git
tag, and the deposit carries no `.git`, so `released` here means "the documents say
so" and the tag must be verified when the release is cut.
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DOI = "10.5281/zenodo.21850965"

def read(p):
    return p.read_text(encoding="utf-8", errors="replace")

def main(argv):
    paper = Path(argv[1]) if len(argv) > 1 else None
    if paper is None:
        for c in (ROOT / "paper" / "paper.tex", ROOT.parent / "paper" / "paper.tex"):
            if c.exists():
                paper = c; break
    readme, manifest, cff = ROOT / "README.md", ROOT / "ARTIFACT_MANIFEST.md", ROOT / "CITATION.cff"
    for f in (readme, manifest, cff):
        if not f.exists():
            print(f"RELEASE CONSISTENCY CHECK FAILED: missing {f}", file=sys.stderr); return 1

    versions, ok = {}, True
    if paper is not None and paper.exists():
        m = re.search(r'\\def\\CFBDCTVersion\{([\d.]+)\}', read(paper))
        if m: versions["paper"] = m.group(1)
    else:
        print("release_consistency: no paper source in this deposit; comparing the other three")
    for name, f, pat in (("README", readme,   r'(?m)^Version:\s*([\d.]+)'),
                         ("manifest", manifest, r'(?m)^- Version:\s*`([\d.]+)`'),
                         ("CITATION.cff", cff, r'(?m)^version:\s*"([\d.]+)"')):
        m = re.search(pat, read(f))
        if m: versions[name] = m.group(1)
        else:
            print(f"FAIL: no version found in {name}", file=sys.stderr); ok = False

    print("release_version: " + ", ".join(f"{k}={v}" for k, v in sorted(versions.items())))
    if len(set(versions.values())) > 1:
        print(f"FAIL: the documents disagree about the version: {versions}", file=sys.stderr); ok = False

    # The concept DOI is quoted in all of them and must be the same string.
    for name, f in (("README", readme), ("manifest", manifest), ("CITATION.cff", cff)):
        if CONCEPT_DOI not in read(f):
            print(f"FAIL: {name} does not carry the concept DOI {CONCEPT_DOI}", file=sys.stderr); ok = False
    if paper is not None and paper.exists() and CONCEPT_DOI not in read(paper):
        print(f"FAIL: the paper does not carry the concept DOI {CONCEPT_DOI}", file=sys.stderr); ok = False

    # Release status.  A candidate says so; a release must have a version DOI.
    texts = {"README": read(readme), "manifest": read(manifest), "CITATION.cff": read(cff)}
    if paper is not None and paper.exists():
        texts["paper"] = read(paper)
    candidate = {k: ("release candidate" in v.lower()) for k, v in texts.items()}
    unassigned = {k: bool(re.search(r'not yet assigned|assigned when|reserved at deposit time|do not exist yet', v))
                  for k, v in texts.items()}
    print("release_status: " + ", ".join(f"{k}={'candidate' if candidate[k] else 'released'}"
                                         for k in sorted(candidate)))
    if any(candidate.values()) and not all(candidate.values()):
        missing = sorted(k for k, v in candidate.items() if not v)
        print(f"FAIL: some documents call this a release candidate and these do not: {missing}",
              file=sys.stderr); ok = False
    if not any(candidate.values()) and any(unassigned.values()):
        stale = sorted(k for k, v in unassigned.items() if v)
        print(f"FAIL: the release is not marked a candidate, yet {stale} still say the version DOI "
              f"is unassigned", file=sys.stderr); ok = False
    # A candidate must not also assert that the tag exists.
    if all(candidate.values()):
        for k, v in texts.items():
            if re.search(r'is tagged \\texttt\{v|^- Git tag: `v', v, re.M):
                print(f"FAIL: {k} calls this a release candidate but also states the tag exists",
                      file=sys.stderr); ok = False
    print("RELEASE CONSISTENCY CHECK " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv))
