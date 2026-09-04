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
# ★The version DOI is the identifier most able to send a reader to the wrong object,
# and until this was added it was the one no check compared: changing a digit of it in
# the paper left every shipped check passing.  It is read from the documents rather
# than pinned here, so cutting the next release does not mean editing this file; what
# is enforced is that the four documents name the same one, and exactly one.
VERSION_DOI_RE = re.compile(r"10\.5281/zenodo\.(\d+)")

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

    # The version DOI: every document must name the same one, and it must not be the
    # concept DOI, which resolves to whichever version is latest rather than to this one.
    concept_id = CONCEPT_DOI.split(".")[-1]
    version_dois = {}
    for name, f in (("README", readme), ("manifest", manifest), ("CITATION.cff", cff),
                    *(( ("paper", paper), ) if paper is not None and paper.exists() else ())):
        found = {m.group(1) for m in VERSION_DOI_RE.finditer(read(f))} - {concept_id}
        # Earlier versions are cited by DOI too; the one for this release is the one
        # that appears in the same document as the version string.
        version_dois[name] = found
    # ★Comparing the documents only with each other is not enough: the README names the
    # version DOI three times, and changing one of them left the intersection --- and so
    # every check --- intact.  Compare against a ledger instead, so that any DOI the
    # documents name and the ledger does not is a finding wherever it appears.
    ledger_path = ROOT / "tools" / "release_dois.txt"
    if not ledger_path.exists():
        print(f"FAIL: missing DOI ledger {ledger_path}", file=sys.stderr); ok = False
    else:
        ledger = {}
        ledger_ver = {}
        for line in read(ledger_path).splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) == 3:
                role, ver, d = parts
            else:                       # ★the two-column form this file used to have
                role, d = parts; ver = None
            ledger[d.split(".")[-1]] = role
            if ver and ver != "-":
                ledger_ver[ver] = d.split(".")[-1]
        release = [k for k, v in ledger.items() if v == "version"]
        if len(release) != 1:
            print(f"FAIL: the ledger must name exactly one version DOI, it names {len(release)}",
                  file=sys.stderr); ok = False
        for name, f in (("README", readme), ("manifest", manifest), ("CITATION.cff", cff),
                        *(( ("paper", paper), ) if paper is not None and paper.exists() else ())):
            found = {m.group(1) for m in VERSION_DOI_RE.finditer(read(f))}
            unknown = sorted(found - set(ledger))
            if unknown:
                print(f"FAIL: {name} names Zenodo DOIs absent from the ledger: "
                      f"{['10.5281/zenodo.' + u for u in unknown]}", file=sys.stderr); ok = False
            if release and release[0] not in found:
                print(f"FAIL: {name} does not name the version DOI of this release",
                      file=sys.stderr); ok = False
        # ★The check above asks only whether a DOI appears in the ledger.  That is not
        # the property the documents assert: they assert that a *named version* has a
        # *particular* DOI, and three releases in a row named the current DOI as the
        # previous version's while every check passed, because both DOIs were in the
        # ledger.  Membership is not the pairing.  So read the pairs out of each
        # document and compare them with the ledger's.
        # ★Both orders occur: "v0.7.3: 10.5281/zenodo.NNN" and "10.5281/zenodo.NNN
        # (v0.7.3)".  A pattern for one order reads the other one off by one entry and
        # reports every row of a correct list as wrong, which is how the first version
        # of this check behaved.  Match both, and require the two to be adjacent --- no
        # other DOI or version number between them.
        fwd = re.compile(r"v(\d+\.\d+\.\d+)(?:[^0-9]|(?<=v)\d)"
                         r"{0,40}?10\.5281/zenodo\.(\d+)")
        bwd = re.compile(r"10\.5281/zenodo\.(\d+)[^0-9]{0,10}?\(v(\d+\.\d+\.\d+)\)")
        for name, f in (("README", readme), ("manifest", manifest),
                        *(( ("paper", paper), ) if paper is not None and paper.exists() else ())):
            body = read(f)
            pairs = [("v" + m.group(2), m.group(1)) for m in bwd.finditer(body)]
            claimed = {v for v, _ in pairs}
            pairs += [("v" + m.group(1), m.group(2)) for m in fwd.finditer(body)
                      if "v" + m.group(1) not in claimed]
            for ver, doi in pairs:
                want = ledger_ver.get(ver)
                if want and want != doi:
                    print(f"FAIL: {name} pairs {ver} with 10.5281/zenodo.{doi}; the "
                          f"ledger has 10.5281/zenodo.{want}", file=sys.stderr); ok = False
        if release and ledger_ver:
            prev = [d for v, d in ledger_ver.items()
                    if ledger.get(d) == "previous"]
            if release[0] in prev:
                print("FAIL: the version DOI is also listed as a previous one",
                      file=sys.stderr); ok = False
            print(f"version_doi_pairs: {len(ledger_ver)} version-to-DOI pairs checked")

        if release:
            print(f"release_version_doi: 10.5281/zenodo.{release[0]} "
                  f"(ledger: {len(ledger)} known DOIs)")

    # The tag: the documents name it, so they must name the same one.  A review
    # changed the manifest's tag to v0.6.1 and every check still passed.
    # ★Intersecting the documents' tag sets let a single wrong tag survive, because the
    # right one still appeared elsewhere in the same document.  Test each occurrence
    # instead: a tag named in the position where a document states its own tag must be
    # this release's tag.  Earlier tags may still be cited in prose about earlier
    # versions, so only the self-describing positions are pinned.
    release_tag = f"v{sorted(set(versions.values()))[0]}" if versions else None
    SELF_TAG = [("manifest", manifest, r"(?m)^- Git tag: `(v[\d.]+)`"),
                ("README",   readme,   r"(?m)^Git tag:\s*`?(v[\d.]+)`?")]
    for name, f, pat in SELF_TAG:
        m = re.search(pat, read(f))
        if m and release_tag and m.group(1) != release_tag:
            print(f"FAIL: {name} states its tag is {m.group(1)}, but the version is "
                  f"{release_tag[1:]}", file=sys.stderr); ok = False
    if release_tag:
        print(f"release_tag: {release_tag}")

    # The Zenodo record number written in a URL must be the version DOI's number; a
    # review changed it in the manifest and nothing noticed.
    if release:
        for name, f in (("README", readme), ("manifest", manifest)):
            for m in re.finditer(r"zenodo\.org/record/(\d+)", read(f)):
                if m.group(1) not in ledger:
                    print(f"FAIL: {name} links to Zenodo record {m.group(1)}, which the "
                          f"ledger does not know", file=sys.stderr); ok = False

    # The paper defines its version through a macro; a review deleted the definition
    # and nothing noticed, which would leave the version blank in the typeset paper.
    if paper is not None and paper.exists():
        if not re.search(r'\\def\\CFBDCTVersion\{[\d.]+\}', read(paper)):
            print("FAIL: the paper does not define \\CFBDCTVersion", file=sys.stderr); ok = False
        else:
            print("paper_version_macro: defined")

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
