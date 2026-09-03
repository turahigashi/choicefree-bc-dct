#!/usr/bin/env python3
"""check_public_state.py --- does the public state match what the documents say?

    python3 tools/check_public_state.py [--commit <sha>]

`check_release_consistency.py` compares the paper, the README, the manifest and the
citation file with each other.  Four documents can agree perfectly and all be wrong:
they can name a tag that was never pushed and a DOI that resolves to nothing.  A
review put it plainly --- textual consistency and the actual published state are two
different things --- so they are two different checks, and this is the second one.

It is deliberately not part of `build_audit.sh`.  That script must run offline, from
an extracted archive, years from now; a network check there would fail for reasons
that say nothing about the artifact.  This one is a release gate: run it once, when
the deposit is cut, and record what it printed.

Exit status is 0 only if every check reached the network and passed.  A check that
could not reach the network fails: "we could not tell" is not "it is fine".
"""
import json, re, subprocess, sys, urllib.request, urllib.error
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TIMEOUT = 30

def read(p): return p.read_text(encoding="utf-8", errors="replace")

def get(url, want_json=False):
    req = urllib.request.Request(url, headers={"User-Agent": "choicefree-bc-dct-release-check"})
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as r:
            body = r.read()
            return r.status, (json.loads(body) if want_json else body)
    except urllib.error.HTTPError as e:
        return e.code, None
    except Exception as e:
        return None, str(e)

def main(argv):
    # ★Without a commit to compare against, this checked only that a tag of the right
    # name exists -- and a review found the paper saying the tag and the deposit were
    # made from "the exact tree audited above" while the tree had moved four commits
    # past the tag.  The name was right and the object was not.  So default to the
    # commit this working tree is on, and let --commit override it deliberately.
    want_commit = None
    if "--commit" in argv:
        want_commit = argv[argv.index("--commit") + 1]
    else:
        try:
            want_commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                         capture_output=True, text=True, check=True
                                         ).stdout.strip()
            print(f"comparing against this working tree: {want_commit[:12]}")
        except Exception:
            print("FAIL: no commit given and this is not a git checkout; pass --commit",
                  file=sys.stderr)
            return 1
    ok = True

    manifest = read(ROOT / "ARTIFACT_MANIFEST.md")
    version = re.search(r"(?m)^- Version: `([\d.]+)`", manifest).group(1)
    # ★The citation file names both the version DOI and the concept DOI; taking the
    # first match found the concept DOI, which resolves to whichever version is latest
    # and so would have reported an unrelated record as this release.  Take the one on
    # the `doi:` key, and refuse to proceed if it is the concept DOI.
    cff = read(ROOT / "CITATION.cff")
    m = re.search(r'(?m)^doi:\s*"?10\.5281/zenodo\.(\d+)"?', cff)
    if not m:
        print("FAIL: CITATION.cff has no doi: key", file=sys.stderr); return 1
    doi = m.group(1)
    concept = re.search(r"concept DOI[^0-9]*10\.5281/zenodo\.(\d+)", read(ROOT / "README.md"))
    if concept and concept.group(1) == doi:
        print(f"FAIL: CITATION.cff names the concept DOI {doi}, which resolves to whichever "
              f"version is latest, not to this release", file=sys.stderr); return 1
    tag = f"v{version}"
    print(f"declared: tag={tag} version_doi=10.5281/zenodo.{doi}")

    # 1. The tag exists in the public repository, and points where it should.
    repo = re.search(r"github\.com/([\w.-]+/[\w.-]+)", read(ROOT / "CITATION.cff"))
    slug = repo.group(1).rstrip("/") if repo else None
    if not slug:
        print("FAIL: no repository named in CITATION.cff", file=sys.stderr); ok = False
    else:
        st, body = get(f"https://api.github.com/repos/{slug}/git/refs/tags/{tag}", want_json=True)
        if st != 200 or not isinstance(body, dict):
            print(f"FAIL: the public repository has no tag {tag} (HTTP {st})", file=sys.stderr); ok = False
        else:
            sha = body.get("object", {}).get("sha", "")
            # An annotated tag points at a tag object; dereference it.
            if body.get("object", {}).get("type") == "tag":
                st2, b2 = get(f"https://api.github.com/repos/{slug}/git/tags/{sha}", want_json=True)
                sha = b2.get("object", {}).get("sha", sha) if st2 == 200 and isinstance(b2, dict) else sha
            print(f"public_tag: {tag} -> {sha[:12]}")
            if want_commit and not sha.startswith(want_commit[:12]):
                print(f"FAIL: {tag} points at {sha[:12]}, not the expected {want_commit[:12]}",
                      file=sys.stderr); ok = False

    # 2. The version DOI resolves, and to a record of this version.
    st, body = get(f"https://zenodo.org/api/records/{doi}", want_json=True)
    if st != 200 or not isinstance(body, dict):
        print(f"FAIL: 10.5281/zenodo.{doi} does not resolve as a published record (HTTP {st})",
              file=sys.stderr); ok = False
    else:
        got = (body.get("metadata") or {}).get("version")
        files = [f.get("key") for f in body.get("files", [])]
        print(f"zenodo_record: version={got} files={files}")
        if got != version:
            print(f"FAIL: the published record is version {got}, not {version}", file=sys.stderr); ok = False
        if not files:
            print("FAIL: the published record carries no files", file=sys.stderr); ok = False

        # ★The record can carry a file of the right name and the wrong bytes.  When the
        # archive built from the tagged tree is beside us, compare its digest with what
        # Zenodo holds, so "the deposit is this tree" is checked rather than assumed.
        local = ROOT.parent / f"choicefree-bc-dct-{version}.zip"
        if local.exists():
            import hashlib
            mine = hashlib.md5(local.read_bytes()).hexdigest()
            theirs = {f.get("key"): (f.get("checksum") or "").split(":")[-1]
                      for f in body.get("files", [])}
            match = [k for k, v in theirs.items() if v == mine]
            print(f"archive_md5: local={mine[:12]} matches={match}")
            if not match:
                print(f"FAIL: no published file matches the local archive; "
                      f"published digests {theirs}", file=sys.stderr); ok = False
        else:
            print(f"archive_md5: no local archive at {local.name} to compare")

        # The DOI must also resolve through doi.org, not only through Zenodo's API.
        st3, _ = get(f"https://doi.org/10.5281/zenodo.{doi}")
        print(f"doi_org_resolution: HTTP {st3}")
        if st3 not in (200, 302, 301):
            print(f"FAIL: doi.org does not resolve 10.5281/zenodo.{doi} (HTTP {st3})",
                  file=sys.stderr); ok = False

    print("PUBLIC STATE CHECK " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv))
