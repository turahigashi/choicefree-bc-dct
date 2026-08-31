#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
AUDIT_ROOTS = [
    "ChoiceFreeMeasureDCTPublic",
    "SupplementChoiceFreeMeasureDCT",
    "Mathdemo.CheckSec3PortAxioms",
    "Mathdemo.CheckDCTV2Axioms",
    "Mathdemo.CheckBishopChengTheorem415PropAxioms",
    "Mathdemo",
]
BANNED_LITERALS = [
    "Classical.choice",
    "Classical.choose",
    "Classical.",
    "native_decide",
    "Quot.out",
]

BANNED_REGEXES = [
    ("sorry", re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")),
    ("admit", re.compile(r"(?<![A-Za-z0-9_'])admit(?![A-Za-z0-9_'])")),
    ("unsafe", re.compile(r"(?<![A-Za-z0-9_'])unsafe(?![A-Za-z0-9_'])")),
    ("open scoped Classical", re.compile(r"(?<![A-Za-z0-9_'])open\s+scoped\s+Classical(?![A-Za-z0-9_'])")),
    ("open Classical", re.compile(r"(?<![A-Za-z0-9_'])open\s+Classical(?![A-Za-z0-9_'])")),
    ("classical", re.compile(r"(?<![A-Za-z0-9_'])classical(?![A-Za-z0-9_'])")),
    # Added in v0.4.2.  The first six close gaps that a literal scan of the
    # earlier list left open; the last catches a vacuous statement, which the
    # token scan otherwise cannot see (it detects vacuous proofs, not vacuous
    # statements).  All seven report zero on the v0.4.2 closure.
    ("axiom declaration", re.compile(r"(?m)^\s*axiom\s")),
    ("Quotient.out", re.compile(r"(?<![A-Za-z0-9_'])Quotient\.out(?![A-Za-z0-9_'])")),
    ("partial def", re.compile(r"(?m)^\s*partial\s+def\s")),
    ("implemented_by", re.compile(r"implemented_by")),
    ("extern", re.compile(r"@\[extern")),
    ("debug.skipKernelTC", re.compile(r"debug\.skipKernelTC")),
    ("conclusion True", re.compile(r":\s*True\s*:=")),
]

def strip_comments(src: str) -> str:
    out = []
    i = 0
    depth = 0
    n = len(src)
    while i < n:
        if depth == 0 and i + 1 < n and src[i:i+2] == "--":
            j = src.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
        elif i + 1 < n and src[i:i+2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and i + 1 < n and src[i:i+2] == "-/":
            depth -= 1
            i += 2
        elif depth > 0:
            if src[i] == "\n":
                out.append("\n")
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)

def mod_to_path(mod: str) -> Path:
    return ROOT / (mod.replace('.', '/') + '.lean')

def imports(path: Path) -> list[str]:
    src = strip_comments(path.read_text(encoding='utf-8'))
    out: list[str] = []
    for line in src.splitlines():
        s = line.strip()
        if s.startswith('import '):
            out.extend(s.split()[1:])
    return out

# ★Modules that belong to this project.  A missing file under one of these
# prefixes is a packaging error, not an external dependency, and must fail the
# audit: treating it as external silently shrinks the closure being audited.
LOCAL_PREFIXES = (
    "Mathdemo",
    "ChoiceFreeMeasureDCTPublic",
    "SupplementChoiceFreeMeasureDCT",
)
# ★Prefixes that are legitimately outside this repository.
EXTERNAL_PREFIXES = ("Mathlib", "Init", "Std", "Lean", "Batteries", "Aesop", "Qq", "Plausible", "ImportGraph", "ProofWidgets", "LeanSearchClient")

class AuditError(RuntimeError):
    pass

def is_local(mod: str) -> bool:
    return any(mod == p or mod.startswith(p + ".") for p in LOCAL_PREFIXES)

def is_external(mod: str) -> bool:
    return any(mod == p or mod.startswith(p + ".") for p in EXTERNAL_PREFIXES)

def closure(roots: list[str]) -> list[str]:
    seen: list[str] = []
    def dfs(mod: str) -> None:
        if mod in seen:
            return
        path = mod_to_path(mod)
        if not path.exists():
            # ★fail closed: a project-local import that is not on disk is an error.
            if is_local(mod):
                raise AuditError(f"missing project-local import: {mod} (expected {path})")
            if not is_external(mod):
                raise AuditError(f"unclassified import, neither local nor allowed-external: {mod}")
            return
        seen.append(mod)
        for dep in imports(path):
            dfs(dep)
    for r in roots:
        dfs(r)
    return seen

def tracked_lean_paths() -> set[str] | None:
    """The Lean paths of the development recorded in SHA256SUMS.

    Files under `tools/` are auditing scripts, not part of the development, and
    are excluded: they are not imported by anything and so never appear in the
    import closure."""
    f = ROOT / 'SHA256SUMS'
    if not f.exists():
        return None
    out = set()
    for line in f.read_text(encoding='utf-8').splitlines():
        parts = line.split(None, 1)
        if len(parts) != 2:
            continue
        rel = parts[1].strip().lstrip('./')
        if rel.endswith('.lean') and not rel.startswith('tools/'):
            out.add(rel)
    return out or None

def token_hits(src: str) -> list[tuple[str, int, str]]:
    hits = []
    for lineno, line in enumerate(src.splitlines(), start=1):
        for token in BANNED_LITERALS:
            if token in line:
                hits.append((token, lineno, line.strip()))
        for token, regex in BANNED_REGEXES:
            if regex.search(line):
                hits.append((token, lineno, line.strip()))
    return hits

def main() -> int:
    try:
        mods = closure(AUDIT_ROOTS)
    except AuditError as e:
        print(f"audit_roots: {', '.join(AUDIT_ROOTS)}")
        print(f"STATIC AUDIT FAILED: {e}")
        return 1
    failures = []
    for mod in mods:
        path = mod_to_path(mod)
        src = strip_comments(path.read_text(encoding='utf-8'))
        for token, lineno, line in token_hits(src):
            failures.append((path.relative_to(ROOT), lineno, token, line))
    print(f"audit_roots: {', '.join(AUDIT_ROOTS)}")
    print(f"closure_files: {len(mods)}")
    for mod in mods:
        print(f"closure: {mod_to_path(mod).relative_to(ROOT)}")
    # ★The closure must coincide with the Lean files the release tracks.
    tracked = tracked_lean_paths()
    if tracked is not None:
        got = {str(mod_to_path(m).relative_to(ROOT)) for m in mods}
        only_tracked = sorted(tracked - got)
        only_closure = sorted(got - tracked)
        print(f"tracked_lean_files: {len(tracked)}")
        if only_tracked or only_closure:
            print("STATIC AUDIT FAILED: closure does not match the tracked Lean file set")
            for x in only_tracked[:20]:
                print(f"  tracked but not in closure: {x}")
            for x in only_closure[:20]:
                print(f"  in closure but not tracked: {x}")
            if len(only_tracked) > 20 or len(only_closure) > 20:
                print(f"  ... {len(only_tracked)} tracked-only, {len(only_closure)} closure-only in total")
            return 1
    else:
        print("tracked_lean_files: (SHA256SUMS absent; set comparison skipped)")
    if failures:
        print("STATIC AUDIT FAILED")
        for path, lineno, token, line in failures:
            print(f"{path}:{lineno}: banned {token}: {line}")
        return 1
    print("STATIC AUDIT PASSED")
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
