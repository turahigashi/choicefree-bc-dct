#!/usr/bin/env python3
"""Check the *current-release identity* visible in a manuscript PDF against its TeX.

★Written by the round-6 reviewer and adopted here unchanged in substance.  The defect
it catches was real: v0.7.7 bumped the version in every document and rebuilt only the
title page, so the submitted `paper.pdf` still announced 0.7.6 and the previous DOI ---
on its cover, in four self-describing passages, and in its link annotations.  Every
existing check read the TeX, and the root checksums exclude `paper/`, so nothing saw it.

Usage: python3 check_submission_pdf.py submission/paper.tex submission/paper.pdf
Requires Python 3 and Poppler's pdftotext on PATH. No network access, no OCR.

This is deliberately a narrow release gate, not a full semantic PDF/TeX comparison.
Historical version/DOI references are allowed. The current identity is read from the
TeX version macro and title/date DOI, then from the PDF title and explicit current-
release sentences. A successful exit says nothing about Lean kernel verification.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import re
import shutil
import subprocess
import sys

def strip_comments(text: str) -> str:
    lines=[]
    for line in text.splitlines():
        i=0
        while i<len(line):
            if line[i]=='\\':
                i+=2;continue
            if line[i]=='%':
                line=line[:i];break
            i+=1
        lines.append(line)
    return '\n'.join(lines)

def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tex',type=Path);ap.add_argument('pdf',type=Path)
    args=ap.parse_args()
    for p in (args.tex,args.pdf):
        if not p.is_file():
            print(f'FAIL: missing input: {p}',file=sys.stderr);return 2
    if not shutil.which('pdftotext'):
        print('FAIL: pdftotext is required (Poppler utilities).',file=sys.stderr);return 2
    try:
        src=strip_comments(args.tex.read_text(encoding='utf-8'))
        version_match=re.search(r'\\def\\CFBDCTVersion\{([0-9]+(?:\.[0-9]+)+)\}',src)
        date_match=re.search(r'\\date\{Submitted manuscript.*?\\doi\{(10\.5281/zenodo\.\d+)\}',src,re.S)
        if not version_match or not date_match:
            print('FAIL: cannot locate the expected current-release macro and title DOI.',file=sys.stderr);return 2
        ver,doi=version_match.group(1),date_match.group(1)
        proc=subprocess.run(['pdftotext','-layout',str(args.pdf.resolve()),'-'],capture_output=True,timeout=30,check=False)
        if proc.returncode:
            print('FAIL: pdftotext could not parse the PDF: '+proc.stderr.decode(errors='replace'),file=sys.stderr);return 2
        text=proc.stdout.decode('utf-8',errors='replace')
    except (OSError,UnicodeError,subprocess.TimeoutExpired) as exc:
        print(f'FAIL: {exc}',file=sys.stderr);return 2
    first=text.split('\f',1)[0]
    current=re.search(r'Artifact\s+version\s+([\d.]+),\s*(10\.5281/zenodo\.\d+)',first)
    print(f'expected_version: {ver}\nexpected_doi: {doi}')
    if not current:
        print('FAIL: no current artifact identity found on PDF page 1.');return 1
    found_ver,found_doi=current.groups();print(f'pdf_title_version: {found_ver}\npdf_title_doi: {found_doi}')
    ok=True
    if found_ver!=ver:print('FAIL: PDF title version does not match the TeX.');ok=False
    if found_doi!=doi:print('FAIL: PDF title DOI does not match the TeX.');ok=False
    # Check explicit self-describing positions only. Old releases in the history
    # are legitimate and must not be rejected merely because they are mentioned.
    flat=re.sub(r'\s+',' ',text)
    for label,pat in [
        ('current_tree',r'This tree is v([\d.]+), tagged'),
        ('audit_banner',r'artifact(?:_| )version=([\d.]+)'),
        ('availability_tag',r'under tag v([\d.]+), an annotated tag')]:
        hits=re.findall(pat,flat)
        if not hits:
            print(f'FAIL: no {label} field found in PDF.');ok=False
        elif any(v!=ver for v in hits):
            print(f'FAIL: {label} reports {hits}, expected {ver}.');ok=False
        else:print(f'{label}: {ver}')
    print('SUBMISSION PDF IDENTITY CHECK '+('PASSED' if ok else 'FAILED'))
    return 0 if ok else 1

if __name__=='__main__':
    raise SystemExit(main())
