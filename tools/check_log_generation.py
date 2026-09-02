#!/usr/bin/env python3
"""check_log_generation.py --- the shipped reference log must be of this script's generation.

    python3 tools/check_log_generation.py

The reference logs are archived from a run and promoted once, when a release is cut.
Promotion is a manual step, and a manual step gets skipped: a review found the shipped
`logs/build_audit.txt` missing two stages the script had gained and recording a
frozen-name count from an earlier generation, while the paper said the log recorded a
complete run of the current tree.  Checksums cannot see this --- they show the log has
not been corrupted since it was shipped, not that it came from this script.

So compare the two directly: every stage the script announces must appear in the
shipped log, and the figures the log carries must be the ones the current apparatus
produces.  A log that predates a change to the script fails here.
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def main():
    script = (ROOT / "build_audit.sh").read_text(encoding="utf-8")
    log_path = ROOT / "logs" / "build_audit.txt"
    if not log_path.exists():
        print(f"LOG GENERATION CHECK FAILED: missing {log_path}", file=sys.stderr); return 1
    log = log_path.read_text(encoding="utf-8", errors="replace")
    ok = True

    stages = re.findall(r'echo "== ([^"]+) =="', script)
    missing = [s for s in stages if f"== {s} ==" not in log]
    print(f"script_stages={len(stages)} missing_from_log={len(missing)}")
    for s in missing:
        print(f"FAIL: the script runs the stage '{s}', which the shipped log does not record",
              file=sys.stderr); ok = False

    # The frozen-name inventory is the figure that moves whenever the list is edited,
    # so it is the sharpest single test that the log is of this generation.
    frozen = len([l for l in (ROOT / "tools" / "frozen_names.txt").read_text(encoding="utf-8").splitlines()
                  if l.strip() and not l.startswith("#")])
    m = re.search(r"frozen_names: (\d+)", log)
    if not m:
        print("FAIL: the shipped log records no frozen-name count", file=sys.stderr); ok = False
    else:
        print(f"frozen_names_in_log={m.group(1)} current={frozen}")
        if int(m.group(1)) != frozen:
            print(f"FAIL: the shipped log records {m.group(1)} frozen names; the list now holds "
                  f"{frozen}, so the log is from an earlier generation", file=sys.stderr); ok = False

    if "BUILD_AUDIT_EXIT=0" not in log:
        print("FAIL: the shipped log does not end in a successful run", file=sys.stderr); ok = False

    print("LOG GENERATION CHECK " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
