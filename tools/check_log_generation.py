#!/usr/bin/env python3
"""check_log_generation.py --- the shipped reference log must be of this script's generation.

    python3 tools/check_log_generation.py [LOG]        # a finished, shipped log
    python3 tools/check_log_generation.py --pending LOG # this run's log, before it ends

★Two operations, deliberately separate.  `--pending` inspects the log the current run
has just written and asks whether it is fit to *become* a reference: every stage once,
in order, no failure line, and the overall marker not yet written.  The default mode
inspects a log that is already finished and shipped, and additionally requires the
marker to be its last line.

Conflating them is what a review caught.  The audit used to write the overall success
marker and then run this check against the *stored* log; when that check failed the
shell exited non-zero, but the run log it had just written still ended in the success
marker, and promoting that log made this check pass.  The exit status and the log
disagreed.  With `--pending` the check reads the log it is about to bless, so it can
run *before* the marker --- and then a failing run leaves no marker at all.

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

def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    pending = False
    if argv and argv[0] == "--pending":
        pending, argv = True, argv[1:]
    script = (ROOT / "build_audit.sh").read_text(encoding="utf-8")
    log_path = Path(argv[0]) if argv else ROOT / "logs" / "build_audit.txt"
    mode = "pending" if pending else "shipped"
    print(f"log_generation_mode: {mode} ({log_path})")
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

    # ★Presence is not order.  A log can name every stage and still be a splice of two
    # runs, or record them in an order the script cannot produce.  Require the stages
    # to appear in the order the script announces them.
    at, disordered = -1, []
    for s in stages:
        i = log.find(f"== {s} ==")
        if i < 0:
            continue
        if i < at:
            disordered.append(s)
        at = i
    if disordered:
        print(f"FAIL: the shipped log records these stages out of the script's order: "
              f"{disordered}", file=sys.stderr); ok = False
    else:
        print(f"stage_order: the {len(stages) - len(missing)} recorded stages are in script order")

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

    # ★Membership is not the verdict.  This used to ask only whether the string
    # "BUILD_AUDIT_EXIT=0" occurred somewhere; a review injected a failure into the
    # last stage, leaving that string in place further up, and the check still passed.
    # The overall marker is now written last, after every stage, so require it to be
    # the log's final content --- and require that no stage below it failed.
    tail = [l for l in log.splitlines() if l.strip()]
    if not tail:
        print("FAIL: the log is empty", file=sys.stderr); ok = False
    elif pending:
        # ★Before the marker is written, it must not be there.  A run that already
        # carries it is not a fresh run log: it is a finished one being re-blessed,
        # or a spliced one.
        if "BUILD_AUDIT_EXIT=0" in log:
            print("FAIL: this run's log already carries the overall success marker "
                  "before the run has finished", file=sys.stderr); ok = False
        elif tail[-1].strip() == "CORE_AUDIT_EXIT=0":
            print("FAIL: this run's log ends at CORE_AUDIT_EXIT=0; the stages after the "
                  "main block are missing", file=sys.stderr); ok = False
        else:
            print("pending_marker: no overall success marker yet, as expected")
    elif tail[-1].strip() != "BUILD_AUDIT_EXIT=0":
        print(f"FAIL: the shipped log does not end with the overall success marker; its "
              f"last line is {tail[-1].strip()[:80]!r}", file=sys.stderr); ok = False
    else:
        print("terminal_marker: BUILD_AUDIT_EXIT=0 is the last line")

    # ★Each stage exactly once.  A log assembled from two runs can contain every stage,
    # in order, and still be two runs.
    dup = [st for st in stages if log.count(f"== {st} ==") > 1]
    if dup:
        print(f"FAIL: these stages are recorded more than once: {dup}", file=sys.stderr)
        ok = False

    # A stage that failed says so in its own output.  An incomplete or failed run must
    # never be promoted to the shipped reference log, whatever its final line says.
    bad = [l for l in log.splitlines()
           if l.startswith("FAIL") or l.startswith("MISS")
           or l.rstrip().endswith("CHECK FAILED") or "AUDIT FAILED" in l]
    if bad:
        print(f"FAIL: the log records {len(bad)} failure line(s); the first is "
              f"{bad[0].strip()[:100]!r}", file=sys.stderr); ok = False
    else:
        print("failure_lines: 0")

    label = "PENDING LOG CHECK" if pending else "LOG GENERATION CHECK"
    print(label + " " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
