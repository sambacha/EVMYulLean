#!/usr/bin/env python3
"""Sequential wall-clock elaboration time of Lean files (`lake env lean FILE`), best of N runs.

Used by docs/PROOF_GOLF_REPORT.md. Dependencies must already be built.
Usage: time-modules.py [-n RUNS] FILE...
"""
import subprocess
import sys
import time


def main():
    args = sys.argv[1:]
    runs = 1
    if args[:1] == ["-n"]:
        runs = int(args[1])
        args = args[2:]
    total = 0.0
    for f in args:
        best = None
        for _ in range(runs):
            t = time.monotonic()
            r = subprocess.run(["lake", "env", "lean", f], capture_output=True, text=True)
            dt = time.monotonic() - t
            if r.returncode != 0:
                print(f"{f}\tFAILED\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
                sys.exit(1)
            best = dt if best is None else min(best, dt)
        total += best
        print(f"{f}\t{best:.2f}", flush=True)
    print(f"TOTAL\t{total:.2f}")


if __name__ == "__main__":
    main()
