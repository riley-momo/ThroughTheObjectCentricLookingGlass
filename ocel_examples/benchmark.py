"""Time the Souffle evaluation of each example run: mean +- sample std over N runs.

Each timed run is the full `souffle` invocation (parse, load facts, evaluate,
write outputs) into a scratch directory; warm-up runs are discarded.

    python ocel_examples/benchmark.py [-n 10] [--warmup 1] [RUN_DIR ...]
"""

from __future__ import annotations

import argparse
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent


def time_run(run_dir: Path, n: int, warmup: int) -> list[float]:
    (dl,) = run_dir.glob("*.dl")
    times = []
    with tempfile.TemporaryDirectory() as out:
        cmd = ["souffle", str(dl), "-F", str(run_dir / "facts"), "-D", out]
        for i in range(warmup + n):
            t0 = time.perf_counter()
            subprocess.run(cmd, check=True)
            if i >= warmup:
                times.append(time.perf_counter() - t0)
    return times


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("runs", nargs="*", type=Path,
                    help="run directories (default: every ocel_examples/*/gen*/)")
    ap.add_argument("-n", type=int, default=10, help="timed runs (default 10)")
    ap.add_argument("--warmup", type=int, default=1, help="discarded runs (default 1)")
    a = ap.parse_args()

    runs = a.runs or sorted(p for p in HERE.glob("*/gen*") if any(p.glob("*.dl")))
    print(f"{'run':<24}{'mean (s)':>10}{'std (s)':>10}{'n':>4}")
    for r in runs:
        ts = time_run(r, a.n, a.warmup)
        name = str(r.resolve().relative_to(HERE))
        print(f"{name:<24}{statistics.mean(ts):>10.3f}{statistics.stdev(ts):>10.3f}{len(ts):>4}")


if __name__ == "__main__":
    main()
