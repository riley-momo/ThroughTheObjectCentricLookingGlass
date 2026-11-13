"""Score each example run against its log's reference cases.

For each reference case, take the occurrence (whole) of the run whose events
overlap it best, measured by the Jaccard index |R & W| / |R | W| of the two event
sets. The score of a run is the mean of these best matches over all reference
cases: 1 when every reference case is reproduced exactly by one occurrence, and
lower both when a case is split over several occurrences and when it is merged
into a larger one. Also reported: how many reference cases are matched exactly.

    python ocel_examples/evaluate.py [RUN_DIR ...]

Reference cases come from reference_cases.py (LOG/reference/case_event.tsv).
"""

from __future__ import annotations

import argparse
import collections
from pathlib import Path

HERE = Path(__file__).resolve().parent


def read_tsv(path):
    with open(path) as f:
        return [line.rstrip("\n").split("\t") for line in f if line.strip()]


def score(reference, occurrences):
    """reference, occurrences: dict id -> set of events. Returns (mean Jaccard, exact)."""
    occ_of = collections.defaultdict(list)
    for w, es in occurrences.items():
        for e in es:
            occ_of[e].append(w)
    total, exact = 0.0, 0
    for es in reference.values():
        inter = collections.Counter(w for e in es for w in occ_of[e])
        best = max((n / (len(es) + len(occurrences[w]) - n) for w, n in inter.items()),
                   default=0.0)
        total += best
        exact += best == 1.0
    return total / len(reference), exact


def group(rows):
    d = collections.defaultdict(set)
    for k, v in rows:
        d[k].add(v)
    return d


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("runs", nargs="*", type=Path,
                    help="run directories (default: every ocel_examples/*/gen*/ with a reference)")
    a = ap.parse_args()
    runs = a.runs or sorted(p for p in HERE.glob("*/gen*")
                            if (p / "output" / "execution_event.csv").exists()
                            and (p.parent / "reference" / "case_event.tsv").exists())
    print(f"{'run':<24}{'occurrences':>12}{'overlap':>9}{'exact':>12}")
    refs = {}
    for r in runs:
        r = r.resolve()
        if r.parent not in refs:
            refs[r.parent] = group(read_tsv(r.parent / "reference" / "case_event.tsv"))
        ref = refs[r.parent]
        occ = group(read_tsv(r / "output" / "execution_event.csv"))
        mean, exact = score(ref, occ)
        name = str(r.relative_to(HERE))
        print(f"{name:<24}{len(occ):>12}{mean:>9.3f}{exact:>7}/{len(ref)}")


if __name__ == "__main__":
    main()
