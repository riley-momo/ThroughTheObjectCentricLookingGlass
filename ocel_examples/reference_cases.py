"""Build reference cases for an example log, independent of any domain theory.

For the simulated logs (logistics, order_mgmt, p2p), a reference case is a root
object together with every object reachable from it through the composition
relations the simulator recorded as qualified object-to-object relations in the
published OCEL 2.0 file; relations to shared resources are not followed. The
domain theories never read these relations: they see only event participation.
For bpi17, a reference case is an original BPI Challenge 2017 case, carried in
the OCEL log as its Application object.

The events of a reference case are the events in which one of its objects
participates. The result is written as `reference/case_event.tsv` (case, event).

    python ocel_examples/reference_cases.py LOG [--sqlite PUBLISHED.sqlite]

LOG is one of logistics, order_mgmt, p2p, bpi17. The published logs (OCEL 2.0
SQLite) are on Zenodo: logistics 10.5281/zenodo.8428084 (ContainerLogistics.sqlite),
order_mgmt 10.5281/zenodo.8428112 (order-management.sqlite), p2p
10.5281/zenodo.8412920 (ocel2-p2p.sqlite).
"""

from __future__ import annotations

import argparse
import collections
import sqlite3
from pathlib import Path

HERE = Path(__file__).resolve().parent

# root type, and the composition qualifiers followed from parent to part:
# "fwd" follows source -> target, "rev" follows target -> source.
SPECS = {
    "logistics": dict(
        run="gen_order",
        root="Customer Order",
        follow={"TD for CO": "fwd", "CR for TD": "rev", "CR contains HU": "fwd"},
        # not followed: "TR loads CR" (trucks), "* VH for TD" (vehicles)
    ),
    "order_mgmt": dict(
        run="gen",
        root="orders",
        follow={"comprises": "fwd", "contains": "rev"},
        # not followed: "places" (customers), "is a" (products), employee relations
    ),
    "p2p": dict(
        run="gen",
        root="purchase_requisition",
        follow={
            "Quotation of PR": "fwd", "Purchase Order of Quotation": "fwd",
            "Good Receipts of Purchase Order": "rev",
            "Invoice Receipts of Purchase Order": "fwd", "Invoice Receipt of Goods Receipt": "fwd",
            "order_pm": "fwd", "goods_receipt_pm": "fwd", "invoice_receipt_pm": "fwd",
            "assigned_materials of PR": "fwd", "Materials of Quotation": "fwd",
            "Materials of Purchase Order": "fwd", "Materials of Goods Receipt": "fwd",
        },
        # purchase orders without a quotation would be further roots
        orphan=("purchase_order", "Purchase Order of Quotation"),
    ),
    "bpi17": dict(run="gen", root_local="application"),
}


def read_tsv(path):
    with open(path) as f:
        return [line.rstrip("\n").split("\t") for line in f if line.strip()]


def simulated_cases(spec, sqlite_path):
    db = sqlite3.connect(f"file:{sqlite_path}?mode=ro", uri=True)
    types = dict(db.execute("SELECT ocel_id, ocel_type FROM object"))
    o2o = db.execute("SELECT ocel_source_id, ocel_qualifier, ocel_target_id FROM object_object").fetchall()
    down = collections.defaultdict(set)
    for s, q, t in o2o:
        d = spec["follow"].get(q)
        if d == "fwd":
            down[s].add(t)
        elif d == "rev":
            down[t].add(s)
    roots = sorted(o for o, t in types.items() if t == spec["root"])
    if "orphan" in spec:
        otype, qual = spec["orphan"]
        linked = {t for s, q, t in o2o if q == qual}
        roots += sorted(o for o, t in types.items() if t == otype and o not in linked)
    cases = {}
    for r in roots:
        seen, stack = {r}, [r]
        while stack:
            for y in down[stack.pop()]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        cases[r] = seen
    return cases


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("log", choices=sorted(SPECS))
    ap.add_argument("--sqlite", help="published OCEL 2.0 SQLite file (simulated logs)")
    a = ap.parse_args()
    spec = SPECS[a.log]
    facts = HERE / a.log / spec["run"] / "facts"
    local_type = dict(read_tsv(facts / "type.facts"))
    events_of = collections.defaultdict(set)
    for x, e in read_tsv(facts / "participates.facts"):
        events_of[x].add(e)

    if "root_local" in spec:
        cases = {o: {o} for o, t in local_type.items() if t == spec["root_local"]}
    else:
        if not a.sqlite:
            ap.error(f"{a.log} needs --sqlite (the published log)")
        cases = simulated_cases(spec, a.sqlite)

    out = HERE / a.log / "reference"
    out.mkdir(exist_ok=True)
    rows = sorted((c, e) for c, objs in cases.items()
                  for e in set().union(*(events_of[o] for o in objs if o in events_of)))
    with open(out / "case_event.tsv", "w") as f:
        f.writelines(f"{c}\t{e}\n" for c, e in rows)
    n_cases = len({c for c, _ in rows})
    n_events = len({e for _, e in rows})
    all_events = len(read_tsv(facts / "event.facts"))
    print(f"{a.log}: {n_cases} reference cases covering {n_events}/{all_events} events "
          f"-> {out / 'case_event.tsv'}")


if __name__ == "__main__":
    main()
