"""Derive a domain theory from the advanced case notion (ACN) of van Detten,
Schumacher and Leemans, "A Framework for Advanced Case Notions in Object-Centric
Process Mining" (ICPM 2024 Workshops, LNBIP 533, 2025), and generate its run.

A very simple version of their Algorithm 1. ACN marks a type T as diverging on
an activity a when two distinct events of a share an object of T (T is
resource-like at a). Growing a case connected-components style, it follows all
events of an object reached through event e only if the object's type does not
diverge on act(e); objects of diverging types are kept as leaves. Translated
into declarations:

  B_D  = the types ACN ever follows: those not diverging on some activity in
         which they occur. A type diverging on every activity stays a resource.
  Pi_D = ActConn(T1, T2, a) for distinct T1, T2 in B_D co-occurring in an event
         of a, at least one of them not diverging on a: ACN follows the link
         from one to the other in at least one direction.

Not carried over: ACN's choice of a start type by a correctness/simplicity
score (here every identity-bearing type generates wholes), its exclusion of
further objects of the start type, and its lack of determinacy (the derived
Fuse_a instances keep (Det), so the result stays within the schema family).

    python ocel_examples/acn_theory.py SOURCE --out DIR [--format duckdb|facts] \
        [--rename OLD:NEW ...] [--name N] [--run]
"""

from __future__ import annotations

import argparse
import collections
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from ocel_to_datalog import _pair, generate, load_log  # noqa: E402


def derive(triples, activities):
    """Return (identity_types, connections, divergent) for the ACN-derived theory."""
    typ = {o: t for _, t, o in triples}
    objs = collections.defaultdict(set)                  # event -> objects
    for e, _, o in triples:
        objs[e].add(o)

    seen = collections.defaultdict(set)                  # (a, o) -> events of a with o
    for e, os_ in objs.items():
        a = activities.get(e)
        for o in os_:
            seen[a, o].add(e)
    occurs = collections.defaultdict(set)                # a -> types occurring in a
    divergent = collections.defaultdict(set)             # a -> types diverging on a
    for (a, o), es in seen.items():
        occurs[a].add(typ[o])
        if len(es) > 1:
            divergent[a].add(typ[o])

    identity = {t for a, ts in occurs.items() for t in ts - divergent[a]}
    connections = set()
    for e, os_ in objs.items():
        a = activities.get(e)
        ts = sorted({typ[o] for o in os_} & identity)
        for i, t1 in enumerate(ts):
            for t2 in ts[i + 1:]:
                if t1 not in divergent[a] or t2 not in divergent[a]:
                    connections.add((t1, t2, a))
    return sorted(identity), sorted(connections), divergent


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("source")
    ap.add_argument("--out", required=True)
    ap.add_argument("--format", default="duckdb", choices=["duckdb", "facts"])
    ap.add_argument("--rename", action="append", default=[], type=_pair, metavar="OLD:NEW")
    ap.add_argument("--name")
    ap.add_argument("--run", action="store_true", help="also invoke souffle")
    a = ap.parse_args()

    rn = dict(a.rename).get
    e2o, activities = load_log(a.source, a.format)
    if not any(v is not None for v in activities.values()):
        sys.exit("ACN needs activities, and this log has none")
    triples = [(e, rn(t, t), o) for e, t, o in e2o]
    identity, connections, divergent = derive(triples, activities)

    all_types = sorted({t for _, t, _ in triples})
    print(f"identity-bearing: {identity}")
    print(f"resources (diverging on every activity they occur in): "
          f"{sorted(set(all_types) - set(identity))}")
    pairs = collections.Counter((t1, t2) for t1, t2, _ in connections)
    print("ActConn pairs (number of activities): "
          + ", ".join(f"{t1}:{t2} ({n})" for (t1, t2), n in sorted(pairs.items())))

    dl = generate(a.source, identity, connections, a.out, name=a.name, fmt=a.format,
                  renames=dict(a.rename), run=a.run)
    print("wrote", dl)


if __name__ == "__main__":
    main()
