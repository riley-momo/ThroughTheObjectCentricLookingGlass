"""Generate a Souffle program computing the wholes of a domain theory over an OCEL log.

A domain theory D (paper, Sections 4-5) is given by
  - its identity-bearing types B_D (--identity T), each instantiating IdConn(T) and Sum(T);
  - its declared connections (--connect A:B), each TypeConn(A,B), which instantiates
    Fuse(A,B) when A and B are both identity-bearing, or (--connect A:B@activity)
    ActConn(A,B,a), which instantiates the activity-restricted Fuse_a(A,B).
--fuse0 drops the determinacy conjuncts of every declared instance (Fuse^0), and
--cc declares the connected-components theory D_CC (Section 5.2): every type
identity-bearing, Fuse^0 for every pair of types including each with itself.
The datalog rules are a fixed template; only facts/*.facts change per log/theory.

    python ocel_to_datalog.py LOG.duckdb --out DIR --identity T [--identity T2 ...] \
        [--connect A:B[@ACTIVITY] ...] [--fuse0] [--rename OLD:NEW ...] [--name N] [--run]
    python ocel_to_datalog.py LOG.duckdb --out DIR --cc [--name N] [--run]
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


def load_log(source, fmt="duckdb"):
    """Return (triples, activities): (eid, object_type, object_id) triples, and
    {eid: activity} for every event (activity None when the log has none).

    fmt="duckdb": a DuckDB file with log_e2o(eid, object_type, object_id) and,
    optionally, log_events(eid, activity, ...).
    fmt="facts": a facts/ directory written by an earlier run.
    """
    if fmt == "duckdb":
        import duckdb

        con = duckdb.connect(str(source), read_only=True)
        rows = con.execute(
            "SELECT DISTINCT eid, object_type, object_id FROM log_e2o"
        ).fetchall()
        triples = [(str(e), str(t), str(o)) for e, t, o in rows]
        cols = {c for (c,) in con.execute(
            "SELECT column_name FROM information_schema.columns "
            "WHERE table_name = 'log_events'").fetchall()}
        # events with no participants are absent from log_e2o but are still
        # events (deficient by Thm. 1), so take the event set from log_events
        activities = {e: None for e, _, _ in triples}
        if "eid" in cols:
            q = ("SELECT DISTINCT eid, activity FROM log_events" if "activity" in cols
                 else "SELECT DISTINCT eid, NULL FROM log_events")
            activities.update({str(e): (None if a is None else str(a))
                               for e, a in con.execute(q).fetchall()})
        con.close()
        return triples, activities

    if fmt == "facts":
        d = Path(source)
        rd = lambda f: ([l.rstrip("\n").split("\t") for l in open(d / f) if l.strip()]
                        if (d / f).exists() else [])
        typ = dict(rd("type.facts"))
        triples = [(e, typ[o], o) for o, e in rd("participates.facts")]
        activities = {e: None for (e,) in rd("event.facts")}
        activities.update(dict(rd("occurrence_of.facts")))
        return triples, activities

    raise ValueError(f"unsupported format: {fmt}")


def parse_connect(s):
    """'A:B' -> (A, B, None); 'A:B@activity' -> (A, B, activity)."""
    pair, _, act = s.partition("@")
    a, b = pair.split(":", 1)
    return a, b, (act or None)


def generate(source, identity_types=(), connections=(), out_dir=".", *,
             name=None, fmt="duckdb", renames=None, run=False,
             fuse0=False, cc=False):
    """fuse0: every declared (Fuse) instance drops its determinacy conjuncts
    (Fuse^0). cc: the connected-components theory D_CC -- every type
    identity-bearing, Fuse^0 for every pair of types including T with itself."""
    rn = (renames or {}).get
    e2o, activities = load_log(source, fmt)
    triples = [(e, rn(t, t), o) for e, t, o in e2o]
    log_types = {t for _, t, _ in triples}

    if cc:
        if identity_types or connections:
            raise ValueError("cc declares the whole theory; give no identity/connections")
        identity_types = sorted(log_types)
        connections = [(a, b, None) for a in identity_types for b in identity_types if a <= b]
        fuse0 = True
    identity = {rn(t, t) for t in identity_types}
    if not identity:
        raise ValueError("no identity-bearing types declared")
    connections = [(rn(a, a), rn(b, b), act) for a, b, act in connections]
    unknown = (identity | {t for a, b, _ in connections for t in (a, b)}) - log_types
    if unknown:
        raise ValueError(f"types not in log: {sorted(unknown)}")
    log_acts = {a for a in activities.values() if a is not None}

    fuse, fuse_act = set(), set()
    for a, b, act in connections:
        spec = f"{a}:{b}" + (f"@{act}" if act else "")
        if not {a, b} <= identity:
            # TypeConn/ActConn instantiates (Fuse) only between identity-bearing
            # types; otherwise it yields connection but never identifies wholes
            print(f"warning: --connect {spec} instantiates no (Fuse): "
                  f"{sorted({a, b} - identity)} not identity-bearing", file=sys.stderr)
        elif act is None:
            fuse.add((a, b))
        elif act not in log_acts:
            raise ValueError(f"activity not in log: {act!r}")
        else:
            fuse_act.add((a, b, act))

    out = Path(out_dir)
    facts = out / "facts"
    facts.mkdir(parents=True, exist_ok=True)
    stale = facts / "binding_type.facts"   # input of the pre-Fuse template
    if stale.exists():
        stale.unlink()

    def tsv(fname, rows):
        body = "".join("\t".join(r) + "\n" for r in sorted(set(rows)))
        (facts / fname).write_text(body)

    tsv("event.facts", [(e,) for e in activities])
    tsv("occurrence_of.facts", [(e, a) for e, a in activities.items() if a is not None])
    tsv("participates.facts", [(o, e) for e, _, o in triples])
    tsv("type.facts", [(o, t) for _, t, o in triples])
    tsv("identity_type.facts", [(t,) for t in identity])
    tsv("fuse_type.facts", fuse)
    tsv("fuse_activity.facts", fuse_act)
    tsv("fuse_nodet.facts", [("nodet",)] if fuse0 else [])

    name = name or Path(str(source)).stem
    decls = [f"{a}:{b}" for a, b in sorted(fuse)] + \
            [f"{a}:{b}@{act}" for a, b, act in sorted(fuse_act)]
    header = (
        f"// generated by ocel_to_datalog.py from {name}\n"
        + ("// D_CC: all types identity-bearing, Fuse^0 for every pair\n" if cc else "")
        + f"// identity={sorted(identity)} {'fuse0' if fuse0 else 'fuse'}={decls} "
        f"resources={sorted(log_types - identity)}\n\n"
    )
    dl = out / f"{name}.dl"
    dl.write_text(header + TEMPLATE)

    if run:
        (out / "output").mkdir(exist_ok=True)
        subprocess.run(
            ["souffle", str(dl), "-F", str(facts), "-D", str(out / "output")],
            check=True,
        )
        summary = (out / "output" / "criteria_summary.csv").read_text().splitlines()
        nw, ne, nd, nc = summary[1].split("\t")
        print(f"wholes={nw} events={ne} deficient={nd} convergent={nc}")
    return dl


TEMPLATE = r"""// ---- the log (Section 4) ----
.decl event(e:symbol)
.input event
.decl occurrence_of(e:symbol, a:symbol)
.input occurrence_of
.decl participates(x:symbol, e:symbol)
.input participates
.decl type(x:symbol, t:symbol)
.input type

// ---- the domain theory D ----
.decl identity_type(t:symbol)              // B_D: IdConn(T), Sum(T)
.input identity_type
.decl fuse_type(t1:symbol, t2:symbol)      // Fuse(T1,T2), from TypeConn
.input fuse_type
.decl fuse_activity(t1:symbol, t2:symbol, a:symbol)  // Fuse_a(T1,T2), from ActConn
.input fuse_activity
.decl fuse_nodet(flag:symbol)              // nonempty: Fuse^0, determinacy dropped
.input fuse_nodet

// O_D: the identity-bearing objects
.decl identity_bearing(x:symbol)
identity_bearing(x) :- type(x, t), identity_type(t).
.decl resource(x:symbol)
resource(x) :- type(x, _), !identity_bearing(x).

// identity-bearing types present in each event
.decl has_type(e:symbol, t:symbol)
has_type(e, t) :- participates(x, e), identity_bearing(x), type(x, t).

// ---- (Det): det_T(e) fails iff two objects of T in B_D participate in e ----
.decl indeterminate(e:symbol, t:symbol)
indeterminate(e, t) :- has_type(e, t), participates(x, e), type(x, t),
                       participates(y, e), type(y, t), ord(x) < ord(y).

// ---- (Fuse) / (Fuse_a): the instances applicable at each event ----
// sigma-equality is symmetric, so each declared pair applies in both orders
.decl fuse_decl(t1:symbol, t2:symbol)
fuse_decl(a, b) :- fuse_type(a, b).
fuse_decl(b, a) :- fuse_type(a, b).
.decl fuse_act_decl(t1:symbol, t2:symbol, a:symbol)
fuse_act_decl(t1, t2, a) :- fuse_activity(t1, t2, a).
fuse_act_decl(t2, t1, a) :- fuse_activity(t1, t2, a).

.decl applicable(e:symbol, t1:symbol, t2:symbol)
applicable(e, t1, t2) :- has_type(e, t1), has_type(e, t2), fuse_decl(t1, t2),
                         !indeterminate(e, t1), !indeterminate(e, t2).
applicable(e, t1, t2) :- has_type(e, t1), has_type(e, t2), occurrence_of(e, a),
                         fuse_act_decl(t1, t2, a),
                         !indeterminate(e, t1), !indeterminate(e, t2).
// (Fuse^0): without the determinacy conjuncts (the connected-components theory)
applicable(e, t1, t2) :- fuse_nodet(_), has_type(e, t1), has_type(e, t2),
                         fuse_decl(t1, t2).
applicable(e, t1, t2) :- fuse_nodet(_), has_type(e, t1), has_type(e, t2),
                         occurrence_of(e, a), fuse_act_decl(t1, t2, a).

// determinate co-participation under an applicable instance identifies wholes
.decl fuse(x:symbol, y:symbol)
fuse(x, y) :- applicable(e, t1, t2), participates(x, e), type(x, t1),
              participates(y, e), type(y, t2).

// ---- ~_D: the least equivalence on O_D containing the (Fuse) pairs ----
// fuse is symmetric (each declared pair applies in both orders), so the classes
// of ~_D are the connected components of fuse over O_D. Each class is named by
// its least member (by ordinal): ordinals propagate along fuse, and subsumption
// keeps only the least per object, so no class is enumerated pairwise (classes
// can span most of the log, e.g. under D_CC).
.decl least_member(x:symbol, n:number)
least_member(x, ord(x)) :- identity_bearing(x).
least_member(y, n) :- least_member(x, n), fuse(x, y).
least_member(x, n1) <= least_member(x, n2) :- n2 <= n1.

// ---- the wholes sigma(o) (Lemma 1) ----
// sigma(x) = sigma(y) iff x ~_D y, i.e. iff they have the same least member
.decl object_ord(n:number, x:symbol)
object_ord(ord(x), x) :- identity_bearing(x).
.decl whole_of(x:symbol, w:symbol)
whole_of(x, w) :- least_member(x, n), object_ord(n, w).

.decl execution(w:symbol)
execution(w) :- whole_of(_, w).
// the identity-bearing objects generating the whole: [o]_D
.decl execution_object(w:symbol, x:symbol)
execution_object(w, x) :- whole_of(x, w).
// part(e, sigma(o)) iff e in E[[o]_D]  (Sum(T))
.decl execution_event(w:symbol, e:symbol)
execution_event(w, e) :- whole_of(x, w), participates(x, e).
.decl execution_size(w:symbol, n:number)
execution_size(w, n) :- execution(w), n = count : { execution_event(w, _) }.

// distinct wholes sharing an event (they overlap exactly at convergent events)
.decl overlaps(a:symbol, b:symbol)
overlaps(a, b) :- execution_event(a, e), execution_event(b, e), ord(a) < ord(b).

// ---- correctness criteria (Section 5.1) ----
// Deficient(e) :<=> e is part of no whole
.decl deficient(e:symbol)
deficient(e) :- event(e), !execution_event(_, e).
// the (non-identity-bearing, by Thm. 1) types participating in a deficient event
.decl deficient_type(e:symbol, t:symbol)
deficient_type(e, t) :- deficient(e), participates(x, e), type(x, t).

// Convergent(e) :<=> e is part of two distinct wholes; n = how many
.decl convergent(e:symbol, n:number)
convergent(e, n) :- execution_event(a, e), execution_event(b, e), a != b,
                    n = count : { execution_event(_, e) }.

// Thm. 2: why. (i) "indeterminate", T: det_T(e) fails for T in B_D;
// (ii) "unfused", T1:T2: determinate participants of distinct types in distinct
// wholes with no applicable declared (Fuse) instance at e
.decl convergent_cause(e:symbol, kind:symbol, types:symbol)
convergent_cause(e, "indeterminate", t) :- convergent(e, _), indeterminate(e, t).
convergent_cause(e, "unfused", cat(t1, ":", t2)) :-
    convergent(e, _), has_type(e, t1), has_type(e, t2), ord(t1) < ord(t2),
    !indeterminate(e, t1), !indeterminate(e, t2), !applicable(e, t1, t2),
    participates(x, e), type(x, t1), participates(y, e), type(y, t2),
    whole_of(x, wx), whole_of(y, wy), wx != wy.

.decl criteria_summary(wholes:number, events:number, deficient:number, convergent:number)
criteria_summary(nw, ne, nd, nc) :- nw = count : { execution(_) },
                                    ne = count : { event(_) },
                                    nd = count : { deficient(_) },
                                    nc = count : { convergent(_, _) }.

.output indeterminate
.output execution
.output execution_object
.output execution_event
.output execution_size
.output overlaps
.output deficient
.output deficient_type
.output convergent
.output convergent_cause
.output criteria_summary(headers=true)
"""


def _pair(s):
    a, b = s.split(":", 1)
    return a, b


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("source", help="DuckDB log with a log_e2o(eid, object_type, object_id) "
                                   "table (or a facts/ directory with --format facts)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--identity", action="append", default=[], metavar="TYPE",
                    help="an identity-bearing type (in B_D); repeatable")
    ap.add_argument("--connect", action="append", default=[], type=parse_connect,
                    metavar="A:B[@ACTIVITY]",
                    help="TypeConn(A,B), or ActConn(A,B,ACTIVITY); repeatable")
    ap.add_argument("--fuse0", action="store_true",
                    help="declared Fuse instances drop determinacy (Fuse^0)")
    ap.add_argument("--cc", action="store_true",
                    help="the connected-components theory D_CC: every type identity-"
                         "bearing, Fuse^0 for all pairs (no --identity/--connect)")
    ap.add_argument("--rename", action="append", default=[], type=_pair, metavar="OLD:NEW")
    ap.add_argument("--format", default="duckdb", choices=["duckdb", "facts"])
    ap.add_argument("--name")
    ap.add_argument("--run", action="store_true", help="also invoke souffle")
    a = ap.parse_args()

    dl = generate(a.source, a.identity, a.connect, a.out, name=a.name,
                  fmt=a.format, renames=dict(a.rename), run=a.run,
                  fuse0=a.fuse0, cc=a.cc)
    print("wrote", dl)


if __name__ == "__main__":
    main()
