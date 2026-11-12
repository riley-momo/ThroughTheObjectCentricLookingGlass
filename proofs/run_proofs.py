#!/usr/bin/env python3
"""Re-run every proof in this directory with Prover9 and regenerate the
.proof transcripts, then check consistency with Mace4.

    ./run_proofs.py                 # everything, in dependency order
    ./run_proofs.py t2b_convergence_sources p3b_dr_no_convergence

Each goal file is run as  axioms.in + INCLUDEs + CITEd goals + the file.
Directives (comment lines in the goal file):

  %% INCLUDE: f.in g.in     concatenate these files (ground facts, vocabulary)
  %% CITES: name ...        import the goals of name.in as assumptions; name
                            must have been proved earlier in ORDER
  %% FOREACH: $V a b c      expand INSTANCE lines containing $V, once per value
  %% INSTANCE: formula      a ground sub-goal, proved on its own before the
                            file's main goal; every proved instance is
                            available to later instances and the main goal

Search strategy: Prover9's auto mode first; if that fails, set of support
(background theory as `usable`, so only clauses descending from the goal's
denial are selected); then auto mode again with the full time limit.  The
strategy only changes the search order, not what is proved from what.

A proof that does not use the goal's denial means the assumptions are
inconsistent; it is reported as VACUOUS and counts as a failure.

Environment: PROVER9, PROOFTRANS, MACE4 (binaries), TIMEOUT (seconds for the
last attempt, default 300), FAST (seconds for the first two, default 30).
"""
import os, re, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROVER9 = os.environ.get("PROVER9", "prover9")
PROOFTRANS = os.environ.get("PROOFTRANS", "prooftrans")
MACE4 = os.environ.get("MACE4", "mace4")
TIMEOUT = int(os.environ.get("TIMEOUT", 300))
FAST = int(os.environ.get("FAST", 30))

ORDER = """
l1a_sim_to_sigma l1a_sigma_to_sim l1b_parts
t1a_deficiency t1b_deficiency_only_B
t2a_convergence_fwd t2a_convergence_bwd t2b_convergence_sources
p1_lemma_objects p1_lemma_fuse_instances p1a_monotonicity_sim p1b_monotonicity_parts
t3i_tradeoff_deficiency t3ii_tradeoff_divergence t3iii_no_divergence_below
c1a_below_intended c1b_no_divergence c1c_deficient
p2_lemma_fuse_adjacent p2_sim_in_ccomp p2_lemma_adjacent_fuse p2_lemma_sim_closed
p2_ccomp_in_sim p2i_cc_parts p2ii_cc_upper_bound p2_cc_criteria
p3a_no_deficiency p3b_no_convergence p3c_d1_one_whole p3d_d2_identity p3e_d2_separate
p4i_projection_traces p4ii_projection_paths
""".split()

GOALS_RE = re.compile(r"^formulas\(goals\)\.\n(.*?)^end_of_list\.\n", re.S | re.M)


def directives(text, key):
    return [m.group(1).strip() for m in re.finditer(rf"^%% {key}:(.*)$", text, re.M)]


def goal_body(name):
    m = GOALS_RE.search((HERE / f"{name}.in").read_text())
    return m.group(1)


def instances(text):
    insts = directives(text, "INSTANCE")
    for spec in directives(text, "FOREACH"):
        var, *vals = spec.split()
        expanded = []
        for i in insts:
            expanded += [i.replace(var, v) for v in vals] if var in i else [i]
        insts = expanded
    return insts


def background(text, proved_instances):
    parts = [(HERE / "axioms.in").read_text()]
    for inc in " ".join(directives(text, "INCLUDE")).split():
        parts.append((HERE / inc).read_text())
    for c in " ".join(directives(text, "CITES")).split():
        parts.append(f"formulas(assumptions).  % cited: {c}\n{goal_body(c)}end_of_list.\n")
    # the goal file itself, minus its goals
    parts.append(GOALS_RE.sub("", text))
    if proved_instances:
        parts.append("formulas(assumptions).  % proved instances\n"
                     + "".join(f"  {i}.\n" for i in proved_instances) + "end_of_list.\n")
    return "".join(parts)


def prove(bg, goal_text):
    """Try the strategies in turn; return (transcript, strategy, seconds) or None."""
    for strategy, secs in (("auto", FAST), ("sos", FAST), ("auto", TIMEOUT)):
        src = bg if strategy == "auto" else bg.replace(
            "formulas(assumptions).", "formulas(usable).")
        problem = f"assign(max_seconds, {secs}).\n{src}formulas(goals).\n{goal_text}end_of_list.\n"
        out = subprocess.run([PROVER9], input=problem, capture_output=True, text=True).stdout
        if "THEOREM PROVED" not in out:
            continue
        proof = out[out.find("== PROOF =="):out.find("end of proof")]
        if not re.search(r"\[(deny|goal)", proof):
            return ("VACUOUS", strategy, 0)
        t = re.search(r"% Proof 1 at ([0-9.]+)", out)
        trans = subprocess.run([PROOFTRANS], input=out, capture_output=True, text=True).stdout
        return (trans, strategy, float(t.group(1)) if t else 0.0)
    return None


def run(name):
    path = HERE / f"{name}.in"
    if not path.exists():
        return "MISSING", ""
    text = path.read_text()
    done, transcripts, total = [], [], 0.0
    steps = [(i, f"  {i}.\n") for i in instances(text)] + [(None, goal_body(name))]
    for label, goal in steps:
        r = prove(background(text, done), goal)
        what = label or "main goal"
        if r is None:
            return "FAILED", f"on {what}"
        trans, strategy, secs = r
        if trans == "VACUOUS":
            return "VACUOUS", f"on {what}: assumptions inconsistent"
        transcripts.append(f"%%%%%%%%%% {name}: {what}  [strategy: {strategy}]\n{trans}")
        total += secs
        if label:
            done.append(label)
    (HERE / f"{name}.proof").write_text("\n".join(transcripts))
    n = len(steps)
    return "PROVED", f"({n} step{'s' if n > 1 else ''}, {total:.2f}s)"


def mace4_check():
    src = (HERE / "axioms.in").read_text() + (HERE / "mace4_consistency.in").read_text()
    out = subprocess.run([MACE4, "-t", "300"], input=src, capture_output=True, text=True).stdout
    (HERE / "mace4_consistency.model").write_text(out)
    return "Exiting with 1 model" in out


def main():
    names = [a.removesuffix(".in") for a in sys.argv[1:]] or ORDER
    ok = True
    for name in names:
        start = time.time()
        status, info = run(name)
        if status != "PROVED":
            ok = False
            (HERE / f"{name}.proof").unlink(missing_ok=True)
        print(f"{name:34s} {status:8s} {info}   [wall {time.time() - start:.0f}s]", flush=True)
    if not sys.argv[1:]:
        found = mace4_check()
        ok &= found
        print(f"{'mace4_consistency':34s} {'MODEL' if found else 'NO MODEL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
