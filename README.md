# Object-Centric Event Log Abstraction and Case Extraction Through Mereotoplogy

Reference implementation of the theory of applied process mereotoplogy from *Through the Object-Centric Looking Glass: Case Notions as Mereotopological Sums*. Given an OCEL (object-centric event log) in DuckDB and a domain theory — which object types are identity-bearing (𝔅) and which pairs of them are connected — it compiles a fixed [Soufflé](https://souffle-lang.github.io/) Datalog program that computes the wholes σ(o) of the theory and evaluates the correctness criteria on them.

## The mereotopology, briefly

Mereotopology is the study of *part-whole* relationships and *connection*. The paper reads both relations off the log directly:

- **Part** (`part`): an event is an atomic part of the whole it belongs
  to, the ordinary sense of "part of a whole" — reflexive (an event is part
  of itself), antisymmetric, transitive.
- **Connection** (`C`): two events are connected when an identity-bearing
  object participates in both (IdConn), or when a declared pair of types
  co-participate (TypeConn) — an `A` in one event and a `B` in the other, tied
  together through a shared event where both show up.
- **Sum/fusion**: each identity-bearing object `o` generates a whole σ(o)
  (Sum(T)). Determinate co-participation under a declared pair identifies
  wholes (Fuse): if an `A` and a `B` meet in an event that has exactly one
  `A` and exactly one `B`, they generate the same whole. σ(o) has as parts the
  events of every object it is identified with, and nothing else (Lemma 1).

Concretely: `--identity order --identity container` makes each order and each container generate a whole. `--connect order:container` adds Fuse(order, container), so an order and a container that meet determinately generate the *same* whole. `--connect A:B@activity` (ActConn) restricts this to events of one activity. A type not declared identity-bearing (a resource, like a forklift or truck) can sit inside a whole's events but never generates or identifies one; a `--connect` naming it instantiates no (Fuse) and the script warns.

## Proofs (`proofs/`)

[proofs/](proofs/) contains machine-checked proofs of the results of Section 5 of the paper. Each one is checked with [Prover9](https://www.cs.unm.edu/~mccune/prover9/), a first-order automated theorem prover, and the consistency of the axioms is checked with Mace4.

```
cd proofs && ./run_proofs.py          # all goals, in dependency order, + Mace4 check
./run_proofs.py t2a_convergence_fwd   # a single goal
```

`PROVER9`, `PROOFTRANS` and `MACE4` select the binaries if they are not on `PATH`. The runner tries Prover9's auto mode first. If that fails, it tries set of support, with the background theory as `usable` (this changes only the search order, not what is proved). It then retries auto mode with the full limit. `FAST` (default 30s) and `TIMEOUT` (default 300s) set the time limits.

### Files

- `axioms.in`: the shared axioms of Section 4 (ground mereology, connection, (Mono), (SumC), (Sum→C), (SumU), (IdConn), (TypeConn)/(ActConn), (Det), (Fuse)/(Fuse_a)/(Fuse⁰), (Sum(T)), ∼_D, D ⊑ D′), plus the definitions of Section 5.1 (`deficient`, `convergent`, `diverges`).
- `<goal>.in`: one claim each. A goal file may contain:
  - `%% INCLUDE: f.in` to add ground facts or extra vocabulary;
  - `%% CITES: g …` to import the goals of earlier, already proved files as assumptions (the paper's "by Lemma 1");
  - its own `formulas(assumptions)` holding the instances of the Least schemata it uses (see below);
  - `%% INSTANCE: φ` (with `%% FOREACH: $V v1 v2 …`) for ground steps over a small example, each proved separately before the main goal.
- `<goal>.proof`: the Prover9 proof transcript(s) (via `prooftrans`). The runner rejects any proof that does not use the goal's denial, i.e. one that only shows the assumptions are inconsistent.
- `example_c1.in`, `example_p3.in`: minimal two-event logs that witness the existence claims Cor. 1 and Prop. 3. Every other result is domain-independent and proved from the schemata alone. Closed-world evaluation of concrete logs, Table 2 included, is the job of the Datalog implementation, not of these proofs.
- `connected_components.in`, `p4_projection.in`: vocabulary for Props. 2 and 4.
- `mace4_consistency.in` / `.model`: a finite model of the axioms and the Least instances, on a log with a genuinely convergent event.

### Encoding

- **Schemata as first-order axioms.** Types and activities are individuals: `T(x)` becomes `ty(x) = T`, and "T ∈ 𝔅_D" becomes `ibt(d,T)`. A schema quantified over types is then one first-order axiom.
- **Several domain theories in one signature.** Everything that depends on the domain theory carries a theory index `d` (`sg(d,o)` = σ_D(o), `sim(d,x,y)` = x ∼_D y, `ib(d,x)` = x ∈ O_D, `decl`, `decla`). This lets results that compare theories (D ⊑ D′) be stated directly. `det(t,e)` is not indexed, because it is defined per type. (Only) is not asserted, since with several theories in one structure it would make every whole of D a whole of D′. No result of Section 5 uses it.
- **Leastness.** "We take the least assignment" is second-order. It is used through two first-order schemata, and each goal file writes out the instances it needs, much as one would instances of an induction schema:
  - (Least_sim[P]): ∼_D is contained in every equivalence P on O_D that contains the (Fuse) pairs;
  - (Least_sg[P]): the same holds for σ-equality, i.e. σ identifies no more objects than (Fuse) forces.

### Claims

| Paper | File(s) | Statement |
|---|---|---|
| Lemma 1 | `l1a_sim_to_sigma`, `l1a_sigma_to_sim` | σ(o₁) = σ(o₂) iff o₁ ∼_D o₂ |
| | `l1b_parts` | part(e, σ(o)) iff e ∈ E[[o]_D] |
| Thm. 1 | `t1a_deficiency` | e is deficient iff none of its participants has a type in 𝔅_D |
| | `t1b_deficiency_only_B` | theories with the same 𝔅 have the same deficient events |
| Thm. 2 | `t2a_convergence_fwd`, `t2a_convergence_bwd` | e is convergent iff it has identity-bearing participants x ≁_D y |
| | `t2b_convergence_sources` | convergent ⇒ (i) det_T(e) fails for some T ∈ 𝔅, or (ii) participants of distinct types with no applicable (Fuse) instance |
| Prop. 1 | `p1_lemma_objects`, `p1_lemma_fuse_instances`, `p1a_monotonicity_sim` | D ⊑ D′ ⇒ ∼_D ⊆ ∼_D′ |
| | `p1b_monotonicity_parts` | D ⊑ D′ ⇒ every event of σ_D(o) is part of σ_D′(o) |
| Thm. 3 | `t3i_…`, `t3ii_…`, `t3iii_…` | (i) deficiency is antitone, (ii) divergence is monotone, (iii) D ⊑ D* ⇒ no divergence |
| Cor. 1 | `c1a_…`, `c1b_…`, `c1c_…` | minimal example: D ⊑ D*, D does not diverge, yet an event is deficient under D |
| Prop. 2 | `p2_lemma_*`, `p2_sim_in_ccomp`, `p2_ccomp_in_sim`, `p2i_cc_parts` | (i) the wholes of D_CC are the connected-component cases |
| | `p2ii_cc_upper_bound` | (ii) every whole of every D lies within a connected-component case |
| | `p2_cc_criteria` | D_CC has no convergent events, and only participant-free deficient ones |
| Prop. 3 | `p3a_…`, `p3b_…` | minimal example: neither D1 nor D2 has deficient or convergent events |
| | `p3c_…`, `p3d_…`, `p3e_…` | D1 puts e₁, e₂ in one whole, while D2 never does (∼_D2 is the identity by leastness) |
| Prop. 4 | `p4i_projection_traces` | (i) ev(σ_G) = ⋃_{o∈G} ev(D[o→o \\ (O∖{o})]) |
| | `p4ii_projection_paths` | (ii) ev(D[o_s→o_e \\ (O∖G)]) ⊆ ev(σ_G) |

Two claims carry extra assumptions, both stated in the files:

- Prop. 1's "every whole of D is part of a whole of D′" is proved at the level of events (E[[o]_D] ⊆ E[[o]_D′], the paper's own proof). Deriving parthood between the wholes themselves would need strong supplementation, which is not among the axioms.
- Prop. 4(i) assumes (Trace): the directly-follows path from an object's first event to its last, using only its own edges, passes through all of Tr(o). This is a fact about finite linear orders, not about the theory.

## Requirements

- [Ontop](https://ontop-vkg.org/), for the virtual knowledge graph mapping of an OCEL log to ground facts.
- [Soufflé](https://souffle-lang.github.io/), to evaluate the generated Datalog program.
- Python 3 to run the scripts, with the `duckdb` package when reading a DuckDB log.

To reproduce the proofs, you also need [Prover9 and Mace4](https://www.cs.unm.edu/~mccune/prover9/) (including `prooftrans`).


## Usage

```
python ocel_to_datalog.py LOG.duckdb --out DIR --identity TYPE [--identity TYPE ...] \
    [--connect A:B[@ACTIVITY] ...] [--rename OLD:NEW ...] [--format duckdb|facts] \
    [--name NAME] [--run]
```

- `LOG.duckdb` — a DuckDB file containing a `log_e2o(eid, object_type,
  object_id)` table (the event-to-object relation of the log, as produced by
  the Ontop mapping of the OCEL 2.0 log) and, optionally, `log_events(eid,
  activity, …)`, which supplies activities and events with no participants.
  With `--format facts`, a `facts/` directory written by an earlier run instead.
- `--out DIR` — output directory; `facts/` and (with `--run`) `output/` are
  created inside it.
- `--identity TYPE` — declares `TYPE` identity-bearing (in 𝔅): IdConn(T) and
  Sum(T), so each of its objects generates a whole (repeatable).
- `--connect A:B` — TypeConn(A, B), instantiating Fuse(A, B) when both are
  identity-bearing. `--connect A:B@ACTIVITY` is ActConn(A, B, a), instantiating
  the activity-restricted Fuse_a(A, B) (repeatable).
- `--rename OLD:NEW` — rename an object type from the log before processing
  (repeatable).
- `--name NAME` — base name for the generated `.dl` file; defaults to the
  source's stem.
- `--run` — also invoke `souffle` on the generated program, write CSV
  results to `DIR/output/`, and print the criteria totals.

This writes `DIR/<name>.dl` (the Datalog program) and `DIR/facts/*.facts`
(the log and the declarations encoded as Soufflé input relations). The Datalog
rules are a fixed template (see `TEMPLATE` in
[ocel_to_datalog.py](ocel_to_datalog.py)) following the schemata of Section 4:
(Det), (Fuse)/(Fuse_a), ∼_D as the least equivalence on identity-bearing
objects containing the (Fuse) pairs (a Soufflé `eqrel`), and σ by Lemma 1.

### Outputs

| File | Columns | Meaning |
|---|---|---|
| `execution.csv` | whole | one row per whole σ(o), named by its least member |
| `execution_object.csv` | whole, object | the identity-bearing objects generating it, [o]_D |
| `execution_event.csv` | whole, event | its parts, E[[o]_D] |
| `execution_size.csv` | whole, n | number of events |
| `overlaps.csv` | whole, whole | distinct wholes sharing an event |
| `indeterminate.csv` | event, type | det_T(e) fails: two or more objects of identity-bearing T |
| `deficient.csv` | event | part of no whole |
| `deficient_type.csv` | event, type | the types participating in a deficient event (none identity-bearing, Thm. 1) |
| `convergent.csv` | event, n | part of n ≥ 2 distinct wholes |
| `convergent_cause.csv` | event, kind, types | Thm. 2: `indeterminate` T (det_T fails), or `unfused` T1:T2 (determinate participants of distinct types in distinct wholes, with no applicable declared Fuse) |
| `criteria_summary.csv` | wholes, events, deficient, convergent | totals, with a header row |

## Examples

[ocel_examples/](ocel_examples/) holds one subfolder per sample log, each with one generated run. The source logs (`mapped_log.duckdb`, the Ontop mapping of each OCEL 2.0 log) are not included because of their size; the generated `facts/` hold everything the runs need:

```
ocel_examples/<log>/
  mapped_log.duckdb       # source OCEL log (not included)
  gen*/                   # one folder per run of ocel_to_datalog.py
    <name>.dl             # generated Soufflé program
    facts/                # generated input facts (.facts files)
    output/               # Soufflé results (.csv), present when run with --run
```

[ocel_examples/regenerate.sh](ocel_examples/regenerate.sh) records the exact domain theory of every run and regenerates them all (each run is regenerated from its `facts/` unless its `mapped_log.duckdb` is present; `PYTHON` then selects an interpreter with `duckdb`). Each `.dl` header also records 𝔅 and the declared (Fuse) pairs.

| Run | 𝔅 | Declared Fuse pairs | Wholes | Events | Deficient | Convergent (cause) |
|---|---|---|---:|---:|---:|---:|
| `bpi17/gen` | application, offer, workflow | application:offer, application:workflow | 1 575 | 23 561 | 0 | 0 |
| `logistics/gen_order` | order, transport_document, container, handling_unit | order:transport_document, transport_document:container (Fig. 1), container:handling_unit | 2 536 | 35 372 | 0 | 691 (indeterminate container; 124 also transport_document) |
| `order_mgmt/gen` | orders, items, packages | orders:items, items:packages | 10 606 | 21 008 | 0 | 9 667 (indeterminate items) |
| `p2p/gen` | purchase_requisition, quotation, purchase_order, goods_receipt, invoice_receipt, payment, material | the 9 pairs that co-occur in the log | 2 550 | 14 671 | 0 | 1 090 (indeterminate material) |

`logistics/gen_order` adds handling units to the Fig. 1 theory. Without them, all 10 553 "Collect Goods" events, in which a handling unit is the only participant, are deficient (Thm. 1). Each handling unit's only other event, "Load Truck", has exactly one container and one handling unit, so Fuse(container, handling_unit) puts every handling unit into its container's whole. Deficiency drops to 0 with the same wholes and the same convergent events.

To time the evaluation, run [ocel_examples/benchmark.py](ocel_examples/benchmark.py) (`souffle` must be on `PATH`). It reports, for each run, the mean ± sample standard deviation of the full `souffle` invocation (parse, load, evaluate, write) over 10 runs, after one discarded warm-up run (`-n`, `--warmup`).
