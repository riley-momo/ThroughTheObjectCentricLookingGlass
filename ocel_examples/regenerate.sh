#!/usr/bin/env bash
# Regenerate every example run: the exact domain theory of each is recorded here.
#   PYTHON  interpreter with duckdb installed      (default: python)
#   RUN     extra flag for ocel_to_datalog.py      (default: --run, needs souffle on PATH)
# A log whose mapped_log.duckdb is absent is regenerated from existing facts/
# (the run's own, or else another run's of the same log: the log facts are shared).
#
# Each log has its domain theory (gen*) and two baselines: gen_flat flattens the
# log on one object type (B = {T}, no pairs: each object of T is a case), and
# gen_cc is the connected-components theory D_CC (Section 5.2). gen_acn is the
# theory derived from the advanced case notion of van Detten et al. (acn_theory.py).
set -euo pipefail
cd "$(dirname "$0")"
PYTHON=${PYTHON:-python}
RUN=${RUN---run}

gen() {  # gen LOG RUN_DIR NAME ARGS...
  local log=$1 dir=$2 name=$3; shift 3
  local src=(--format duckdb "$log/mapped_log.duckdb")
  if [[ ! -f $log/mapped_log.duckdb ]]; then
    local facts=$log/$dir/facts
    [[ -f $facts/participates.facts ]] || facts=$(ls -d "$log"/gen*/facts | head -n 1)
    src=(--format facts "$facts")
  fi
  echo "== $log/$dir"
  $PYTHON "${SCRIPT:-../ocel_to_datalog.py}" "${src[@]}" --out "$log/$dir" --name "$name" $RUN "$@"
}
acn() {  # acn LOG NAME ARGS...: the ACN-derived theory (acn_theory.py), needs activities
  SCRIPT=acn_theory.py gen "$1" gen_acn "$2" "${@:3}"
}

gen bpi17 gen bpi17 \
  --identity application --identity offer --identity workflow \
  --connect application:offer --connect application:workflow
gen bpi17 gen_flat bpi17_flat --identity application
gen bpi17 gen_cc bpi17_cc --cc
acn bpi17 bpi17_acn

# the paper's running example theory (Fig. 1), plus handling units: without
# them every "Collect Goods" event (a handling unit alone) is deficient
gen logistics gen_order logistics_order --rename customer_order:order \
  --identity order --identity transport_document --identity container \
  --identity handling_unit \
  --connect order:transport_document --connect transport_document:container \
  --connect container:handling_unit
gen logistics gen_flat logistics_flat --rename customer_order:order --identity container
gen logistics gen_cc logistics_cc --rename customer_order:order --cc
acn logistics logistics_acn --rename customer_order:order

gen order_mgmt gen order_mgmt \
  --identity orders --identity items --identity packages \
  --connect orders:items --connect items:packages
gen order_mgmt gen_flat order_mgmt_flat --identity orders
gen order_mgmt gen_cc order_mgmt_cc --cc
acn order_mgmt order_mgmt_acn

gen p2p gen p2p \
  --identity purchase_requisition --identity quotation --identity purchase_order \
  --identity goods_receipt --identity invoice_receipt --identity payment --identity material \
  --connect purchase_requisition:quotation --connect purchase_requisition:material \
  --connect quotation:purchase_order --connect purchase_order:goods_receipt \
  --connect purchase_order:invoice_receipt --connect purchase_order:payment \
  --connect goods_receipt:invoice_receipt --connect goods_receipt:payment \
  --connect invoice_receipt:payment
gen p2p gen_flat p2p_flat --identity purchase_order
gen p2p gen_cc p2p_cc --cc
acn p2p p2p_acn
