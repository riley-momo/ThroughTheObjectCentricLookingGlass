#!/usr/bin/env bash
# Regenerate every example run: the exact domain theory of each is recorded here.
#   PYTHON  interpreter with duckdb installed      (default: python)
#   RUN     extra flag for ocel_to_datalog.py      (default: --run, needs souffle on PATH)
# A log whose mapped_log.duckdb is absent is regenerated from its existing facts/.
set -euo pipefail
cd "$(dirname "$0")"
PYTHON=${PYTHON:-python}
RUN=${RUN---run}

gen() {  # gen LOG RUN_DIR NAME ARGS...
  local log=$1 dir=$2 name=$3; shift 3
  local src=(--format duckdb "$log/mapped_log.duckdb")
  [[ -f $log/mapped_log.duckdb ]] || src=(--format facts "$log/$dir/facts")
  echo "== $log/$dir"
  $PYTHON ../ocel_to_datalog.py "${src[@]}" --out "$log/$dir" --name "$name" $RUN "$@"
}

gen bpi17 gen bpi17 \
  --identity application --identity offer --identity workflow \
  --connect application:offer --connect application:workflow

# the paper's running example theory (Fig. 1), plus handling units: without
# them every "Collect Goods" event (a handling unit alone) is deficient
gen logistics gen_order logistics_order --rename customer_order:order \
  --identity order --identity transport_document --identity container \
  --identity handling_unit \
  --connect order:transport_document --connect transport_document:container \
  --connect container:handling_unit

gen order_mgmt gen order_mgmt \
  --identity orders --identity items --identity packages \
  --connect orders:items --connect items:packages

gen p2p gen p2p \
  --identity purchase_requisition --identity quotation --identity purchase_order \
  --identity goods_receipt --identity invoice_receipt --identity payment --identity material \
  --connect purchase_requisition:quotation --connect purchase_requisition:material \
  --connect quotation:purchase_order --connect purchase_order:goods_receipt \
  --connect purchase_order:invoice_receipt --connect purchase_order:payment \
  --connect goods_receipt:invoice_receipt --connect goods_receipt:payment \
  --connect invoice_receipt:payment
