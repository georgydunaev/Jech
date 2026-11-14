#!/bin/sh
set -e
cd "$(dirname "$0")"
COQC_BIN="$(command -v coqc 2>/dev/null || echo "/usr/bin/coqc")"
"$COQC_BIN" -Q . '' Jech.v
"$COQC_BIN" -Q . '' Part_III.v
"$COQC_BIN" -Q . '' section_mostowski.v
"$COQC_BIN" src/axioms/axInfty.v
"$COQC_BIN" src/axioms/axRep.v
