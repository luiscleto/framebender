#!/bin/sh
# The gate: every law in LAWS.bend must be proven in PROOF.bend, first by
# bend2, then again by the Lean-proven BendTT kernel (--verdict needs Lean,
# installed with elan into ~/.elan). Also checks the examples and the files.
set -e
cd "$(dirname "$0")"
export BEND_NO_TELEMETRY=1
export PATH="$HOME/.elan/bin:$PATH"
bend examples.bend --check-only 2>&1 | grep -q 'ALL PROOFS CHECK\|TODOs found' || { bend examples.bend --check-only; exit 1; }
bend main.bend --check-only 2>&1 | grep -q 'rely on unsafe' || { bend main.bend --check-only; exit 1; }
bend PROOF.bend --check-only
bend PROOF.bend --verdict
