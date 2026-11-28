#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
here=$PWD
[[ -n "$LEAN_BIN" && -n "$LEAN_PATH" ]]
[[ "$("$LEAN_BIN" --version)" == *"4.36.0"*"611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"* ]]
sha256sum -c SHA256SUMS
mkdir -p replay-logs tmp
export TMPDIR="$here/tmp" TMP="$here/tmp" TEMP="$here/tmp"
export LEAN_PATH="$here:$LEAN_PATH"
timeout -k2s 230s bash -c '
set -euo pipefail
for M in WeightedCutDraft WeightedBranchCountsDraft DiagonalWeightedThresholdDraft DiagonalBalancedDraft DiagonalWeightedBalancedDraft DiagonalWeightedAudit; do
  timeout -k1s 35s "$LEAN_BIN" -j1 -M2450 -DwarningAsError=true -o "$M.olean" "$M.lean" 2>&1 | tee "replay-logs/$M.log"
  printf "%s exit=0\n" "$M" >> replay-logs/receipts.log
done
'
grep -Fq "'WidthThree.Diagonal.Labels.balanced_of_diagonal_product' depends on axioms: [propext, Classical.choice, Quot.sound]" replay-logs/DiagonalWeightedAudit.log
! grep -E 'warning:|error:|sorryAx|Lean.ofReduceBool|Lean.trustCompiler' replay-logs/*.log
