#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
here="$PWD"
[[ -n "$LEAN_BIN" && "$LOCK_PATH" = /* ]]
[[ "$("$LEAN_BIN" --version)" == *"4.36.0"*"611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"* ]]
sha256sum -c SHA256SUMS
mkdir -p tmp replay-logs
export TMPDIR="$here/tmp" TMP="$here/tmp" TEMP="$here/tmp" LEAN_PATH="$here"
exec 9>"$LOCK_PATH"
flock -n 9
timeout -k1s 20s bash -c '
set -euo pipefail
for M in PairwiseGateEnvelopeDraft PairwiseGateEnvelopeAudit; do
  "$LEAN_BIN" -j1 -M600 -DwarningAsError=true -o "$M.olean" "$M.lean" 2>&1 | tee "replay-logs/$M.log"
  printf "%s exit=0\n" "$M" >> replay-logs/receipts.log
done
'
for name in pairwise_envelope_rank_le pairwise_envelope_weights_iff pairwise_budget_of_one_small; do
  grep -Fq "'WidthThree.Diagonal.$name' depends on axioms: [propext, Quot.sound]" replay-logs/PairwiseGateEnvelopeAudit.log
done
! grep -E 'warning:|error:|sorryAx|Lean.ofReduceBool|Lean.trustCompiler' replay-logs/*.log
