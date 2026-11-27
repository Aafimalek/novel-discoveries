#!/bin/bash
set -eu
while read -r id module ns codes; do
  gate="Audit_${id}.lean"
  log="audit-${id}.log"
  cat > "$gate" <<END
import AuditArchivedDeclaration
import $module
set_option maxRecDepth 50000
set_option maxHeartbeats 0
audit_loaded_archive $ns.branchFullFormula $ns.branchFullUnsat [$codes]
#print axioms $ns.branchFullUnsat
END
  if ! timeout 50 bash "${CHECK_LEAN:-./check-replay.sh}" "$gate" > "$log" 2>&1; then
    echo "FAILED $id"
    cat "$log"
    exit 1
  fi
  cat "$log"
done < audited-branches.tsv
