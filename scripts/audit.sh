#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

bash scripts/static_audit.sh
lake build --wfail NativeCarryC3Crosswalk
lake build --wfail NativeCarryC3Crosswalk.Audit
lake build --wfail NativeCarryC3Crosswalk.CompletedTfvdGreenIntertwiningAudit

audit_output="$(mktemp)"
trap 'rm -f "$audit_output"' EXIT
{
  lake env lean NativeCarryC3Crosswalk/Audit.lean
  lake env lean NativeCarryC3Crosswalk/CompletedTfvdGreenIntertwiningAudit.lean
} 2>&1 | tee "$audit_output"
python3 scripts/check_axiom_output.py "$audit_output"

echo "kernel audit passed"
