#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if rg -n --glob '*.lean' \
    '(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)' \
    NativeCarryC3Crosswalk NativeCarryC3Crosswalk.lean; then
  echo "static audit failed: local Lean trust escape found" >&2
  exit 1
fi

python3 -m json.tool audit/theorem-registry.json >/dev/null
python3 scripts/check_github_markdown.py
bash -n scripts/audit.sh scripts/static_audit.sh

echo "static audit passed: sources, registry, scripts, and Markdown"
