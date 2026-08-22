#!/usr/bin/env python3
"""Validate one Lean dependency report per registered theorem."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REGISTRY_PATHS = [
    ROOT / "audit/theorem-registry.json",
    ROOT / "audit/completed-tfvd-green-intertwining-theorem-registry.json",
]


def fail(message: str) -> None:
    raise SystemExit(f"foundational dependency check failed: {message}")


if len(sys.argv) != 2:
    fail("usage: check_axiom_output.py AXIOM_OUTPUT")

output = Path(sys.argv[1]).read_text()
expected: list[str] = []
for registry_path in REGISTRY_PATHS:
    registry = json.loads(registry_path.read_text())
    expected.extend(entry["qualified"] for entry in registry["theorems"])

pattern = re.compile(
    r"'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*?)\])",
    re.DOTALL,
)
matches = list(pattern.finditer(output))
names = [match.group(1) for match in matches]
if names != expected:
    fail("output declarations differ from the ordered theorem registries")

for match in matches:
    raw = match.group(3)
    dependencies = set() if raw is None else {
        item.strip()
        for item in raw.replace("\n", " ").split(",")
        if item.strip()
    }
    unexpected = dependencies - ALLOWED
    if unexpected:
        fail(
            f"{match.group(1)} uses non-allowlisted dependencies: "
            f"{sorted(unexpected)}"
        )

print(f"foundational dependency check passed: {len(matches)} theorem reports")
