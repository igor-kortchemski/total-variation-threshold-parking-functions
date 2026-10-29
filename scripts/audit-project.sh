#!/usr/bin/env bash
# Implementation axiom closure, full Lean-kernel replay and negative control.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
python3 scripts/prepare-audit.py
mkdir -p .scratch/validation
probe=".scratch/validation/AuditProject.lean"
if [ -e "$probe" ]; then echo "Temporary probe already exists: $probe" >&2; exit 2; fi
cp scripts/audit_project.lean.in "$probe"
trap 'rm -f "$probe"' EXIT
scripts/compile-lock.sh lake env lean --run "$probe"
