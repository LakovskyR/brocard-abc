#!/bin/sh
# Rebuild every computed artifact and check it against the committed copy.
# Usage: sh reproduce.sh    (set PYTHON=python if python3 is not on PATH)
set -eu
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
tmp=$(mktemp -d)

$PY code/witness_certificates.py --limit 1038 --output "$tmp/w.jsonl" --stats "$tmp/w.stats.json" > /dev/null
cmp "$tmp/w.jsonl" certificates/witnesses_1_1038.jsonl
$PY code/verify_certificates.py certificates/witnesses_1_1038.jsonl
$PY code/abc_bound_check.py
$PY code/zhou_route_check.py > /dev/null
$PY code/zhou_route_check.py --verify-output

$PY - <<'PYEOF'
import hashlib
for line in open("SHA256SUMS"):
    digest, path = line.split()
    assert hashlib.sha256(open(path, "rb").read()).hexdigest() == digest, path
print("certificate and outputs match SHA256SUMS")
PYEOF

if command -v lake > /dev/null; then
    cd lean
    lake exe cache get
    lake build
    lake env lean Brocard/Axioms.lean | tee "$tmp/axioms.txt"
    if grep -q sorryAx "$tmp/axioms.txt"; then echo "sorryAx found"; exit 1; fi
    echo "Lean build passed; no theorem depends on sorryAx"
else
    echo "lake not found: Lean build skipped (see README)"
fi
