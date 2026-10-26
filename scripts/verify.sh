#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=1

echo "== lake build =="
lake build

for c in check_no_forbidden check_dependencies check_coverage check_docstring_verbatim check_import_dag check_sorry check_axioms check_zones; do
  echo "== $c =="
  python "scripts/$c.py"
done

python scripts/tex_extract.py --check
echo "== gen_lean --check =="
python scripts/gen_lean.py --check

echo "all checks passed"
