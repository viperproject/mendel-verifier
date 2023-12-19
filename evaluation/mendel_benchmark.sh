#!/usr/bin/env bash

set -euo pipefail

# Folder in which the script is contained
SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

# Root folder of the project
ROOT_DIR="$SCRIPT_DIR/.."
cd "$ROOT_DIR"

touch "evaluation/benchmark.log"

python3 x.py run-benchmarks \
    --warmup-path="prusti-tests/tests/verify_safe_clients/fail/clients/refcell.rs" \
    --warmup-iterations=10 \
    --bench-iterations=10 \
    --benchmark-csv="evaluation/benchmarked-files.csv" \
    --report-dir="evaluation/" \
    --log-file="evaluation/benchmark.log"

mv evaluation/benchmark*.*.json evaluation/benchmark-result.json

python3 scripts/benchmark_report.py evaluation/benchmark-result.json > evaluation/benchmark-result.txt
