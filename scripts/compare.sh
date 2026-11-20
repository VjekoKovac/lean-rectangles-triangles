#!/usr/bin/env bash
# Use Lean Comparator and the independent NanoDa kernel bundled in Lean 4.35.
set -euo pipefail
cd "$(dirname "$0")/.."
source_config=${1:-comparator.json}
local_config=$(mktemp)
trap 'rm -f "$local_config"' EXIT
python3 - "$source_config" "$local_config" "$(lean --print-prefix)/bin" <<'PY'
import json
from pathlib import Path
import sys
source, destination, binaries = map(Path, sys.argv[1:])
cfg = json.loads(source.read_text())
if set(cfg["permitted_axioms"]) != {"propext", "Classical.choice", "Quot.sound"}:
    raise SystemExit("Unexpected axiom allowlist")
cfg.pop("enable_nanoda", None)
cfg["external_kernels"] = {"nanoda": [str(binaries / "nanoda_bin")]}
destination.write_text(json.dumps(cfg))
PY
lake comparator --config "$local_config"
