#!/usr/bin/env bash
# Judge Solution against Challenge as Palomar does: the toolchain's own
# `lake comparator`, replaying the proof through Lean's kernel and the bundled
# independent kernels (NanoDa, con-ron). Needs bwrap. Run from formal/.
set -euo pipefail
cd "$(dirname "$0")/.."
prefix=$(lean --print-prefix)
config=$(mktemp)
trap 'rm -f "$config"' EXIT
python3 - "$prefix" "$config" <<'PY'
import json, sys
prefix, dst = sys.argv[1:]
c = json.load(open('comparator.json'))
c['external_kernels'] = {'nanoda': [f'{prefix}/bin/nanoda_bin'],
                         'con-ron': [f'{prefix}/bin/con-ron']}
json.dump(c, open(dst, 'w'), indent=2)
PY
lake build
lake comparator --config "$config"
