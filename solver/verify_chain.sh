#!/usr/bin/env bash
set -euo pipefail

# Reconstruct the flag products from source so both binary tables use the same model order.
solver=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
certs="$solver/../certs"
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT

"${CXX:-g++}" -std=c++17 -O3 -fopenmp "$solver/flag_gen.cpp" -o "$work/flags"
"${CXX:-g++}" -std=c++17 -O3 -fopenmp "$solver/flag_gen_ext.cpp" -o "$work/ext"
for order in 5 6; do
    "$work/flags" dump "$order" "$work"
    "$work/ext" "$work/flags_m$order.bin" "$work/ext_m$order.bin"
done

python3 "$solver/verify_cert_independent.py" "$work/flags_m5.bin" \
    "$certs/cert_m5_689_2000.json"
python3 "$solver/verify_ext_cert_independent.py" "$work/flags_m5.bin" "$work/ext_m5.bin" \
    "$certs/cert_m5_tier1_linonly_427_1250_to_689_2000.json"
six=("$certs/cert_m6_css83_sos_3383_10000_to_427_1250.json"
     "$certs/cert_m6_css83_nosos_677_2000_to_427_1250.json"
     "$certs/cert_m6_css83_33827_100000_to_427_1250.json"
     "$certs/cert_m6_css1037_33823_100000_to_33827_100000.json")
PYTHONPATH="$solver" python3 - "$certs/canon_witnesses_m6.json" \
    "$work/flags_m6.bin" "$work/ext_m6.bin" "${six[@]}" <<'PY'
import sys
from fractions import Fraction
from pathlib import Path
from verify_ext_cert_independent import product_table_endpoints
from verify_six_vertex import verify_files

witnesses, flags, extensions, *certificates = map(Path, sys.argv[1:])
verify_files(witnesses, flags, extensions, certificates, Fraction(427, 1250), product_table_endpoints)
PY
