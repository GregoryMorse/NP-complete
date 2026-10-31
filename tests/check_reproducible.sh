#!/bin/sh
# The build must not depend on Python's hash randomisation: build twice with
# different PYTHONHASHSEED values and compare the machine hashes.
set -e
cd "$(dirname "$0")/.."
PYTHONHASHSEED=1 python3 build.py > /tmp/repro1.txt
PYTHONHASHSEED=2 python3 build.py > /tmp/repro2.txt
if cmp -s /tmp/repro1.txt /tmp/repro2.txt; then
    echo "reproducible:"; cat /tmp/repro1.txt
else
    echo "NOT reproducible"; diff /tmp/repro1.txt /tmp/repro2.txt; exit 1
fi
