#!/bin/sh
# Export each module given in its own exporter process, with a time limit
# ($LIMIT seconds, default 300, import included): a module whose export runs
# over it is skipped and named in work/skipped.txt. Run from the example dir.
LIMIT=${LIMIT:-300}
mkdir -p work
cd exporter
LEAN_PATH=$(lake env printenv LEAN_PATH); export LEAN_PATH
for m in "$@"; do
  rm -f "out/$m.json"
  if perl -e 'alarm shift; exec @ARGV' "$LIMIT" .lake/build/bin/export "$m" 2>&1 | grep -E '^[^ ]+: [0-9]+ declarations|error|exception'; then :; fi
  [ -f "out/$m.json" ] || { echo "skipped $m"; echo "$m" >> ../work/skipped.txt; }
done
