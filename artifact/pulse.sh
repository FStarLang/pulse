#!/bin/bash

ROOT=$(dirname $0)

# Execute F* including the path to the everything needed.
exec \
  fstar.exe \
  --query_cache \
  --z3version 4.13.3 \
  --include "$ROOT/out/lib/pulse" \
  --include "$ROOT/share/pulse/examples" \
  --include "$ROOT/share/pulse/examples/by-example" \
  --include "$ROOT/share/pulse/examples/parallel" \
  --include "$ROOT/share/pulse/examples/dice" \
  --include "$ROOT/share/pulse/examples/dice/cbor" \
  --include "$ROOT/share/pulse/examples/dice/dpe" \
  --include "$ROOT/share/pulse/examples/dice/l0" \
  --include "$ROOT/share/pulse/examples/dice/engine" \
  --include "$ROOT/share/pulse/examples/dice/external" \
  --include "$ROOT/share/pulse/examples/dice/external/hacl" \
  --include "$ROOT/share/pulse/examples/dice/cbor" \
  "$@"
