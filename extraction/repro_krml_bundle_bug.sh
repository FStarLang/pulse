#!/bin/bash
# Reproducer for KaRaMeL issue: Pulse fn functions fail Low* re-check
# due to monomorphization type mismatch between erased type variants.
#
# Bug summary:
#   When a Pulse module (AVLTree, with .fsti) defines a polymorphic data type
#   `tree_t (k:Type) (v:Type)` where `v` is erased, krml's monomorphizer creates
#   two incompatible type instantiations:
#     - node<range, ()>   (from the caller's erased argument)
#     - node<range, any>  (from the callee's internal representation)
#
#   The checker then rejects the function because subtype check fails:
#     option__node__key_any* <=? option__node__key_()*
#   These are different C struct layouts (one has a `void* value` field, the
#   other doesn't).
#
# Impact: 5 Pulse `fn` functions in RangeMap.fst are silently dropped from
#   the C output. Users must provide manual C implementations.
#
# Expected: krml should unify `()` and `any` as the same erased type during
#   monomorphization, producing a single struct type.
#
# Environment:
#   - fstar.exe version: (see output)
#   - krml version: (see output)
#   - Pulse: FStarLang/pulse branch lef/circular_buffer

set -e

PULSE_HOME="${PULSE_HOME:-$HOME/pulse}"
KRML="${KRML:-$HOME/karamel/krml}"
KRMLLIB="${KRMLLIB:-$HOME/karamel/krmllib}"

echo "fstar.exe version: $(fstar.exe --version 2>&1 | head -1)"
echo "krml version: $($KRML -version 2>&1 | head -1)"
echo ""

FSTAR_OPTS="
  --include $PULSE_HOME/out/lib/pulse
  --include $PULSE_HOME/out/lib/pulse/lib
  --include $PULSE_HOME/build/lib.pulse.checked
  --include $PULSE_HOME/build/lib.common.checked
  --include $PULSE_HOME/lib/pulse/lib
  --include $PULSE_HOME/lib/common
  --cache_checked_modules
  --cache_dir /tmp/krml_repro_cache
  --warn_error -321
  --ext optimize_let_vc
  --load_cmxs pulse
"

MODULES="Pulse.Lib.RangeMap Pulse.Lib.RangeMap.Spec Pulse.Lib.AVLTree Pulse.Lib.Spec.AVLTree"

rm -rf /tmp/krml_repro_cache /tmp/krml_repro_output /tmp/krml_repro_c
mkdir -p /tmp/krml_repro_cache /tmp/krml_repro_output /tmp/krml_repro_c

echo "=== Step 1: Verify & extract Pulse modules to .krml ==="
for mod in $MODULES; do
    src="$PULSE_HOME/lib/pulse/lib/${mod}.fst"
    echo "  Verifying $mod..."
    fstar.exe $FSTAR_OPTS "$src" 2>&1 | tail -1
done

for mod in $MODULES; do
    src="$PULSE_HOME/lib/pulse/lib/${mod}.fst"
    echo "  Extracting $mod to .krml..."
    fstar.exe $FSTAR_OPTS --already_cached ',*' \
        --codegen krml --extract_module "$mod" \
        --odir /tmp/krml_repro_output "$src" 2>&1 | tail -1
done

echo ""
echo "=== Step 2: Run krml (expect 5 functions to be dropped) ==="
$KRML -skip-compilation -skip-makefiles -skip-linking \
    -warn-error -2 -warn-error -15 -warn-error -4 -warn-error -26 \
    -warn-error -18 -warn-error -9 -warn-error -17 \
    -tmpdir /tmp/krml_repro_c \
    "$KRMLLIB/.extract/"*.krml \
    /tmp/krml_repro_output/*.krml 2>&1 | grep "Cannot re-check"

echo ""
echo "=== Step 3: Type mismatch detail ==="
$KRML -skip-compilation -skip-makefiles -skip-linking \
    -warn-error -2 -warn-error -15 -warn-error -4 -warn-error -26 \
    -warn-error -18 -warn-error -9 -warn-error -17 \
    -d checker \
    -tmpdir /tmp/krml_repro_c \
    "$KRMLLIB/.extract/"*.krml \
    /tmp/krml_repro_output/*.krml 2>&1 | grep -B1 "Cannot re-check.*range_map_create"

echo ""
echo "=== Root Cause ==="
echo "The AVLTree module (has .fsti) defines:"
echo "  type tree_t (k:Type) (v:Type) = option (node k v)"
echo ""
echo "After Pulse elaboration + monomorphization, krml creates TWO structs:"
echo "  node__range_()  = { key: range; left: option*; right: option* }"
echo "  node__range_any = { key: range; value: void*; left: option*; right: option* }"
echo ""
echo "RangeMap uses node<range, ()> but AVLTree internally uses node<range, any>."
echo "The checker fails because these have different C memory layouts."
echo "krml should unify () and any as the same erased type."
