# KaRaMeL Bug: Pulse `fn` using `box` fails Low* re-check

## Problematic Example

`Pulse.Lib.RangeMap.fst` (no `.fsti`) defines functions that use `box` (heap-allocated mutable ref) wrapping an AVL tree from `Pulse.Lib.AVLTree` (has `.fsti`):

```fstar
// AVLTree.fsti — polymorphic tree with erased value parameter
type tree_t (k: Type) (v: Type) = option (node k v)

// RangeMap.fst — uses tree_t with () as the erased value
type range_map_t = box (tree_t range unit)

fn range_map_create (_: unit)
  requires emp
  returns r: range_map_t
  ensures range_map_pred r empty_rm
{
  let ct = AVLTree.create ();
  alloc ct    // Box.alloc — becomes `heap newbuf` in krml AST
}
```

## How to extract

```bash
# 1. Verify & extract to .krml
for mod in Pulse.Lib.AVLTree Pulse.Lib.Spec.AVLTree Pulse.Lib.RangeMap Pulse.Lib.RangeMap.Spec; do
  fstar.exe --codegen krml --extract_module $mod \
    --include $PULSE_HOME/out/lib/pulse --include $PULSE_HOME/out/lib/pulse/lib \
    --include $PULSE_HOME/build/lib.pulse.checked --include $PULSE_HOME/build/lib.common.checked \
    --include $PULSE_HOME/lib/pulse/lib --include $PULSE_HOME/lib/common \
    --cache_checked_modules --cache_dir _cache --odir _output \
    --warn_error -321 --ext optimize_let_vc --load_cmxs pulse \
    $PULSE_HOME/lib/pulse/lib/${mod}.fst
done

# 2. Run krml
krml -skip-compilation -skip-makefiles -skip-linking \
  -warn-error -2 -warn-error -15 -warn-error -4 -warn-error -26 \
  -warn-error -18 -warn-error -9 -warn-error -17 \
  -tmpdir _c_output \
  ~/karamel/krmllib/.extract/*.krml _output/*.krml
```

## What happens

5 functions are silently dropped:

```
Cannot re-check Pulse.Lib.RangeMap.range_map_create as valid Low* and will not extract it.
Cannot re-check Pulse.Lib.RangeMap.range_map_free as valid Low* and will not extract it.
Cannot re-check Pulse.Lib.RangeMap.range_map_contiguous_from as valid Low* and will not extract it.
Cannot re-check Pulse.Lib.RangeMap.range_map_max_endpoint as valid Low* and will not extract it.
Cannot re-check Pulse.Lib.RangeMap.range_map_add as valid Low* and will not extract it.
```

## Root cause

Running with `-d checker` reveals the failing subtype check:

```
option__node__range_any* <=? option__node__range_()*
```

The monomorphizer creates **two incompatible C struct types** for the same logical type:

| Variant | Fields | Origin |
|---------|--------|--------|
| `node__range_()` | `{ key, left, right }` | RangeMap caller — erased value = `()` |
| `node__range_any` | `{ key, value, left, right }` | AVLTree impl — erased value = `any` |

These have different memory layouts (3 vs 4 fields), so the checker correctly rejects the subtype check — but the root problem is that they should have been unified into one type.

## Expected behavior

`()` and `any` should be treated as the same erased type during monomorphization, producing a single struct type. The functions should extract to valid C.
