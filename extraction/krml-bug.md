# KaRaMeL Bug: Monomorphization mismatch for erased type parameter

## Minimal Example (`TestKrmlBug.fst`)

```fstar
module TestKrmlBug
#lang-pulse
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module AVL = Pulse.Lib.AVLTree

fn my_create (_u: unit)
  requires emp
  returns r: AVL.tree_t SZ.t unit
  ensures AVL.is_tree r Pulse.Lib.Spec.AVLTree.Leaf
{
  AVL.create SZ.t unit
}
```

## Steps to reproduce

```bash
PULSE_HOME=~/pulse

# 1. Extract TestKrmlBug + AVLTree deps to .krml
fstar.exe TestKrmlBug.fst \
  --include $PULSE_HOME/out/lib/pulse --include $PULSE_HOME/out/lib/pulse/lib \
  --include $PULSE_HOME/build/lib.pulse.checked --include $PULSE_HOME/build/lib.common.checked \
  --include $PULSE_HOME/lib/pulse/lib --include $PULSE_HOME/lib/common \
  --cache_checked_modules --cache_dir _cache --odir _output \
  --warn_error -321 --ext optimize_let_vc --load_cmxs pulse \
  --codegen krml --extract_module TestKrmlBug

for mod in Pulse.Lib.AVLTree Pulse.Lib.Spec.AVLTree; do
  fstar.exe $PULSE_HOME/lib/pulse/lib/${mod}.fst \
    --include $PULSE_HOME/out/lib/pulse --include $PULSE_HOME/out/lib/pulse/lib \
    --include $PULSE_HOME/build/lib.pulse.checked --include $PULSE_HOME/build/lib.common.checked \
    --include $PULSE_HOME/lib/pulse/lib --include $PULSE_HOME/lib/common \
    --cache_checked_modules --cache_dir _cache --odir _output \
    --warn_error -321 --ext optimize_let_vc --load_cmxs pulse \
    --codegen krml --extract_module $mod
done

# 2. Run krml
krml -skip-compilation -skip-makefiles -skip-linking \
  -warn-error -2-4-9-15-17-18-26 \
  ~/karamel/krmllib/.extract/*.krml _output/*.krml
```

## Observed

```
Cannot re-check TestKrmlBug.my_create as valid Low* and will not extract it.
```

With `-d checker`, the failing subtype check:

```
option__node__size_t_any* <=? option__node__size_t_()*
```

## Root cause

`AVLTree.fsti` declares `tree_t (k v : Type)` with erased value `v`.
After monomorphization, krml produces **two incompatible structs**:

| Variant | Fields | Origin |
|---------|--------|--------|
| `node__size_t_()` | `{ key, left, right }` | Caller instantiates `v = unit` → erased to `()` |
| `node__size_t_any` | `{ key, value, left, right }` | AVLTree impl uses `v = any` |

`create__size_t` returns `node__size_t_any*` but the caller expects `node__size_t_()*`.
These have different memory layouts (3 vs 4 fields), so the checker rejects.

## Expected

`()` and `any` should unify to the same monomorphized type for erased parameters, producing one struct.
