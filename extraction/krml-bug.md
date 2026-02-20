# KaRaMeL Bug: Erased type parameter monomorphized as `any` vs `()` across `.fsti` boundary

## Minimal reproducer (3 files, 45 lines total)

### `MyLib.fsti`

```fstar
module MyLib
#lang-pulse
open Pulse.Lib.Pervasives

noeq type node (k v: Type0) = {
  key: k;
  value: v;
  left: option (node k v);
  right: option (node k v);
}

type tree (k v: Type0) = option (node k v)

val is_tree (#k #v: Type0) (ct: tree k v) (ft: Ghost.erased (tree k v)) : slprop

fn create (k v: Type0)
  requires emp
  returns x: tree k v
  ensures is_tree x (Ghost.hide (None #(node k v)))
```

### `MyLib.fst`

```fstar
module MyLib
#lang-pulse
open Pulse.Lib.Pervasives

let is_tree #k #v ct ft = pure (ct == Ghost.reveal ft)

fn create (k v: Type0)
  requires emp
  returns x: tree k v
  ensures is_tree x (Ghost.hide (None #(node k v)))
{
  let r : tree k v = None #(node k v);
  fold (is_tree r (Ghost.hide (None #(node k v))));
  r
}
```

### `MyCaller.fst`

```fstar
module MyCaller
#lang-pulse
open Pulse.Lib.Pervasives

fn test (_u: unit)
  requires emp
  returns r: MyLib.tree FStar.SizeT.t unit
  ensures MyLib.is_tree r (Ghost.hide (None #(MyLib.node FStar.SizeT.t unit)))
{
  MyLib.create FStar.SizeT.t unit
}
```

## Steps to reproduce

```bash
PULSE_HOME=~/pulse  # adjust as needed
FO="--include $PULSE_HOME/out/lib/pulse --include $PULSE_HOME/out/lib/pulse/lib \
    --include $PULSE_HOME/build/lib.pulse.checked --include $PULSE_HOME/build/lib.common.checked \
    --include $PULSE_HOME/lib/pulse/lib --include $PULSE_HOME/lib/common \
    --cache_checked_modules --cache_dir _cache --warn_error -321 \
    --ext optimize_let_vc --load_cmxs pulse"
mkdir -p _cache _output

# 1. Verify
fstar.exe $FO MyLib.fsti && fstar.exe $FO MyLib.fst && fstar.exe $FO MyCaller.fst

# 2. Extract to .krml
fstar.exe $FO --codegen krml --odir _output --extract_module MyLib MyLib.fst
fstar.exe $FO --codegen krml --odir _output --extract_module MyCaller MyCaller.fst

# 3. Run KaRaMeL
krml -skip-compilation -skip-makefiles -skip-linking \
  -warn-error -2-4-9-15-17-18-26 \
  $(find $KRML_HOME/krmllib/.extract -name '*.krml') _output/*.krml
```

## Observed

```
Cannot re-check MyCaller.test as valid Low* and will not extract it.
```

With `-d checker`:

```
option__MyLib_node__size_t_any <=? option__MyLib_node__size_t_()
```

## Root cause

Pulse extraction replaces the erased type parameter `v` with `any` in `MyLib.fst`'s `.krml` output, but the caller `MyCaller.fst` instantiates `v = unit` which becomes `()`. After monomorphization, two incompatible C struct types are created:

| Variant | C fields | Source |
|---------|----------|--------|
| `node__size_t_()` | `{ key, left, right }` | Caller: `v = unit` → erased to `()` (3 fields) |
| `node__size_t_any` | `{ key, value, left, right }` | Impl: `v = any` → kept as `void*` (4 fields) |

`create` returns `node__size_t_any*` but the caller expects `node__size_t_()*`. These have incompatible memory layouts.

**Note:** This does NOT happen with plain F* (non-Pulse) modules. Plain F* extraction keeps `v` as a proper type variable in the `.krml`, so monomorphization correctly unifies it. The issue is specific to how Pulse `fn` elaboration handles Type-kinded parameters during extraction.

## Expected

The erased `v` should either:
1. Be kept as a type variable in the `.krml` (like plain F* does), so monomorphization unifies it, or
2. `any` and `()` should be treated as equivalent during monomorphization for erased parameters
