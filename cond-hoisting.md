# Stateful If/Match Conditions

## Problem

`if` and `match` conditions were `term` (pure F\* expressions). Hoisting only
descends into `Tv_App` arguments, so stateful operations nested inside F\*-level
`if`/`match` within a condition were invisible:

```
if (if true then !r = 0 else false) { ... }   // fails: !r buried in Tv_Match
```

## Solution

Change `Tm_If.b` and `Tm_Match.sc` from `term` to `st_term`, following the
existing `Tm_While.condition` pattern. A token-stream preprocessor makes
parentheses optional for backward compatibility.

## Files Changed

### Parser & Sugar

| File | Change |
|------|--------|
| `pulseparser.mly` — `ifStmt`, `matchStmt` | `IF LPAREN pulseStmt RPAREN`, `MATCH LPAREN pulseStmt RPAREN` |
| `PulseSyntaxExtension_Parser.ml` — `make_auto_paren_lexer` | Token preprocessor: auto-inserts `LPAREN`/`RPAREN` when omitted. Detects `LBRACE` at depth 0 as end-of-condition. Passes through F\*-level `if/then` and `match/with` unmodified. |
| `PulseSyntaxExtension.Sugar.fst` — `If.head`, `Match.head` | `A.term` → `stmt` |
| `PulseSyntaxExtension.Desugar.fst` — `If`/`Match` cases | `desugar_term` → `desugar_stmt` |
| `PulseSyntaxExtension.SyntaxWrapper.fsti` — `tm_if`, `tm_match` | Parameter type `term` → `st_term` |
| `PulseSyntaxExtension_SyntaxWrapper.ml` — `tm_if`, `tm_match` | Wrap with `Tm_STApp`/return as needed |

### AST & Naming

| File | Change |
|------|--------|
| `Pulse.Syntax.Base.fsti` — `Tm_If.b`, `Tm_Match.sc` | `term` → `st_term` |
| `Pulse.Syntax.Base.fst` — `eq_st_term'` | `eq_tm` → `eq_st_term` for `b`/`sc` |
| `Pulse.Syntax.Naming.fsti` — `freevars_st'`, `ln_st'`, `subst_st_term'` | `*_term` → `*_st_term` for `b`/`sc` (follows `Tm_While.condition`) |
| `Pulse.Syntax.Naming.fst` — `close_open_inverse_st'` | Same pattern |
| `Pulse.Typing.FV.fst` — `freevars_close_st_term'` | Same pattern |
| `Pulse.Syntax.Printer.fst` — `print_st_head` | `term_to_string b` → `st_term_to_string b` |
| `Pulse.ElimGoto.fst` — `Tm_If`/`Tm_Match` cases | `elab_term` → `elab_st_term` for `b`/`sc` |

### Checker

| File | Function | Change |
|------|----------|--------|
| `Pulse.Checker.If.fst` | `check_if_term` (new) | Pure path: extracts `term` from `Tm_Return`, uses original `check_equiv_emp` logic |
| | `check` | Dispatches: `Tm_Return` → `check_if_term`, other → checks `b` via `check g b ...`, composes with `compose_checker_result_t` |
| `Pulse.Checker.Match.fst` | `check_match_term` (new) | Pure path: `compute_tot_term_type_and_u` on extracted term |
| | `check` | Dispatches: `Tm_Return` → `check_match_term`, other → checks `sc` via `check g sc ...`, composes |
| `Pulse.Checker.fst` | `maybe_elaborate_stateful_head` | Restored `Tm_If`/`Tm_Match` cases: extracts F\* term from `Tm_Return`, runs `hoist_stateful_apps`, rebuilds as `st_term` |

### Extraction

| File | Change |
|------|--------|
| `Pulse.Extract.Main.fst` — `Tm_If`, `Tm_Match` | Uniform `extract_dv g b` / `extract_dv g sc` — no `Tm_Return` special-case |
| `Pulse_Extract_CompilerLib.ml` — `mk_if` | Binds monadic condition to fresh variable via `mk_let`, then branches on it |

### Test

| File | Purpose |
|------|---------|
| `test/StatefulIfCondition.fst` | Regression: `if !r = 0 { }`, `if (if true { !r = 0 } else { false }) { }`, `match Some 1 { }` |

## Token Preprocessor Logic

`make_auto_paren_lexer` wraps the base lexer. On `IF`/`MATCH`:

1. If next token is `LPAREN` → pass through (already parenthesized)
2. Otherwise, buffer tokens tracking `()`/`[]` nesting depth:
   - `LBRACE` at depth 0 → insert `LPAREN` before buffered tokens, `RPAREN` after
   - `RETURNS`/`ENSURES` at depth 0 → same (annotation before body)
   - `THEN`/`WITH` at depth 0 → F\*-level syntax, no modification
