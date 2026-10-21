# mathlib-informath

Informalizations of Lean Mathlib4: Mathlib's statements translated to Dedukti
and read in English and as formulas by
[Informath](https://github.com/GrammaticalFramework/informath).

[mathlib-informath.html](mathlib-informath.html) shows, for each statement of
the modules in `modules.txt` (so far the prime numbers of `Mathlib/Data/Nat/Prime/`):

* its Lean source, with a link to its line in Mathlib on GitHub,
* its translation to Dedukti,
* Informath's informalization in English and as a formula, rendered by MathJax.

## Files

| | |
|---|---|
| `Export.lean` | a Lean program that exports statements of Mathlib modules to Informath's Dedukti dialect |
| `mapping.tsv` | Lean constants mapped to Informath's base constants (`Nat.Prime` to `prime`, `Dvd.dvd` to `divide`, ...) |
| `mathlib.dkgf` | the Informath symbol table of the other Mathlib constants the statements use |
| `modules.txt` | the modules exported and shown |
| `out/` | the export: `<Module>.dk` (the statements), `<Module>.json` (docstrings, source lines), `<Module>-deps.dk` (the constants they use) |
| `build-html.py` | builds `mathlib-informath.html` |

The translation keeps the explicit arguments of Lean's constants and drops the
implicit and instance ones, turns type class assumptions such as `[Group G]`
into hypotheses, and treats casts between number types as the identity. The
result is meant for reading, not for type checking in Dedukti.

## Building

Requirements: a Mathlib checkout beside this one (`../mathlib4`, with
`lake exe cache get` run there), the Lean toolchain of `lean-toolchain`, and
Informath built (`stack build` or `stack install`) with `INFORMATH_ROOT`
pointing to it.

    lake build                                # the exporter
    lake exe export $(cat modules.txt)        # -> out/
    python3 build-html.py                     # -> mathlib-informath.html

To check the symbol table against the exported constants, and to read a module
back by hand:

    cat out/*-deps.dk out/*.dk > /tmp/base.dk
    RunInformath -base=/tmp/base.dk mathlib.dkgf
    RunInformath -add-symboltables=mathlib.dkgf out/Mathlib.Data.Nat.Prime.Defs.dk
