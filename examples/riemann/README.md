# The Riemann hypothesis submission, informalized

On 2026-11-20 Levent Alpöge announced Lean proofs of the Riemann hypothesis
and of the generalized Riemann hypothesis for Dirichlet L-functions. The
submission has 175,187 modules, about 17 million lines and a million
declarations, and no comments. This example reads the top of it in English and
as formulas with Informath, as mathlib-informath does for Mathlib and
[../navier-stokes](../navier-stokes) for OpenAI's Navier–Stokes formalization:
the statements it claims, the statement its proof actually proves, the
hypotheses of the proof's last step, and the definitions of the notions those
use. It reads statements and definitions, not proofs.

## Sources

- L. Alpöge, the announcement: [remark.pdf](https://alpo.ge/remark.pdf)
- The Lean submission as published, with a Comparator setup:
  [homeowmorphism/riemann-hypothesis-original](https://github.com/homeowmorphism/riemann-hypothesis-original),
  read here at commit
  [e4ed653](https://github.com/homeowmorphism/riemann-hypothesis-original/tree/e4ed6533e67aaf71e918c97ccf1ed4d5458a0b23)
  (the source `src/` is tree 24df20b, unchanged since the tag `as-published`;
  Lean 4.33.1, Mathlib v4.33.1)
- Community cleanup:
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)

## The pages

[comparison.html](comparison.html) puts the readings beside Alpöge's
announcement, which has no theorem statements: the claims (RH and GRH for
Dirichlet L-functions), the statement the proof actually proves
(`EveryCharacter`, GRH in its half-plane form), and the three propositions of
its last step: `Row0b` (Galois representations of polarized cusp
representations), `RecTExists` (a local Langlands correspondence, with most
laws required only for "good" representations) and `VWin`, which is the
announcement's step 17 (a bound on Ш¹(E, ℚ_l/ℤ_l(−e)) over a cyclotomic
ℤ₂-tower, "a significant weakening of Vandiver"). Then what the readings show,
and what they do not.

[index.html](index.html) lists the modules read, in four groups, and
[pages/](pages/) has one page per module in mathlib-informath's format: each
declaration with its Lean source (linked to GitHub), its Dedukti, an English
reading and a formula.

1. **The claims.** `Challenge.lean` states the five theorems with `sorry`,
   importing only Mathlib; Comparator checks that `Main.lean` proves exactly
   these statements. They are read from `Challenge`, since `Main` imports the
   whole submission.
2. **From the claims to the statement of the proof.** All five follow from
   `UpperTheory.EveryCharacter` (no Dirichlet L-function vanishes for
   Re s > 1/2, except L(1, s) at s = 1) by the functional equation
   (`Supplements/Kernels/MainTheorems.lean`, `CritLine`, `RhOfRight`).
3. **The hypotheses of the last step.**
   `CharacterBoxes/MainConclusion.lean` proves `EveryCharacter` from
   `Row0b (IsRecT)` (Galois representations attached to the regular algebraic,
   polarized cusp representations of GL_a over CM fields, with local-global
   compatibility), `RecTExists` (a local Langlands correspondence with given
   laws at every place of every number field) and `VWin` (a bound on the
   lengths of the Tate–Shafarevich groups Ш¹ of the twists ℚ_l/ℤ_l(e) over
   subfields of cyclotomic fields), and
   `VWin` from `Row0b`. Each of these is proved elsewhere in the submission.
4. **The notions these use**: the modules that declare the constants of the
   definitions in 1–3, one level down (Weil–Deligne representations,
   irreducible representations of GL_n of local fields, cusp representations,
   Hecke characters, p-adic Hodge theory, …).

Two modules of group 4 are left out because the exporter does not finish
them in five minutes: `Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw`
and `.DRS`. They declare `GlobalTheory.Fc.Hyps`, a structure of 50 hypotheses
that `UpperTheory.Top.plugWin` takes, and `DRS`, one of its parameters, both
deeply nested; their names show where they are used.

[constants.tsv](constants.tsv) lists the Lean constants that the readings
show, with their occurrences, where they are declared (the submission,
Mathlib or Lean) and the symbol table entry used, as in ../navier-stokes.

## How it is made

    ./build.sh fetch     # the first time: fetch the compiled files, then build
    ./build.sh

`build.sh` needs:

- **The submission.** `../riemann-hypothesis-original` beside
  mathlib-informath (or `$RIEMANN`), with Mathlib's compiled files
  (`lake exe mathlib/cache get` in it, about 6.5 GB) and those of the modules
  read here. The full cache of the submission (`lake exe cache get`) unpacks
  to about 105 GB; `./build.sh fetch` runs `scripts/fetch-cache.py`, which
  takes from the same pinned community cache (list and archives checked by
  sha256, as `scripts/restore-cache.py` of the submission does) only the
  import closure of the modules read, 15,668 modules and 11 GB, and compiles
  `Challenge`, which is not in the cache.
- **Informath** in `$INFORMATH_ROOT` (default `../informath` beside
  mathlib-informath), at commit 9e031c0 or later, which has the two changes
  made for this example: a quantification over the proofs of a proposition
  whose variable occurs only in hidden arguments reads as an implication, so
  that Lean's `∀ (N : ℕ) [NeZero N]` reads "for all natural numbers N, if N
  is nonzero, …" (b1f9218); and a function quantified over loses the proofs
  that its type takes and that its applications give it (62ff048), so that
  `VVle` reads "for all functions ld from natural numbers p₄ to elements of
  LData(E, X, p₄), for all natural numbers p, if p is prime, then …
  shaLen(ld(p), e) …". `riemann.dkgf` reads Lean's `Fact P` as P
  (`#COERCION Fact 1`).

The steps:

1. **Export.** `exporter/` builds mathlib-informath's `Export.lean` (a link
   to it, as are `mapping.tsv` and `binders.txt`) against the submission's
   Lean and Mathlib, and exports the modules in one process (the imports,
   about 8 GB, are loaded once). The names table is made from a first export
   and the modules are exported again with it, as in ../navier-stokes.
   `scripts/export-each.sh` exports each module in its own process with a
   time limit, to find the modules that the exporter does not finish (it
   found APerTw and DRS).
2. **Symbol tables.** `scripts/name-table.py` gives every constant of the
   submission its short name as an operator (`riemann-names.dkgf`); the
   constants of the submission are those that Lean finds declared in a module
   of its `src/` (`exporter/checks/Origins.lean`). The hand-written
   [riemann.dkgf](riemann.dkgf) overrides it. Since the source has no
   comments, each entry is written from the Lean definition, which it cites,
   and the identifier; it is verbal where a phrase of Informath's lexicon
   parses (`RunInformath -parse-example`), otherwise LaTeX. A few Mathlib
   constants get better entries there too (`DirichletCharacter`,
   `DirichletCharacter.LFunction`).
3. **Readings.** `scripts/read-modules.py` runs mathlib-informath's
   `build-index.py`, in English only.
4. **Pages.** `scripts/build-pages.py` (mathlib-informath's `build-html.py`)
   and `scripts/build-comparison.py`.

`scripts/arguments.py` lists the shown arguments of constants (#1, #2, …),
for writing table entries.

## Open issues

- 745 of the 2522 readings still show some notion by its Lean name, mostly
  in group 4 (the p-adic Hodge theory of `DataN` and `DataNLoc`: `LocWach`,
  `LocPrime`, `NTh`, …). Propositions without arguments (`EveryCharacter`, `VWin`,
  `RecTExists`, `Green`) can only be symbols: no sentence without arguments
  parses as an entry.
- Words missing from Informath's lexicon: cuspidal, supercuspidal, polarized,
  L-function, Weil–Deligne, de Rham, Hodge–Tate, Langlands; the entries use
  LaTeX or a near phrase ("cusp representation") instead.
- The proofs, and the modules below group 4, are not read.
