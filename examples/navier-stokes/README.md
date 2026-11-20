# Navier–Stokes and Euler, informalized

OpenAI has announced proofs of finite-time blowup for the Navier–Stokes and
Euler equations, with a Lean formalization that Lean checks completely.
*Navier–Stokes lost in translation* argues that the formalization is not a
faithful translation of the paper's argument. This example reads parts of the
formalization in English and as formulas with Informath, as mathlib-informath
does for Mathlib. The question is whether symbolic informalization helps to
assess a formalized argument. The answer, for this sample, is in
[comparison.html](comparison.html).

## Sources

- OpenAI, *Finite time blowup for Navier–Stokes*:
  [paper (PDF)](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
- The Lean formalization:
  [openai/NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler),
  read here at commit
  [f9e8bc5](https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd),
  the one the article cites (Lean 4.34.0-rc2)
- A. Bastounis, F. Circelli, A. C. Hansen, *Navier–Stokes lost in translation:
  Why Lean verification of AI autoformalisation does not guarantee correct
  natural language proofs*:
  [arXiv:2610.08144](https://arxiv.org/abs/2610.08144), also on the authors'
  site ([PDF](http://www.damtp.cam.ac.uk/research/afha/anders/NavierStokes_LostInTranslation_Final.pdf))

## The pages

- [comparison.html](comparison.html): the article's two examples, Lemma 8.6
  (m + 4 or m + 5 derivatives) and the pressure flux (10.19). Each has the
  paper's statement beside the readings of the Lean declarations, and what the
  readings show. Before them come the main theorem and the definitions it rests
  on.
- [index.html](index.html), [pages/](pages/): all declarations of the 15
  modules read so far, in mathlib-informath's format. Each has its Lean source
  (linked to GitHub), its Dedukti, an English reading and a formula.

The pages read statements and definitions, not proofs.

[constants.tsv](constants.tsv) lists the Lean constants that the readings
show, with the number of their occurrences (most first), where they are
declared (in NavierStokesAndEuler, in Mathlib, or in Lean's own library), and
the symbol table entry that the readings use, with its table. The counts are
those of the informalized text: the statements of the theorems without their
proofs, and the statements and bodies of the definitions, without the
arguments that `#HIDE` hides (implicit types and instances) and without the
theorems that a definition's body uses as proofs. A constant mapped to
Informath's base (`HAdd.hAdd` to `plus`) shows the base's entry; one written
`c__part<m>` or `c__app<m>` counts as `c`. It is made by
`scripts/constants-table.py` (the modules from `exporter/checks/Origins.lean`).

## How it is made

    ./build.sh

`build.sh` needs the following:

- **The formalization.** `../NavierStokesAndEuler` beside mathlib-informath
  (or `$NAVIER_STOKES`), built with `lake exe cache get; lake build` (about 40
  minutes).
- **Informath.** It is found in `$INFORMATH_ROOT` (default `../informath`
  beside mathlib-informath), at commit f9d7c00 or later. Two fixes made for
  this example are in it: the head of a definition whose constant has hidden
  (implicit) arguments showed its arguments shifted (7385dc0), and binder
  macros of propositions, like "eventually", lacked their bound variable
  (f9d7c00).

The steps of `build.sh`:

1. **Export.** `exporter/` builds mathlib-informath's own `Export.lean` (a
   link to it, as are `mapping.tsv` and `binders.txt`) against the project's
   Lean and Mathlib (`lakefile.toml`, `lake-manifest.json`). `ENTRY_TABLES`
   gives it this project's tables besides Mathlib's, so that a function
   applied to fewer arguments than its entry has reads with dots,
   inverse(d, f, ·), and one applied to more applies the entry to them, as
   the README of mathlib-informath explains; an entry of the tables for such
   a form, like `inverse__part1` (N_d⁻¹ f), is kept. The names table is made
   from a first export, and the modules are exported again with it. `MATHLIB`
   is set to the project, so that the definitions keep their bodies.
2. **Symbol tables.** `scripts/name-table.py` gives every constant of the
   project its short name, as an operator (`navier-stokes-names.dkgf`). The
   hand-written [navier-stokes.dkgf](navier-stokes.dkgf) overrides it; each of
   its entries quotes the Lean definition it is written from, in the notation
   of OpenAI's paper and of the article where the definition allows it. The
   tables come on top of mathlib-informath's `definitions.dkgf` and
   `mathlib.dkgf`.
3. **Readings.** `scripts/read-modules.py` runs mathlib-informath's
   `build-index.py`, in English only (`--proofs` adds the texts of the term
   proofs).
4. **Pages.** `scripts/build-pages.py` and `scripts/build-comparison.py`
   (mathlib-informath's `build-html.py`).

[exporter/checks/Uses.lean](exporter/checks/Uses.lean) lists which of the
declarations the article discusses the main theorems use, from the constants of
their proofs, transitively (`cd exporter; lake env lean checks/Uses.lean`).
`scripts/expand.py` prints readings with their macros expanded, and
`scripts/arity.py` the shown arguments of constants, for writing table entries.

## Open issues

- 51 of the 618 readings still show some notion by its Lean name, mostly
  Mathlib notions in the bodies of definitions.
- The proofs, most of them tactic proofs, are not read. Comparing the
  arguments, and not only the statements, would need mathlib-informath's
  tactic replay.
- The Euler modules have no hand-written entries yet.
