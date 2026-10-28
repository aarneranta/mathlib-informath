# mathlib-informath

Informalizations of Lean Mathlib4: Mathlib's statements translated to Dedukti
and read in English, French, Czech, German and as formulas by
[Informath](https://github.com/GrammaticalFramework/informath).

[mathlib-informath.html](mathlib-informath.html) is a table of contents, with
one page in `pages/` for each part of Mathlib in `modules.txt`: so far
`Mathlib/Order/Defs/` (orders and lattices), the `Mathlib/Algebra/` modules
that the prime numbers import (`Group/Nat/Units`, `Prime/Defs`),
`Mathlib/Data/Nat/Prime/` (prime numbers) and `Mathlib/Data/Nat/Factorization/`
(prime factorizations). Each page shows, for each statement:

* its Lean source, with a link to its line in Mathlib on GitHub,
* its translation to Dedukti,
* Informath's informalization in English, French, Czech and German and as a formula,
  rendered by MathJax; the other languages than English are hidden until their buttons
  at an entry, or their check boxes above the entries, are clicked,
* for a theorem whose proof is a term (not a tactic proof), the proof in
  each language: numbered lines, each with the rule or the Mathlib lemma it applies
  (linked to its entry) and the lines it uses.

## Informalizing your own Lean code

`mathlib-informath` reads any Lean 4 code that uses Mathlib, from a file or
from standard input, with the same tools as the pages:

    ./mathlib-informath Example.lean                  # plain text, in English
    ./mathlib-informath -languages=Eng,Fre -html Example.lean   # Example.html
    ./mathlib-informath -pdf Example.lean             # Example.pdf (lualatex)
    echo 'theorem t (n : ℕ) (h : 0 < n) : n ≠ 0 := by omega' | ./mathlib-informath
    ./mathlib-informath -table=my.dkgf Example.lean   # with a symbol table of one's own

Code without an import line gets `import Mathlib`. Lean elaborates it
(`lake exe export --file`, about half a minute, most of it loading Mathlib),
and RunInformath reads its declarations with the symbol tables
`definitions.dkgf` and `mathlib.dkgf`. `./mathlib-informath -check` tells which of the
parts it needs are missing (Lean, Mathlib built in `../mathlib4`, the
exporter built here, Informath in `../informath` or `$INFORMATH_ROOT` with
RunInformath and its grammar), `-install` builds those it can, and `-help`
shows the options.

## The symbol table of all Mathlib definitions

`definitions.dkgf` has English wordings for about two thirds of Mathlib's
definitions (26679 of 38601), made by `definition-table.py` from their
docstrings and names; `mathlib.dkgf`, written by hand, overrides it. A
definition whose name has words that the grammar lacks is tried again with
them replaced by words of Informath's lexicon (`lexicon-repair.py`): verbs by
their nominalizations (`restrictScalars`: "the scalar restriction of #1"),
abbreviations by the word that the docstrings of the definitions named with
them use (`denom`: "denominator"), and proper names by their spelling
(`kronecker`: "Kronecker"), in names of at most two words; the replacements,
to be reviewed, are listed in `out/lexicon-repairs.tsv`. The
words that the wordings need but Informath lacks (about 500) are generated in
English into a block of Informath's `Mathlib.gf` and `MathlibEng.gf`
(`python3 definition-table.py -lexicon`, then `make full_grammar` in
Informath), and in the other languages from `translations.tsv`: one line per
word with its French, German, Swedish and Czech forms, written by Claude and to
be reviewed (its header explains the notation; an empty cell means no word).
Where a language lacks a word, `build-index.py` keeps the reading made without
the generated table, which shows the constant symbolically.

`definitions.html` searches all 38,690 definitions by name and wording and
links to their entries on static pages, `definitions/<Part>-<k>.html` (111
pages of at most 400 definitions), where each has its wording and its reading
in English, as a formula and in French (hidden until asked for): the statement of the definition with its
definiens, read by Informath (`python3 build-definitions.py`, about half an hour with 8
RunInformath processes; the readings are cached in
`out/definition-readings.json`).

## Files

| | |
|---|---|
| `Export.lean` | a Lean program that exports statements of Mathlib modules (or of any Lean file, `--file`) to Informath's Dedukti dialect, all Mathlib definitions (`--definitions`), and the steps of tactic proofs (`--tactics`) |
| `mathlib-informath` | the stand-alone informalizer of Lean code |
| `definition-table.py`, `definitions.dkgf` | the symbol table of all Mathlib definitions, made from their docstrings and names |
| `translations.tsv` | the words that `definition-table.py -lexicon` adds to Informath's lexicon, in French, German, Swedish and Czech: to be reviewed |
| `mapping.tsv` | Lean constants mapped to Informath's base constants (`Nat.Prime` to `prime`, `Dvd.dvd` to `divide`, ...) |
| `mathlib.dkgf` | the Informath symbol table of the other Mathlib constants the statements use |
| `nd.dk` | the natural deduction rules that proofs are translated to (`ifI`, `forallE`, ...) |
| `binders.txt` | constants with a binder notation (`∏ x ∈ s, f x`), whose function arguments are bound variables and bodies |
| `modules.txt` | the modules exported and shown, in the order of the pages; a `# page: X` line puts the modules after it on one page X |
| `out/` | the export: `<Module>.dk` (the statements), `<Module>.json` (docstrings, source lines), `<Module>-deps.dk` (the constants they use) |
| `build-index.py` | builds `index.json`: for each declaration its Dedukti, its readings (English, French, Czech, German, formula) and proof texts, made by RunInformath in a few calls |
| `index.json` | the index, from which the pages are made |
| `build-html.py` | builds `mathlib-informath.html` and `pages/*.html` from `index.json` |
| `tactic-units.py` | the steps of a module's tactic proofs as proof units, for `RunInformath -tactic-proof` |

The translation keeps the explicit arguments of Lean's constants and drops the
implicit and instance ones, turns type class assumptions such as `[CommMonoid M]`
into hypotheses ("Assume that M is a commutative monoid"), and treats casts
and coercions to sets and subtypes as the identity. A finitely supported
function applied to an argument, such as `n.factorization p`, becomes one
constant `Nat__factorization__app n p`, declared in the `-deps.dk` file.
Deprecated aliases and declarations generated by Lean are left out. The result
is meant for reading, not for type checking in Dedukti.

Where the Lean source has a term after its `:=` (not `by` and tactics, nor
equations), the definiens is translated too: a definition becomes a Dedukti
`def` with its definiens, which Informath reads as such ("$p$ is prime, if $p$
is irreducible"), and a theorem a `def` whose definiens is its proof. In a
proof, a λ proving an implication or a universal statement becomes `ifI` or
`forallI`, a hypothesis applied to arguments `ifE` or `forallE`, Lean's logical
rules the rules of `nd.dk` (`mapping.tsv`, third column `all`), and Mathlib
lemmas keep their arguments but for type class instances. The proofs are
written out by `RunInformath -proof-text`. A definiens with compiled pattern
matching (`match_` functions, recursors) is not translated.

A theorem proved by tactics (`:= by ...`) gets its proof text from the steps
of the tactic proof, so far for the modules exported with `--tactics`
(`Mathlib.Data.Nat.Prime.Defs`) and in English. `lake exe export --tactics`
elaborates the module again from its source and writes, for each tactic of a
tactic sequence, the goals before and after it in Dedukti
(`out/<Module>-tactics.json`); `tactic-units.py` compares them and makes proof
units: assumptions ("Assume that $n = 1$"), new variables and facts ("Let $n$ be
an element of $\mathbb{N}$ such that $p = m \times n$"), closed goals, and what
is enough to show ("It is enough to show that ..."); `RunInformath
-tactic-proof` writes them out, each with its tactic as the justification.

Both kinds of proof text are laid out in the same way (`build-index.py`
passes `-proof-indent` and `-proof-goals`, and for the term proofs also
`-proof-merge-hypos`), and `build-html.py` shows the indentation with a
vertical line for each open scope:

* **Indentation.** A line is indented by the assumptions open at it. In a term
  proof, a scope is what one λ binds, and the line that discharges it is back
  one level out. In a tactic proof, `tactic-units.py` gives each unit a
  `depth`: the number of assumptions (the hypotheses of an `intro`, and those at
  the beginning of a case) that are still hypotheses of the goal. The facts of
  `have`, `obtain` or `rw at` and the statement's hypotheses open no scope, and
  an assumption that substitutes (`rintro rfl`) leaves no hypothesis, so it stays
  open until the next step that closes a goal. The depth is approximate where a
  case split changes the type of an earlier hypothesis (`rcases m with ...`
  turns `h` about `m` into `h` about `0`): that hypothesis is no longer counted,
  as Lean's goals do not say where a hypothesis came from.
* **Goals.** An assumption states what it is made for: "To prove that $m = p$,
  assume that $n = 1$." In a term proof, the goal is the conclusion of the rule
  that discharges the assumption, given where it differs from what the
  assumption's scope proves (introductions, not eliminations), and not when it
  is the statement itself. In a tactic proof, an `intro` of propositions only
  gets a `goal`: what is left to show after it; an `intro` of variables does not,
  as its goal would mention them before they are introduced.
* **Merged hypotheses** (term proofs). The variables and hypotheses of one scope
  are one line, aggregated as in statements: "Let $x$ be an element of $X$ such
  that ...", "Assume that $A$ and $B$."

A statement that gets no reading with the symbol table is read again with
`-force-symbolic`, and marked so on the page: this happens where a proposition
is the argument of a macro, as in `{k ∈ s | k ≠ 0}`.

## Building

Requirements: a Mathlib checkout beside this one (`../mathlib4`, with
`lake exe cache get` run there), the Lean toolchain of `lean-toolchain`, and
Informath built (`stack build` or `stack install`) with `INFORMATH_ROOT`
pointing to it, and its grammar of English, French, Czech and German built in Informath:

    cd grammars ; gf --make --probs=Informath.probs InformathEng.gf InformathFre.gf next/InformathCze.gf InformathGer.gf InformathLatex.gf ; mv Informath.pgf ../share/InformathFull.pgf

The French and Czech readings come from the same symbol table: Informath parses
its English wordings into GF trees and linearizes them in each language, so a
word needs a linearization in Informath's grammars (`MathlibFre.gf` and
`next/MathlibCze.gf` for the words of `Mathlib.gf`). The grammar is loaded once for all statements and once for
all proofs, which `build-index.py` reads in one call each, with
`-json -languages=Eng,Fre,Cze` and `-proof-text -languages=Eng,Fre,Cze`. German is read
apart: GF's German linearization is exponential in nested noun phrases, so it is read in
chunks with a time limit of 1 s per statement or proof (`PER_ITEM`), a chunk over the
limit split in halves down to the slow statements, which get no German.

    lake build                                # the exporter
    lake exe export $(grep -v '^#' modules.txt)        # -> out/
    lake exe export --tactics Mathlib.Data.Nat.Prime.Defs   # -> out/<Module>-tactics.json
    python3 build-index.py                    # -> index.json (15 minutes, German)
    python3 build-html.py                     # -> mathlib-informath.html, pages/

To check the symbol table against the exported constants, and to read a module
back by hand:

    cat out/*-deps.dk out/*.dk > /tmp/base.dk
    RunInformath -base=/tmp/base.dk mathlib.dkgf
    RunInformath -add-symboltables=mathlib.dkgf out/Mathlib.Data.Nat.Prime.Defs.dk
