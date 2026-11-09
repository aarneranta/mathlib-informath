# mathlib-informath

Informalizations of Lean Mathlib4: Mathlib's statements translated to Dedukti
and read in English, French, Czech, German and as formulas by
[Informath](https://github.com/GrammaticalFramework/informath).

[mathlib-informath.html](mathlib-informath.html) is a table of contents, with
one page in `pages/` for each part of Mathlib in `modules.txt`: 82 modules,
9126 declarations. Besides `Mathlib/Order/Defs/`, the prime numbers and prime
factorizations, they are the undergraduate modules that much of Mathlib
depends on, in six tiers (see "Theorems with proofs" below). Each page shows,
for each statement:

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

Mathlib's own notation is added as a symbolic variant: `lake exe export
--definitions` prints each definition applied to its arguments with Lean's
delaborator (the scoped notations of its namespaces opened, as `n !` of `Nat`),
and where that is notation rather than the name (`n !`, `⌊x⌋`, `s ∆ t`,
`M ≃* N`, `ℝ≥0`), it is written in LaTeX token by token, into the entry as `|
$#1!$`, or as the entry alone where there is no wording. Notation that is not
easily written in LaTeX (binders as `∑ x ∈ s, f x`, Lean's bracket subscripts
as `⊗[R]` and `f^[n]`) is left out; 42 definitions have one.

A class is shown as on the Structures pages (below): the export writes each
class's structure, by extension of its parent (the one its docstring names,
else its ancestor with the most fields), and its predicate. A class worded as a
noun ("#1 is a monoid") is read as the structure, "A monoid is a semigroup $M$
with an element $1$ of $M$ such that ...", with its predicate under it, "Let
$M$ be a set. Then $M$ is a monoid, if ...". Any other class is read as its
predicate ("$G$ is unique, if ..."). A class whose fields are all technical
(`TopologicalSpace`, its `IsOpen`) keeps its plain declaration.

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
| `structures.txt`, `structures.dkgf` | the classes exported as structure definitions (`lake exe export --structures`), and the nouns that name them |
| `out/` | the export: `<Module>.dk` (the statements), `<Module>.json` (docstrings, source lines), `<Module>-deps.dk` (the constants they use) |
| `build-index.py` | builds `index.json`: for each declaration its Dedukti, its readings (English, French, Czech, German, formula) and proof texts, made by RunInformath in a few calls |
| `index.json` | the index, from which the pages are made |
| `build-html.py` | builds `mathlib-informath.html` and `pages/*.html` from `index.json` |
| `tactic-units.py` | the steps of a module's tactic proofs as proof units, for `RunInformath -tactic-proof` |
| `coverage.py`, `coverage.md` | for each module, how many readings are fully worded and how many theorems have proof texts, and the constants most often left without a wording |

A Greek type variable becomes the Latin capital a textbook would use for a
set ("Let $X$ and $Y$ be sets" for `α` and `β`). The order on sets is
inclusion, and Mathlib writes `s ⊆ t`, `s ∪ t` and `s ∩ t` with the order's
`≤`, `max` and `min`; on sets (and finite sets) these become `Set.Subset`,
`Union.union` and `Inter.inter` again, and `⊤`, `⊥` the universal and the
empty set.

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
lemmas keep their arguments but for type class instances, as do the other
constants that are proofs (`Equivalence.mk`, `propext`), whose types are
stated with their implicit arguments too. The proofs are
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
A step that closes a goal or derives a fact says how, where its tactic tells:
"By rewriting, ..." (`rw`), "By simplification, ..." (`simp`), "By
computation, ..." (`ring`, `omega`, `norm_num`), "By definition, ..." (`rfl`),
"By a routine argument, ..." (`grind`, `aesop`); a step that applies a lemma
(`exact`, `apply`) is left as it is, as its tactic names the lemma. "It is
enough to show that ..." is not said of the goal as it was (up to the names of
bound variables), nor of a fact just stated to be verified.

In a term proof, the text names no lemma (`-proof-no-cite`): the margin cites
every rule, linked to its entry. The rewriting that `simp` and `rw` leave in a
proof term (`congrArg`, `Eq.mpr`, `of_eq_true` over equations between
propositions) is one step, "By rewriting, ...", whose margin names the simp
lemmas it uses; and a lemma that the export applies without its implicit
arguments (`rfl`) states what it proves where it is used.

An additive theorem that `to_additive` makes from a multiplicative one has the
proof of its original, translated: a term proof as Lean has it, a tactic proof
with the goals of each step translated by `to_additive`'s own translation
(`lake exe export --tactics` writes each step once for the theorem and once for
each twin, with its `decl`), so that the tactics in its margin are those of the
original.

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

## Theorems with proofs

The modules beyond the first pages were chosen as the parts of undergraduate
mathematics that most of Mathlib imports, in six tiers (`modules.txt`):

| tier | modules | declarations |
|---|---|---|
| A. logic, sets, orders | `Logic.Function.Basic`, `Order.Basic`, `Order.Lattice`, `Order.Monotone.Basic`, `Order.Bounds.Basic`, `Data.Set.Basic`, `.Image`, `.Function` | 1940 |
| B. groups and rings | `Algebra.Group.Basic`, `.Hom.Defs`, `.Subgroup.Defs`, `.Subgroup.Basic`, `.Even`, `Algebra.Ring.Basic`, `.Parity`, `Algebra.Field.Basic`, `Algebra.Order.Field.Basic`, `GroupTheory.Coset.Basic`, `.QuotientGroup.Basic`, `.OrderOfElement` | 2276 |
| C. elementary number theory | `Data.Nat.GCD.Basic`, `.Factorial.Basic`, `.Choose.Basic`, `.Choose.Sum`, `.ModEq`, `.Totient`, `Data.Int.GCD`, `.ModEq`, `Data.ZMod.Basic`, `Data.Rat.Defs`, `NumberTheory.Divisors` | 892 |
| D. finite sets and sums | `Data.Finset.Basic`, `.Card`, `Data.Fintype.Card`, `Algebra.BigOperators.Group.Finset.Basic`, `.Intervals`, `Combinatorics.Pigeonhole` | 767 |
| E. linear algebra, ideals, polynomials | `LinearAlgebra.Span.Basic`, `.Basis.Defs`, `.LinearIndependent.Defs`, `.Matrix.Determinant.Basic`, `RingTheory.Ideal.Defs`, `.Basic`, `.Quotient.Defs`, `.PrincipalIdealDomain`, `.UniqueFactorizationDomain.Basic`, `Algebra.Polynomial.Basic`, `.Div`, `.Roots` | 1091 |
| F. topology and analysis | `Topology.Basic`, `Order.Filter.Basic`, `Topology.MetricSpace.Pseudo.Defs`, `.Compactness.Compact`, `.Connected.Basic`, `Analysis.Real.Sqrt`, `.SpecificLimits.Basic`, `.Calculus.Deriv.Basic`, `.Calculus.MeanValue`, `.SpecialFunctions.Exp` | 1405 |

All of them are exported with their tactic proofs too. `coverage.md`
(`python3 coverage.py`) tells, module by module, how much reads well; over
all modules, 7024 of the 9126 readings are fully worded, and 7596 of the 8472
theorems have a proof text (3647 from terms, 3949 from tactics); 41 proofs
fail, mostly where a λ proves a proposition that is a ∀ only after a definition
is unfolded. The
readings and proof texts are in English, French and Czech (`LANGUAGES` in
`build-index.py`): 6606 of the readings are fully worded in French and 6519
in Czech. The French and Czech words of the Mathlib lexicon
(`translations.tsv`) are to be reviewed.

The statements leave out, besides decidability, the instance hypotheses that
a textbook never states (`droppedInstance` in `Export.lean`: the coercion
classes `FunLike` and `SetLike`, the compatibility of an order or an action
with the operations, the bare notation classes `Zero`, `Add`, ...), and so do
the λs of their proofs.

## Algebraic structures

The `Structures` pages show Mathlib's classes (`structures.txt`) as informal
mathematics defines them, by extension of a parent (doc/structures, options
B, C and D): `Structures.Algebra.Group` from magmas to commutative groups,
`Structures.Algebra.Ring` from additive commutative monoids to fields,
`Structures.Order.Lattice` from preorders to distributive lattices, and
`Structures.Algebra.Module`:

> A monoid is a semigroup $M$ with an element $1$ of $M$ such that for all
> elements $a$ of $M$, $1 \times a = a$ and $a \times 1 = a$.

> Let $G$ be a set. Then $G$ is a commutative group, if $G$ is a group and for
> all elements $a$ and $b$ of $G$, $a \times b = b \times a$.

`lake exe export --structures` writes, for each class `C`, two declarations:
the structure, whose clauses are its carrier, its parent's predicate and its
own fields,

    Monoid__structure : (M : Set) -> (h : Proof (Semigroup M)) -> ({|1|} : Elem M) ->
      (one_mul : Proof (forall M (a => Eqt M (times {|1|} a) a))) -> ... -> Structure.

which Informath reads with its extension judgement ("a monoid is a semigroup
$M$ with ... such that ..."), and the class as a predicate of its carrier,
defined by its parent and its new fields, their data quantified,

    def Monoid : (M : Set) -> Prop :=
      M => and (Semigroup M) (exists M (e => and (forall M (a => ...)) (forall M (a => ...)))).

shown as a second entry, `Monoid (predicate)`. The class predicate is what
statements assume ("Assume that $G$ is a group").

The parent is the one the docstring names, as Mathlib's docstrings follow the
textbooks ("A `Monoid` is a `Semigroup` with an element `1` such that ...", "A
`Group` is a `Monoid` with an operation `⁻¹` ...", "A commutative monoid is a
monoid with ..."), if it is one of the exported classes; otherwise the
exported ancestor with the most fields. A class without one (`Mul`) is a
structure of all its fields: "A magma is an algebraic structure, where $G$ is
a set and $*$ is a binary operation on $G$". The parent's operations are
written as the statements write them (`a * b` is `times a b`); the new fields
are variables, the operations named by their notation: a binary operation
(`*`, `+`) an `Oper G` applied with `appOper`, a unary one (`⁻¹`, `-`) a
`UOper G` applied with `appUOper` ($a^{-1}$) or `appPrefixUOper` ($-a$), and
the identity element `1` or `0`. In the predicate, they are named $e$ and $i$.
Left out are the fields with a default value (`npow`, `div`, `zpow`) and the
laws that mention them (`npow_zero : x ^ 0 = 1`); the page lists them for each
structure, with its parents and the parent chosen.

A relation field (`≤`, `<`) is a `Rel G` applied with `appRel` ($a \leq b$),
an action (`•` of a module) an `Action R M` applied with `appAction`, and the
lattice operations `⊔` and `⊓` are written as such. A data field not built of
the carrier (`toNNRat` of a division ring, `nnqsmul`) is technical: it is left
out with its laws. A type parameter other than the carrier (`R` of a module)
becomes a clause before it, with its instance as a hypothesis, which Informath
reads as an assumption:

> Let $R$ be a semiring. Then a module over $R$ is an additive commutative
> monoid $M$ with an action $•$ of $R$ on $M$ such that ...

An additive class whose multiplicative version is exported before it
(`AddCommGroup` after `CommGroup`) is derived from it by `to_additive`'s
translations: its name, its parent's and its fields' (`mul_comm` is
`add_comm`), and the notation (`*` is `+`, `1` is `0`, $a^{-1}$ is $-a$).

## Building

Requirements: a Mathlib checkout beside this one (`../mathlib4`, with
`lake exe cache get` run there), the Lean toolchain of `lean-toolchain`, and
Informath built (`stack build` or `stack install`) with `INFORMATH_ROOT`
pointing to it, and its grammar of English, French, Czech, German and Swedish built in Informath
(`share/InformathFull.pgf`):

    make full_grammar

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
    lake exe export --structures              # structures.txt -> out/Structures.*.dk
    python3 build-index.py                    # -> index.json, English (1 minute)
    LANGUAGES=Eng,Fre,Cze,Ger,Swe python3 build-index.py   # all languages (15 minutes, German)
    python3 build-html.py                     # -> mathlib-informath.html, pages/

To check the symbol table against the exported constants, and to read a module
back by hand:

    cat out/*-deps.dk out/*.dk > /tmp/base.dk
    RunInformath -base=/tmp/base.dk mathlib.dkgf
    RunInformath -add-symboltables=mathlib.dkgf out/Mathlib.Data.Nat.Prime.Defs.dk
