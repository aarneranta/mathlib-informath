# mathlib-informath and Verbose Lean

A comparison of mathlib-informath (Lean → Dedukti → Informath, natural
language as output) with [Verbose Lean](https://github.com/PatrickMassot/verbose-lean4)
(controlled natural language as Lean input), P. Massot, *Teaching Mathematics
Using Lean and Controlled Natural Language*, ITP 2024
(`~/claude/docs/massot-verbose.pdf`, the same as the repository's
`itp2024_paper.pdf`). Written 2026-11-11.

Sections 1-4 are the comparison; section 5 the work done on 1 and 5 of
section 4. The files here: `SeqCont.lean` (Verbose's definitions of continuity and
convergence, and two of its examples, in plain Lean with Mathlib),
`verbose.dkgf` (their wordings, as Verbose's notations have them),
`Formulas.lean` (formulas of a Verbose proof as statements), and the readings
that `./mathlib-informath -languages=Eng,Fre -table=verbose.dkgf` gives of them
(`*-readings.txt`).

## 1. Goals and functions: opposite directions

| | Verbose Lean | mathlib-informath |
|---|---|---|
| direction | input: students write proofs in a CNL, Lean checks each sentence | output: existing Lean code is exported to Dedukti, Informath writes text |
| users | students learning to write paper proofs; teachers configuring exercises | readers of formal mathematics |
| material | small exercises, mainly elementary analysis, with the teacher's own definitions and notations | 9126 Mathlib declarations: statements, definitions, term proofs, some tactic proofs |
| unit of language | the proof step: one sentence = one tactic | mainly the proposition; proof steps from natural deduction rules or tactic units |
| assistance | `help` tactic and a click-to-suggest widget; teacher configuration of silently used lemmas and unfoldable definitions | none while proving; variants of a reading ranked (closest to the book's sentence) |
| languages | English and French, each a hand-made copy of the syntax files (17 files) | five languages from one GF abstract syntax; formulas as LaTeX or in words |

Massot's conclusion: a CNL is not an efficient input format for mathematicians,
and making formal mathematics accessible to readers "is much more likely to be
achieved by translating formalized mathematics to natural language a
posteriori", which can also show inferred information and generated proofs.
That is mathlib-informath's direction.

## 2. The controlled languages

**Verbose**: Lean `syntax` rules, about 56 phrase templates in English ("Fix
…", "By … applied to … using that … we get … such that …", "Let's prove that …
works", "It suffices to prove …", "We conclude by …", "Since … we get …").
Between the fixed words are Lean terms in Lean notation; formulas are not put
into words, deliberately: the pedagogy separates stating, proving and using a
fact ("Fix ε > 0" vs. stating ∀ ε > 0; "we get δ such that" takes a witness
instead of claiming existence; ⇒ only in statements). Notation is adjusted
instead (⇒ for implication, `u converges to l`). No morphology or agreement;
one fixed form per sentence.

**Informath**: a GF grammar. The abstract syntax covers judgements,
hypotheses, kinds, adjectives, quantifiers; each language has a concrete
syntax with morphology and agreement ("Soient A et B des préordres sur X tels
que …"). Symbol tables map constants to words and/or LaTeX; formulas can be
verbal or symbolic; variants can be ranked; the grammar parses as well as
generates. Proof texts are natural deduction lines with justifications. Rich
for propositions, poor in proof style; no bounded quantifiers.

## 3. Examples

### A. Continuity implies sequential continuity (the paper's first example)

Lean (the paper's plain tactic proof):

    intro ε ε_pos
    rcases hf ε ε_pos with ⟨δ, δ_pos, Hf⟩
    rcases hu δ δ_pos with ⟨N, Hu⟩
    use N
    intro n n_ge
    exact Hf (u n) (Hu n n_ge)

Verbose (written by the student, from the paper):

    Fix ε > 0
    By hf applied to ε using that ε > 0 we get δ such that
      δ_pos : δ > 0 and Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε
    By hu applied to δ using that δ > 0 we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
    Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
    Fix n ≥ N
    By Hf applied to u n it suffices to prove |u n - x₀| ≤ δ
    We conclude by Hu applied to n using that n ≥ N

mathlib-informath (generated from the plain tactic proof; macros rendered):

> Let f be a function from real numbers to real numbers. Let u be a function
> from natural numbers to real numbers. Let x be a real number such that u
> converges to x and f is continuous at x. Then f ∘ u converges to f(x).

    1.   Let ε ∈ ℝ such that ε > 0.                                   [intro ε ε_pos]
    2.   Let W ∈ ℝ such that W > 0 and for all elements x₂ of ℝ,
         if |x₂ − x₀| ≤ W, then |f(x₂) − f(x₀)| ≤ ε.                 [rcases hf ε ε_pos with ⟨δ, δ_pos, Hf⟩]
    3.   Let N ∈ ℕ such that for all elements n of ℕ,
         if n ≥ N, then |u(n) − x₀| ≤ W.                              [rcases hu δ δ_pos with ⟨N, Hu⟩]
    4.   It is enough to show that for all elements n₁ of ℕ,
         if n₁ ≥ N, then |f ∘ u − f(x₀)| ≤ ε.                         [use N]
    5.     Let n ∈ ℕ such that n ≥ N.                                 [intro n n_ge]
    6.     |f ∘ u − f(x₀)| ≤ ε.                                       [exact Hf (u n) (Hu n n_ge)]

Same structure (one sentence per tactic: mathlib-informath's tactic reading is
the inverse of Verbose). Verbose reads better as a paper proof. Defects of
mathlib-informath that this example shows: δ became W and x₀ became x in the
statement (the exporter keeps ASCII names only: ε, δ, x₀ in definitions become
x, x₁, x₂); `(f ∘ u) n` lost its argument; "Let ε ∈ ℝ such that ε > 0" for
"Fix ε > 0"; the same proof as a term (`Exists.elim … fun δ ⟨δ_pos, Hf⟩ => …`)
gives no proof text, as the pattern-matching λ is compiled to `match`.

### B. Constant sequences converge

Verbose (`Examples.lean`):

    Fix ε > 0
    Let's prove that 0 works
    Fix n ≥ 0
    Calc |u n - l| = |l - l| from h
     _             = 0       by computation
     _             ≤ ε       from ε_pos

mathlib-informath (from a one-line term proof; abridged):

    1. Let x ∈ ℝ.
    2.   To prove that if x > 0, then there exists an element N₁ of ℕ such that …, assume that x > 0.
    3.     To prove that there exists an element N of ℕ such that …, let n₁ ∈ ℕ.
    4.       To prove that if n₁ ≥ 0, then |u(n₁) − l| ≤ x, assume that n₁ ≥ 0.
    5.       By rewriting, there is an element of Leq(|u(n₁) − l|, x).        [rewriting]
    …
    9. For all elements x of ℝ, if x > 0, then there exists an element N₂ of ℕ such that …

Every introduction rule spelled out; the witness 0 never announced (Verbose's
"Let's prove that 0 works"); line 5 is a bug.

### C. A formula: `∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε`

Verbose leaves it as it is. Informath: "for all elements eps1 of ℝ, if eps1 >
0, then there exists an element N₁ of ℕ such that for all elements n₁ of ℕ, if
n₁ ≥ N₁, then |f(u(n₁)) − f(x₀)| ≤ eps1": correct, but a textbook says "for
every ε > 0 there is an N such that … for all n ≥ N", which needs bounded
quantifiers.

## 4. Would a combination make sense?

Putting today's Informath verbalizations into Verbose's output (goal display,
help) would make formulas longer and rename variables, and would go against
Verbose's use of symbols for stating. The promising combinations:

1. **Verbose as an output style of Informath's proof texts.** mathlib-informath
   already pairs each tactic with a sentence; writing those sentences in
   Verbose's CNL gives a text that reads like a paper proof and that Lean with
   Verbose can check again: a round trip, the only one of these with text
   guaranteed correct. The mapping for intro, rcases/obtain, use, suffices,
   exact is close to mechanical.
2. **Verbose's phrasing as a model for Informath's proof lines** in all
   languages ("Fix ε > 0", "we get δ such that", "N works", "it suffices to
   prove"), carried to French, German, Swedish, Czech by GF.
3. **Verbose's languages generated from a GF grammar** of its ~56 templates
   (Lean `syntax`/`elab` files per language, with Informath's morphology).
   Moderate gain: the templates are few, and Lean still parses.
4. **An optional "in words" view** of hypotheses and goals in Verbose's
   display or help, once 5 is done.
5. **Preconditions on the Informath side**: bounded quantifiers ("for every ε >
   0", "Fix n ≥ N") in the grammar and the exporter; Greek variable names kept
   (Export.lean's `freshName` accepts ASCII only); the bugs above: `(f ∘ u) n`
   losing its argument, the "rewriting" line, no proof text for term proofs
   with pattern-matching λ.

## 5. Done (2026-11-11): 1 and 5

### 1. Verbose as an output style: `VerboseGen.lean`, `verbalize.sh`

`#verbalize "title"` before a theorem with an ordinary tactic proof writes it
as a Verbose Lean `Example`: the statement as Given:/Assume:/Conclusion:, each
step as one Verbose sentence, formulas printed by Lean with Verbose's
notations; `verbalize.sh` collects them into a file and checks it with Lean and
Verbose (the round trip):

    ./verbalize.sh SeqContVerbose-input.lean   # -> SeqContVerbose.lean, checked

The three examples of `SeqContVerbose-input.lean` all check
(`SeqContVerbose.lean`). The paper's plain proof

    intro ε ε_pos
    rcases hf ε ε_pos with ⟨δ, δ_pos, Hf⟩
    rcases hu δ δ_pos with ⟨N, Hu⟩
    use N
    intro n n_ge
    exact Hf (u n) (Hu n n_ge)

comes out as

    Fix ε > 0
    By hf applied to ε using ε_pos we get δ such that (δ_pos : δ > 0) and (Hf : ∀ (x : ℝ), |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
    By hu applied to δ using δ_pos we get N such that (Hu : ∀ n ≥ N, |u n - x₀| ≤ δ)
    Let's prove that N works
    Fix n ≥ N
    We conclude by Hf applied to u n using Hu n n_ge

which is Verbose's own example of the paper but for "using that ε > 0"
(Verbose's nameless variant) and the elided "Let's prove that ..." lines.

How: the command elaborates the theorem (synchronously, `Elab.async false`,
so that the proof's info trees are there), and for each tactic of the proof
takes its info node: the goals before and after, so the new local
hypotheses. `intro` is "Fix x rel e" where the hypothesis has the name
Verbose's `Fix` gives (ε_pos, n_ge), else "Fix x" and "Assume h : P";
`rcases`/`obtain` "By f applied to objects using proofs we get ... such that
(h : P) and ..." (the function and arguments as the source writes them, the
elaborated term telling which arguments are proofs); `use t` "Let's prove that
t works"; `exact` "We conclude by ...". Any other tactic stays as it is, which
Verbose allows (`rw`, `linarith` above). The proofs name their hypotheses, so
each `Example` is preceded by `open Verbose.Named in`, as in Verbose's
examples.

Not yet: `apply`/`suffices` ("By h it suffices to prove"), `constructor`
("Let's first prove"), `calc`, `rw` ("We rewrite using"); French (the same
command with Verbose's French phrases); Mathlib's own proofs, which use
Mathlib's notation rather than a teacher's (they would need Verbose with
Mathlib's definitions, not ExampleLib's).

### 5. Informath and the exporter

* **Bounded quantifiers** (Informath 6a81736): a quantified variable with a
  condition on it, a comparison (<, >, ≤, ≥, ≠, ∈, ⊂, ⊆) with a term without
  it, is read as one, its kind kept: the new `FormulaArgKind` (made by
  `MathCore2Informath.aggregate`, taken back to Dedukti by
  `Informath2MathCore.addParenth`) in the existing `AllProp` and `ExistProp`,
  so each language has its own determiners:

  > f is continuous at x₀, if for all real numbers ε > 0, there exists a
  > real number δ > 0, such that for all real numbers x, if |x − x₀| ≤ δ,
  > then |f(x) − f(x₀)| ≤ ε.

  > Pour tous les nombres réels ε > 0, il existe un nombre réel δ > 0 tel
  > que …; för alla reella tal ε > 0 …; pro všechna reálná čísla ε > 0 …

  Unlike Verbose ("∀ ε > 0"), the kind is said: "there exists q ≠ 0" in the
  definition of rational numbers would not say that q is an integer.
  Informath's regression suite: four cases accepted with the new readings,
  the readback cases pass; a variant with a symbolic set as the kind reads
  "an element q > 0 of ℕ".
* **Greek and subscripted names kept** (Export.lean `asciiName`: ε as epsilon,
  x₀ as x0, which Informath shows as ε, x₀; types still X, Y, ...;
  tactic-units.py the same, with Latin capitals only for the names of types).
* **`(f ∘ g) x`** exported as `f (g x)` (its definition; the entry of
  `Function.comp` words f ∘ g only).
* **Rewriting** (`Eq.mpr`, `Eq.mp` on propositions mapped to rules of nd.dk
  with Prop types): "By rewriting, |u(n₁) − l| ≤ ε." instead of "there is an
  element of Leq(...)".
* **Pattern matching on ∧ and ∃** in term proofs (`fun δ ⟨δ_pos, Hf⟩ => …`):
  the matcher translated to the projections and to existsE, so such a proof
  has its proof text (`seq_cont_term`: 19 lines).

Left: proof lines still "Let ε ∈ ℝ such that ε > 0" for Verbose's "Fix ε > 0"
(2 of section 4).
