# Structures and inheritance: suggestions and samples

Work in progress (6 November 2026): how Mathlib's classes, with their
`extends`, could be exported and informalized closer to informal
mathematics. The samples in this directory are read with

    cat ../../mathlib.dkgf samples.dkgf > /tmp/t.dkgf
    RunInformath -add-symboltables=/tmp/t.dkgf -to-lang=Eng parent-clause.dk
    RunInformath -add-symboltables=/tmp/t.dkgf -to-lang=Eng predicate-def.dk
    (echo 'mul : (G : Set) -> Elem G -> Elem G -> Elem G.'; cat notation.dk) > /tmp/n.dk
    RunInformath -add-symboltables=/tmp/t.dkgf -to-lang=Eng /tmp/n.dk

## Option A: flattened (what the page Structures.Algebra does now)

`lake exe export --structures` flattens the fields of all parents into each
class. Complete and correct, but every definition repeats its ancestors:

> A commutative group is an algebraic structure, where G is a set, one is an
> element of G, * is a binary operation on G, (a*b)*c = a*(b*c), one*a = a,
> a*one = a, inv is a function from G to G, inv(a)*a = one, a*b = b*a.

Informal mathematics defines by extension: *a commutative group is a group
in which ab = ba*.

## Option B: the parent as a clause (works now; `parent-clause.dk`)

The structure takes its carrier, its parent's predicate (`[Semigroup M]`, as
Lean's instance) and only its own fields:

> A monoid is an algebraic structure, where M is a set, M is a semigroup,
> one is an element of M, for all a of M, one·a = a, for all a of M, a·one = a.

> A commutative group is an algebraic structure, where G is a set, G is a
> group, for all a and b of G, ab = ba.

The operations come from the parent, as in Lean (instance resolution); in
the export they would be the parent's selectors at the carrier.

## Option C: an extension judgement (needs a grammar rule; target texts)

Option B's encoding, read by a new MathCore judgement, say
`ExtensionJmt : Label -> Kind -> Ident -> [Clause] -> Kind -> Jmt`, which
Dedukti2MathCore would choose when a structure's clauses begin with
`G : Set` and `Proof (P G)`, P read as a noun (from its entry "#1 is a P"):

> A monoid is a semigroup M with an element 1 such that 1a = a and a1 = a for
> all a in M.

> A group is a monoid G with an operation a ↦ a⁻¹ such that a⁻¹a = 1 for all a.

> A commutative group is a group G such that ab = ba for all a, b in G.

(Hand-written: the lin would split the clauses into data, "with ...", and
properties, "such that ...".)

## Option D: the class as a defined predicate (works now; `predicate-def.dk`)

In mathlib-informath a class is already a predicate of its carrier
(`Group : Set -> Prop`, "G is a group"), which statements use. Giving it a
definition by its parent and its new fields reads like a textbook, with
new data quantified:

> Let G be a set. Then G is a commutative group, if G is a group and for all
> elements a of G, for all elements b of G, ab = ba.

> Let M be a set. Then M is a monoid, if M is a semigroup and there exists an
> element e of M such that for all a of M, ea = a and for all a of M, ae = a.

> Let G be a set. Then G is a group, if G is a monoid and there exists a
> function i from G to G such that for all a of G, i(a)a = 1.

Option D', the informal statement of the same (`Group'`):

> ... G is a group, if G is a monoid and for all elements a of G, there
> exists an element b of G such that ba = 1.

This unifies the class (the predicate the statements use) and the structure,
and fits proofs: a projection such as `CommGroup.toGroup`, or a use of the
field `mul_comm`, becomes an elimination of the definition ("since G is a
commutative group, ab = ba"). What is lost: that 1 and a⁻¹ are data, chosen
by the structure (harmless for monoids and groups, where they are unique).

## Choosing the parent

Lean's classes often have several parents (`CommGroup extends Group,
CommMonoid`; `Monoid extends One, Mul, Semigroup, MulOneClass, NPow`).
Informal mathematics names one and lists what is new. The rule "the first
parent that is an exported structure" gives:

| class | primary parent | new fields |
|---|---|---|
| CommMagma | Mul (magma) | mul_comm |
| Semigroup | Mul (magma) | mul_assoc |
| CommSemigroup | Semigroup (also CommMagma) | mul_comm |
| MulOneClass | Mul | one, one_mul, mul_one |
| Monoid | **Mul** (also Semigroup, MulOneClass) | one, mul_assoc, one_mul, mul_one |
| CommMonoid | Monoid (also CommSemigroup) | mul_comm |
| DivInvMonoid | Monoid | inv |
| Group | **DivInvMonoid** | inv_mul_cancel |
| CommGroup | Group (also CommMonoid) | mul_comm |

Wrong for Monoid (a textbook says *a semigroup with ...*) and Group (the
technical DivInvMonoid). Suggestion: take the parent that the docstring
names, which Mathlib writes as a textbook would: "A `Monoid` is a
`Semigroup` with an element 1 such that ...", "A `Group` is a `Monoid` with
an operation ⁻¹ satisfying a⁻¹ * a = 1" (skipping DivInvMonoid). Fallback:
the largest structure parent that has a noun in the symbol table.

## Notation of fields (`notation.dk`)

Fields named by their notation read better: a variable `{|1|}` prints as
1 ("1 is an element of M ... 1a = a"). A unary operation as `UOper G` with
`appUOper` (formula `${#3}^{#2}$`) and a variable `{|{-1}|}` does not work
yet: the variable prints as `\mathrm{{-1}}`, and "an unary operation" has the
wrong article (both Informath issues to look at).

## Still to do

- decide between B+C (structures) and D (predicates), or keep both (B/C on
  the Structures page, D as the definitions of the class predicates)
- the primary parent from docstrings, in Export.lean (`--structures`)
- for C: the grammar rule and Dedukti2MathCore
- additive classes (AddCommGroup etc.): derive from the multiplicative ones
  by `to_additive`'s notation map instead of exporting both
- the aggregation "for all a of G, for all b of G" (D) as "for all a, b of G"
