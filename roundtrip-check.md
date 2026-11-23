# The round trip of NLG and semantics over mathlib-informath

Made by roundtrip-check.py with RunInformath -check-nlg-semantics (Informath doc/nlg-and-semantics.md, doc/nlg-semantics-check.md).

## Statements

9080 judgements: 9076 with MathCore trees, 0 without (no annotation), 3 given up (time limit or failure).

521386 variants; 236 lost, in 8 judgements (0 of them in the default output).

| stage | variants | exact | same hypotheses | equivalent | lost |
|---|---:|---:|---:|---:|---:|
| flatten (passes 1-5) | 32410 | 2726 | 29684 | 0 | 0 |
| aggregate | 25950 | 152 | 21592 | 4167 | 39 |
| variations | 434723 | 6418 | 172792 | 255320 | 193 |
| letDeclared (default output) | 24120 | 2063 | 18958 | 3099 | 0 |
| negated, implied, scoped | 685 | 18 | 573 | 90 | 4 |
| varless | 3420 | 0 | 2111 | 1309 | 0 |
| insitu | 17 | 0 | 17 | 0 | 0 |
| collectivize | 61 | 6 | 51 | 4 | 0 |
| **all** | 521386 | 11383 | 245778 | 263989 | 236 |

### Where the lost ones differ

The head functions of the smallest subtrees where the normalized t and the normalized semantics of t' differ, with the variants, judgements and an example.

| t | semantics of t' | variants | judgements | example |
|---|---|---:|---:|---|
| `CoreAllProp` | `AndProp` | 112 | 5 | SemilatticeSup__structure |
| `ConsClause` | `BaseClause` | 108 | 5 | SemilatticeSup__structure |
| `ConsProp` | `BaseProp` | 16 | 1 | Semiring |

### Modules with most judgements with lost variants

| module | judgements |
|---|---:|
| Structures.Order.Lattice | 3 |
| Structures.Algebra.Group | 2 |
| Structures.Algebra.Ring | 2 |
| Structures.Algebra.Module | 1 |

### Examples of lost variants

* `SemilatticeSup__structure` (aggregate; `CoreAllProp` / `AndProp`): definition . a join semilattice is a partially ordered set $ G $ with a binary operation $ ⊔ $ on $ G $ such that for all elements $ a $ and $ b $ of $ G $ , $ a \leq \appOperMACRoJS { ⊔ } { a } { b } $ and $ b \leq \appOperMACRoJS { ⊔ } { a } { b } $ and for all elements $ a $ , $ b $ and $ c $ of $ G $ , if $ a \leq c $ , then if $ b \leq c $ , then $ \appOperMACRoJS { ⊔ } { a } { b } \leq c $ .
* `SemilatticeSup__structure` (variations; `ConsClause` / `BaseClause`): definition . a join semilattice is a partially ordered set $ G $ with a binary operation $ ⊔ $ on $ G $ such that both for all elements $ a $ and $ b $ of $ G $ , $ a \leq \appOperMACRoJS { ⊔ } { a } { b } $ and $ b \leq \appOperMACRoJS { ⊔ } { a } { b } $ and for all elements $ a $ , $ b $ and $ c $ of $ G $ , if $ a \leq c $ , then if $ b \leq c $ , then $ \appOperMACRoJS { ⊔ } { a } { b } \leq 
* `Semiring` (aggregate; `ConsProp` / `BaseProp`): definition . let $ R $ be a set . then $ R $ is a semiring , if $ R $ is an additive commutative monoid and there exists an element $ e $ of $ R $ , such that there exists an element $ * $ of $ R \rightarrow R \rightarrow R $ , such that for all elements $ a $ , $ b $ and $ c $ of $ R $ , $ \EqtMACRoDE { \appOperMACRoJS { * } { ( \appOperMACRoJS { * } { a } { b } ) } { c } } { \appOperMACRoJS { * 

## Definitions

38972 judgements: 38867 with MathCore trees, 0 without (no annotation), 105 given up (time limit or failure).

227713 variants; 5421 lost, in 206 judgements (30 of them in the default output).

| stage | variants | exact | same hypotheses | equivalent | lost |
|---|---:|---:|---:|---:|---:|
| flatten (passes 1-5) | 75039 | 20214 | 54611 | 0 | 214 |
| letDeclared (default output) | 25252 | 6276 | 18630 | 267 | 79 |
| variations | 107259 | 14050 | 87137 | 1710 | 4362 |
| aggregate | 13695 | 1520 | 11623 | 150 | 402 |
| collectivize | 101 | 3 | 96 | 2 | 0 |
| varless | 5586 | 0 | 5533 | 32 | 21 |
| negated, implied, scoped | 437 | 69 | 347 | 0 | 21 |
| insitu | 22 | 5 | 17 | 0 | 0 |
| #NLG rules | 322 | 0 | 0 | 0 | 322 |
| **all** | 227713 | 42137 | 177994 | 2161 | 5421 |

### Where the lost ones differ

The head functions of the smallest subtrees where the normalized t and the normalized semantics of t' differ, with the variants, judgements and an example.

| t | semantics of t' | variants | judgements | example |
|---|---|---:|---:|---|
| `PropClause` | `VarClause` | 1446 | 11 | LinearOrderedAddCommMonoidWithTop__structure |
| `CoreAllProp` | `AndProp` | 1389 | 19 | SemilatticeSup__structure |
| `ConsProp` | `BaseProp` | 1261 | 50 | MulOneClass |
| `ConsClause` | `BaseClause` | 443 | 58 | Monoid__structure |
| `'\'\\\'p-adic_Adj\\\'\''` | `'\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''` | 220 | 41 | Padic__mulValuation |
| `'\'\\\'p-adic_Adj\\\'\''` | `'\'\\\'\\\\\\\'\\\\\\\\\\\\\\\'p-adic_Adj\\\\\\\\\\\\\\\'\\\\\\\'\\\'\''` | 180 | 41 | Padic__mulValuation |
| `'\'p-adic_Adj\''` | `'\'\\\'p-adic_Adj\\\'\''` | 114 | 18 | padicValInt |
| `'\'p-adic_Adj\''` | `'\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''` | 110 | 18 | padicValInt |
| `NounKind` | `ClassKind` | 100 | 5 | SetLike__GradedMonoid__structure |
| `"S"` | `"R"` | 40 | 1 | IsAbsoluteValue__structure |
| `'\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''` | `'\'\\\'\\\\\\\'\\\\\\\\\\\\\\\'p-adic_Adj\\\\\\\\\\\\\\\'\\\\\\\'\\\'\''` | 40 | 1 | PadicInt__toZModHom |
| `'\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''` | `'\'\\\'\\\\\\\'\\\\\\\\\\\\\\\'\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\'p-adic_Adj\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\'\\\\\\\\\\\\\\\'\\\\\\\'\\\'\''` | 32 | 1 | PadicInt__toZModHom |
| `AdjProp` | `OrProp` | 22 | 5 | CategoryTheory__IsCofilteredOrEmpty |
| `"C"` | `"D"` | 8 | 2 | CategoryTheory__MonoidalClosedFunctor__structure |
| `Adj2Prop` | `CoreExistProp` | 6 | 1 | CategoryTheory__Biproduct__columnNonzeroOfIso |
| `AdjProp` | `CoreExistProp` | 4 | 1 | LinearMap__IsSelfAdjoint |
| `AdjProp` | `AndProp` | 2 | 2 | CategoryTheory__Functor__IsEquivalence__structure |
| `"U"` | `"V"` | 2 | 1 | Prefunctor__MapReverse__structure |
| `"B"` | `"F"` | 2 | 1 | MemTrivializationAtlas__structure |

### Modules with most judgements with lost variants

| module | judgements |
|---|---:|
| Mathlib.NumberTheory.Padics.PadicNumbers | 14 |
| Mathlib.NumberTheory.Padics.PadicIntegers | 9 |
| Mathlib.NumberTheory.Padics.RingHoms | 9 |
| Mathlib.MeasureTheory.Group.Arithmetic | 8 |
| Mathlib.Algebra.Group.Monoid | 6 |
| Mathlib.NumberTheory.Padics.HeightOneSpectrum | 5 |
| Mathlib.CategoryTheory.Filtered.Basic | 4 |
| Mathlib.Order.CompleteBooleanAlgebra | 4 |
| Mathlib.Algebra.Group.DivInvMonoid | 4 |
| Mathlib.Algebra.GroupWithZero.Defs | 4 |
| Mathlib.MeasureTheory.Order.Lattice | 4 |
| Mathlib.NumberTheory.Padics.MahlerBasis | 4 |
| Mathlib.NumberTheory.Padics.WithVal | 4 |
| Mathlib.Topology.Algebra.Monoid.Defs | 4 |
| Mathlib.Order.Heyting.Hom | 3 |

### Examples of lost variants

* `Monoid__structure` (aggregate; `ConsClause` / `BaseClause`): definition . a monoid is a semigroup $ M $ with an element $ 1 $ of $ M $ such that for all elements $ a $ of $ M $ , $ \EqtMACRoDE { 1 \times a } { a } $ and $ \EqtMACRoDE { a \times 1 } { a } $ .
* `MulOneClass` (aggregate; `ConsProp` / `BaseProp`): definition . let $ M $ be a set . then $ M $ is a unital magma , if $ M $ is a multiplicative one and for all elements $ a $ of $ M $ , $ \EqtMACRoDE { 1 \times a } { a } $ and $ \EqtMACRoDE { a \times 1 } { a } $ .
* `SemilatticeSup__structure` (aggregate; `CoreAllProp` / `AndProp`): definition . a join semilattice is a partially ordered set $ G $ with a binary operation $ ⊔ $ on $ G $ such that for all elements $ a $ and $ b $ of $ G $ , $ a \leq \appOperMACRoJS { ⊔ } { a } { b } $ and $ b \leq \appOperMACRoJS { ⊔ } { a } { b } $ and for all elements $ a $ , $ b $ and $ c $ of $ G $ , if $ a \leq c $ , then if $ b \leq c $ , then $ \appOperMACRoJS { ⊔ } { a } { b } \leq c $ .
* `LinearOrderedAddCommMonoidWithTop__structure` (flatten (passes 1-5); `PropClause` / `VarClause`): definition . a linear ordered additive commutative monoid with top is a linearly ordered set $ M $ with an element $ 0 $ of $ M $ and a binary operation $ + $ on $ M $ and an element $ ⊤ $ of $ M $ such that for all elements $ a $ of $ M $ , for all elements $ b $ of $ M $ , for all elements $ c $ of $ M $ , $ \EqtMACRoDE { \appOperMACRoJS { + } { ( \appOperMACRoJS { + } { a } { b } ) } { c } } { 
* `IsAbsoluteValue__structure` (aggregate; `"S"` / `"R"`): definition . let $ S $ be a semiring such that $ S $ is a partially ordered set . then an absolute value is a semiring $ R $ with a function $ f $ from $ R $ to $ S $ such that for all elements $ x $ of $ R $ , $ 0 \leq f ( x ) $ and $ \EqtMACRoDE { f ( x ) } { 0 } $ , if and only if $ \EqtMACRoDE { x } { 0 } $ and for all elements $ x $ and $ y $ of $ R $ , $ f ( x + y ) \leq f ( x ) + f ( y ) $ 
* `CategoryTheory__Functor__IsEquivalence__structure` (aggregate; `AdjProp` / `AndProp`): definition . let $ C $ be a category . then an equivalence is a category $ D $ with a functor $ F $ of $ C $ and $ D $ such that $ F $ is faithful and full and $ F $ is an essential surjection .
* `Prefunctor__MapReverse__structure` (aggregate; `"U"` / `"V"`): definition . let $ U $ be a quiver such that $ U $ has reverses . then a map reverse is a quiver $ V $ with a prefunctor $ r $ of $ U $ and $ V $ such that for all elements $ u $ and $ v $ of $ U $ , for all homomorphisms $ e $ of $ u $ and $ v $ , the map of $ r $ and the reverse of $ e $ is equal to the reverse of the map of $ r $ and $ e $ .
* `CategoryTheory__Biproduct__columnNonzeroOfIso` (flatten (passes 1-5); `Adj2Prop` / `CoreExistProp`): definition . let $ s $ be an element of $ S $ . assume that the identity morphism of $ S_{1} ( s ) $ is distinct from $ 0 $ ( &+ $ &+ \mathrm{nz} &+ $ &+ ) . let $ f $ be a homomorphism of $ \CategoryTheoryLimitsbiproductMACRoAC { S_{1} } $ and $ \CategoryTheoryLimitsbiproductMACRoAC { T_{1} } $ . then the column nonzero of $ s $ and $ f $ is a truncation of $ \mathrm{PSigma} $ applied to the func
* `CategoryTheory__IsCofilteredOrEmpty` (flatten (passes 1-5); `AdjProp` / `OrProp`): definition . let $ C $ be a set . then $ C $ is cofiltered or empty , if $ C $ is a category , for all elements $ X $ of $ C $ , for all elements $ Y $ of $ C $ , there exists an element $ W $ of $ C $ such that there exists a homomorphism $ x $ of $ W $ and $ X $ such that there exists a homomorphism $ x_{1} $ of $ W $ and $ Y $ such that $ \mathrm{True} $ and for all elements $ X $ of $ C $ , fo
* `LinearMap__IsSelfAdjoint` (flatten (passes 1-5); `AdjProp` / `CoreExistProp`): definition . let $ B $ be a linear map of $ M $ and the set of linear maps of $ M $ and $ X $ . let $ f $ be a function from $ M $ to $ M $ . then $ B $ is self-adjoint with respect to a bilinear map , if $ \mathrm{LinearMap\_\_IsAdjointPair} ( B , B , f , f ) $ .
* `SetLike__GradedMonoid__structure` (aggregate; `NounKind` / `ClassKind`): definition . let $ T $ be an additive monoid . let $ R $ be a monoid . then a graded monoid is a graded one $ S $ with a function $ A $ from $ T $ to $ S $ such that for all elements $ i $ and $ j $ of $ T $ , for all elements $ \mathrm{gi} $ and $ \mathrm{gj} $ of $ R $ , if $ \MembershipmemMACRoDQ { A ( i ) } { \mathrm{gi} } $ , then if $ \MembershipmemMACRoDQ { A ( j ) } { \mathrm{gj} } $ , the
* `padicValInt` (flatten (passes 1-5); `'\'p-adic_Adj\''` / `'\'\\\'p-adic_Adj\\\'\''`): definition . let $ p $ be an element of $ \Natural $ . let $ z $ be an element of $ \Integer $ . then the number value integer ['\'p-adic_Adj\''] of $ p $ and $ z $ is an element of $ \Natural $ defined as $ \padicValNatMACRoDI { p } { \IntnatAbsMACRoDV { z } } $ .
* `padicValInt` (#NLG rules; `'\'p-adic_Adj\''` / `'\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''`): definition . let $ p \in \Natural $ . let $ z \in \Integer $ . then the number value integer ['\'\\\'p-adic_Adj\\\'\''] of $ p $ and $ z $ is an element of $ \Natural $ defined as $ \padicValNatMACRoDI { p } { \IntnatAbsMACRoDV { z } } $ .
* `Padic__mulValuation` (flatten (passes 1-5); `'\'\\\'p-adic_Adj\\\'\''` / `'\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''`): definition . the multiplicative valuation is a valuation of the set of numbers ['\'\\\'p-adic_Adj\\\'\''] of $ p $ and $ \mathrm{WithZero} $ applied to the set of multiplicatives of $ \Integer $ .
* `Padic__mulValuation` (#NLG rules; `'\'\\\'p-adic_Adj\\\'\''` / `'\'\\\'\\\\\\\'\\\\\\\\\\\\\\\'p-adic_Adj\\\\\\\\\\\\\\\'\\\\\\\'\\\'\''`): definition . the multiplicative valuation is a valuation of the set of numbers ['\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''] of $ p $ and $ \mathrm{WithZero} $ applied to the set of multiplicatives of $ \Integer $ .
* `MemTrivializationAtlas__structure` (aggregate; `"B"` / `"F"`): definition . let $ B $ be a topological space such that for all elements $ b $ of $ B $ , $ E ( b ) $ is a topological space . then a membership trivialization atlas is a topological space $ F $ with a trivialization $ e $ of $ F $ and $ \mathrm{Bundle\_\_TotalSpace\_\_proj} $ such that $ e $ is an element of the trivialization atlas of $ F $ and $ E $ .
* `CategoryTheory__MonoidalClosedFunctor__structure` (aggregate; `"C"` / `"D"`): definition . let $ C $ be a category such that $ C $ is a cartesian monoidal category and $ \mathrm{CategoryTheory\_\_MonoidalClosed} ( C ) $ . then a monoidal closed functor is a category $ D $ with a functor $ F $ of $ C $ and $ D $ such that for all elements $ A $ of $ C $ , the exponential comparison map of $ F $ and $ A $ is an isomorphism .
* `PadicInt__toZModHom` (flatten (passes 1-5); `'\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''` / `'\'\\\'\\\\\\\'\\\\\\\\\\\\\\\'p-adic_Adj\\\\\\\\\\\\\\\'\\\\\\\'\\\'\''`): definition . let $ v $ be an element of $ \Natural $ . let $ f $ be a function from number integers ['\'\\\'p-adic_Adj\\\'\''] of $ p $ to elements of $ \Natural $ . assume that for all number integers ['\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''] $ x_{1} $ of $ p $ , $ x_{1} - f ( x_{1} ) $ is an element of the span of $ \SingletonsingletonMACRoEW { v } $ ( &+ $ &+ \mathrm{f\_spec} &+ $ &+ ) . assum
* `PadicInt__toZModHom` (#NLG rules; `'\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''` / `'\'\\\'\\\\\\\'\\\\\\\\\\\\\\\'\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\'p-adic_Adj\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\'\\\\\\\\\\\\\\\'\\\\\\\'\\\'\''`): definition . let $ v \in \Natural $ . let $ f $ be a function from number integers ['\'\\\'\\\\\\\'p-adic_Adj\\\\\\\'\\\'\''] of $ p $ to elements of $ \Natural $ such that for all number integers ['\'\\\'\\\\\\\'\\\\\\\\\\\\\\\'p-adic_Adj\\\\\\\\\\\\\\\'\\\\\\\'\\\'\''] $ x_{1} $ of $ p $ , $ x_{1} - f ( x_{1} ) $ is an element of the span of $ \SingletonsingletonMACRoEW { v } $ . assume that for

