# The round trip of NLG and semantics over mathlib-informath

Made by roundtrip-check.py with RunInformath -check-nlg-semantics (Informath doc/nlg-and-semantics.md, doc/nlg-semantics-check.md).

## Statements

9080 judgements: 9076 with MathCore trees, 0 without (no annotation), 3 given up (time limit or failure).

521386 variants; 0 lost, in 0 judgements (0 of them in the default output).

| stage | variants | exact | same hypotheses | equivalent | lost |
|---|---:|---:|---:|---:|---:|
| flatten (passes 1-5) | 32410 | 2726 | 29684 | 0 | 0 |
| aggregate | 25950 | 158 | 21625 | 4167 | 0 |
| variations | 434723 | 6424 | 172883 | 255416 | 0 |
| letDeclared (default output) | 24120 | 2063 | 18958 | 3099 | 0 |
| negated, implied, scoped | 685 | 18 | 577 | 90 | 0 |
| varless | 3420 | 0 | 2111 | 1309 | 0 |
| insitu | 17 | 0 | 17 | 0 | 0 |
| collectivize | 61 | 6 | 51 | 4 | 0 |
| **all** | 521386 | 11395 | 245906 | 264085 | 0 |

### By the first normalization step that makes t and the semantics of t' equal

| step | variants |
|---|---:|
| connectives | 25991 |
| hypothesis variables | 192400 |
| exact | 11395 |
| hypotheses split and sorted | 111565 |
| coercions | 27583 |
| conclusion as hypotheses | 152217 |
| structure clauses | 96 |
| notation | 99 |
| distribution | 40 |

### Where the lost ones differ

The head functions of the smallest subtrees where the normalized t and the normalized semantics of t' differ, with the variants, judgements and an example.

| t | semantics of t' | variants | judgements | example |
|---|---|---:|---:|---|

### Modules with most judgements with lost variants

| module | judgements |
|---|---:|

### Examples of lost variants


## Definitions

38972 judgements: 38867 with MathCore trees, 0 without (no annotation), 105 given up (time limit or failure).

227391 variants; 184 lost, in 17 judgements (1 of them in the default output).

| stage | variants | exact | same hypotheses | equivalent | lost |
|---|---:|---:|---:|---:|---:|
| flatten (passes 1-5) | 75039 | 20278 | 54716 | 37 | 8 |
| letDeclared (default output) | 25252 | 6301 | 18682 | 267 | 2 |
| variations | 107259 | 14141 | 89569 | 3403 | 146 |
| aggregate | 13695 | 1579 | 11901 | 187 | 28 |
| collectivize | 101 | 3 | 96 | 2 | 0 |
| varless | 5586 | 0 | 5554 | 32 | 0 |
| negated, implied, scoped | 437 | 69 | 363 | 5 | 0 |
| insitu | 22 | 5 | 17 | 0 | 0 |
| **all** | 227391 | 42376 | 180898 | 3933 | 184 |

### By the first normalization step that makes t and the semantics of t' equal

| step | variants |
|---|---:|
| exact | 42376 |
| connectives | 60735 |
| coercions | 77075 |
| notation | 783 |
| distribution | 2687 |
| structure clauses | 1772 |
| hypothesis variables | 40823 |
| hypotheses split and sorted | 636 |
| bound variables | 8 |
| conclusion as hypotheses | 312 |
| lost | 184 |

### Where the lost ones differ

The head functions of the smallest subtrees where the normalized t and the normalized semantics of t' differ, with the variants, judgements and an example.

| t | semantics of t' | variants | judgements | example |
|---|---|---:|---:|---|
| `NounKind` | `ClassKind` | 100 | 5 | SetLike__GradedMonoid__structure |
| `"S"` | `"R"` | 40 | 1 | IsAbsoluteValue__structure |
| `AdjProp` | `OrProp` | 22 | 5 | CategoryTheory__IsCofilteredOrEmpty |
| `"C"` | `"D"` | 8 | 2 | CategoryTheory__MonoidalClosedFunctor__structure |
| `Adj2Prop` | `CoreExistProp` | 6 | 1 | CategoryTheory__Biproduct__columnNonzeroOfIso |
| `AdjProp` | `CoreExistProp` | 4 | 1 | LinearMap__IsSelfAdjoint |
| `"U"` | `"V"` | 2 | 1 | Prefunctor__MapReverse__structure |
| `"B"` | `"F"` | 2 | 1 | MemTrivializationAtlas__structure |

### Modules with most judgements with lost variants

| module | judgements |
|---|---:|
| Mathlib.CategoryTheory.Filtered.Basic | 4 |
| Mathlib.CategoryTheory.Preadditive.Biproducts | 1 |
| Mathlib.CategoryTheory.Monoidal.Closed.Ideal | 1 |
| Mathlib.CategoryTheory.Limits.Sifted | 1 |
| Mathlib.CategoryTheory.Monoidal.Closed.Functor | 1 |
| Mathlib.Algebra.Lie.Graded | 1 |
| Mathlib.RingTheory.GradedAlgebra.Basic | 1 |
| Mathlib.Algebra.Order.AbsoluteValue.Basic | 1 |
| Mathlib.Algebra.Lie.Extension | 1 |
| Mathlib.LinearAlgebra.SesquilinearForm.Basic | 1 |
| Mathlib.Topology.FiberBundle.Basic | 1 |
| Mathlib.Combinatorics.Quiver.Symmetric | 1 |
| Mathlib.LinearAlgebra.RootSystem.Defs | 1 |
| Mathlib.Algebra.GradedMonoid | 1 |

### Examples of lost variants

* `IsAbsoluteValue__structure` (aggregate; `"S"` / `"R"`): definition . let $ S $ be a semiring such that $ S $ is a partially ordered set . then an absolute value is a semiring $ R $ with a function $ f $ from $ R $ to $ S $ such that for all elements $ x $ of $ R $ , $ 0 \leq f ( x ) $ and $ \EqtMACRoDE { f ( x ) } { 0 } $ , if and only if $ \EqtMACRoDE { x } { 0 } $ and for all elements $ x $ and $ y $ of $ R $ , $ f ( x + y ) \leq f ( x ) + f ( y ) $ 
* `Prefunctor__MapReverse__structure` (aggregate; `"U"` / `"V"`): definition . let $ U $ be a quiver such that $ U $ has reverses . then a map reverse is a quiver $ V $ with a prefunctor $ r $ of $ U $ and $ V $ such that for all elements $ u $ and $ v $ of $ U $ , for all homomorphisms $ e $ of $ u $ and $ v $ , the map of $ r $ and the reverse of $ e $ is equal to the reverse of the map of $ r $ and $ e $ .
* `CategoryTheory__Biproduct__columnNonzeroOfIso` (flatten (passes 1-5); `Adj2Prop` / `CoreExistProp`): definition . let $ s $ be an element of $ S $ . assume that the identity morphism of $ S_{1} ( s ) $ is distinct from $ 0 $ ( &+ $ &+ \mathrm{nz} &+ $ &+ ) . let $ f $ be a homomorphism of $ \CategoryTheoryLimitsbiproductMACRoAC { S_{1} } $ and $ \CategoryTheoryLimitsbiproductMACRoAC { T_{1} } $ . then the column nonzero of $ s $ and $ f $ is a truncation of $ \mathrm{PSigma} $ applied to the func
* `CategoryTheory__IsCofilteredOrEmpty` (flatten (passes 1-5); `AdjProp` / `OrProp`): definition . let $ C $ be a set . then $ C $ is cofiltered or empty , if $ C $ is a category , for all elements $ X $ of $ C $ , for all elements $ Y $ of $ C $ , there exists an element $ W $ of $ C $ such that there exists a homomorphism $ x $ of $ W $ and $ X $ such that there exists a homomorphism $ x_{1} $ of $ W $ and $ Y $ such that $ \mathrm{True} $ and for all elements $ X $ of $ C $ , fo
* `LinearMap__IsSelfAdjoint` (flatten (passes 1-5); `AdjProp` / `CoreExistProp`): definition . let $ B $ be a linear map of $ M $ and the set of linear maps of $ M $ and $ X $ . let $ f $ be a function from $ M $ to $ M $ . then $ B $ is self-adjoint with respect to a bilinear map , if $ \mathrm{LinearMap\_\_IsAdjointPair} ( B , B , f , f ) $ .
* `SetLike__GradedMonoid__structure` (aggregate; `NounKind` / `ClassKind`): definition . let $ T $ be an additive monoid . let $ R $ be a monoid . then a graded monoid is a graded one $ S $ with a function $ A $ from $ T $ to $ S $ such that for all elements $ i $ and $ j $ of $ T $ , for all elements $ \mathrm{gi} $ and $ \mathrm{gj} $ of $ R $ , if $ \MembershipmemMACRoDQ { A ( i ) } { \mathrm{gi} } $ , then if $ \MembershipmemMACRoDQ { A ( j ) } { \mathrm{gj} } $ , the
* `MemTrivializationAtlas__structure` (aggregate; `"B"` / `"F"`): definition . let $ B $ be a topological space such that for all elements $ b $ of $ B $ , $ E ( b ) $ is a topological space . then a membership trivialization atlas is a topological space $ F $ with a trivialization $ e $ of $ F $ and $ \mathrm{Bundle\_\_TotalSpace\_\_proj} $ such that $ e $ is an element of the trivialization atlas of $ F $ and $ E $ .
* `CategoryTheory__MonoidalClosedFunctor__structure` (aggregate; `"C"` / `"D"`): definition . let $ C $ be a category such that $ C $ is a cartesian monoidal category and $ \mathrm{CategoryTheory\_\_MonoidalClosed} ( C ) $ . then a monoidal closed functor is a category $ D $ with a functor $ F $ of $ C $ and $ D $ such that for all elements $ A $ of $ C $ , the exponential comparison map of $ F $ and $ A $ is an isomorphism .

