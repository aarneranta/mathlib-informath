/-
Export the statements of Mathlib declarations to Informath's Dedukti dialect.

    lake exe export Mathlib.Data.Nat.Prime.Defs [more modules]   # -> out/<Module>.dk, .json
    lake exe export --structures      # the classes of structures.txt as structure definitions

For each declaration of the given modules (theorems, definitions, axioms, and
structures and classes with their fields), the type is translated:

* a binder `(x : α)` with `α : Type` becomes `(x : Elem α)`, one with `α : Prop`
  becomes `(h : Proof α)`, and `(α : Type u)` becomes `(α : Set)`;
* an instance binder `[Group G]` becomes a hypothesis `(_ : Proof (Group G))`;
* in applications, instance arguments are dropped; the implicit ones are kept,
  and out/<Module>-hide.dkgf has the #HIDE lines that hide them in the readings
  (and #COERCION lines for the coercions, which are kept too);
* but where a statement gives an instance that instance resolution would not
  find (`IsOpen[f] = IsOpen[g]` with `{f g : TopologicalSpace X}`, `IsOpen[t.induced f]`),
  it is kept: the constant becomes its variant `IsOpen__in X f s` ("s is open
  in f"), the structure is a named element of the set of the class's
  structures, `(f : Elem (TopologicalSpace__on X))` ("let f be a topology on
  X"), and an equality of such operations is stated pointwise (see givenInstance);
* the constants of `mapping.tsv` become Informath's own (`Dvd.dvd` is `divide`,
  `Nat.Prime` is `prime`, ...), so that Informath's base readings apply, and the
  logical constants become `and`, `or`, `if`, `not`, `iff`, `forall`, `exists`;
* any other constant keeps its Lean name, with `.` written `__`.

Each declaration is preceded by `(; //LEAN:<name> ;)`.  out/<Module>.json has,
for each declaration, its Lean name, its Dedukti name, its kind, its docstring
and Lean's own statement, for the index and for comparing the readings.
out/<Module>-deps.dk declares the constants that the statements use but that
are neither exported nor mapped, with their types translated the same way.

The output is meant to be read by Informath, not checked by Dedukti: universe
levels, instances and computation rules are left out.  The definitions export
(--definitions) keeps the explicit arguments only, as its entries count them.
-/
import Lean
import Mathlib.Tactic.Translate.ToAdditive

open Lean Meta

/-- Lean name -> Dedukti identifier: `.` as `__`, other non-identifier
characters as `_u<hex>_`. -/
def mangle (n : Name) : String :=
  let s := n.toString (escape := false)
  -- the words of Informath's framework are not to be redefined
  let s := if ["Set", "Elem", "Prop", "Proof", "Type"].contains s then "Lean_" ++ s else s
  s.foldl (fun acc c =>
    if c == '.' then acc ++ "__"
    else if c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' then acc.push c
    else acc ++ s!"_u{String.ofList (Nat.toDigits 16 c.toNat)}_") ""

structure St where
  mapping : Std.HashMap Name String := {}
  used : Std.HashSet Name := {}      -- unmapped constants referred to
  derived : Std.HashMap String String := {}  -- c__app, c__in, C__on constants and their types
  derivedHide : Std.HashMap String (Array Nat) := {}  -- the hidden arguments of c__in
  collecting : Bool := false         -- the first pass of a statement (see givenInstance)
  givenKeys : Std.HashSet String := {}  -- the instance types whose arguments are kept
  namedLocals : Std.HashSet FVarId := {}  -- the locals that are named structures
  binders : Std.HashSet Name := {}   -- constants of binders.txt
  names : Std.HashSet String := {}   -- variable names in use
  proofMode : Bool := false          -- in a proof term, theorems keep all their arguments
  -- the statements and proofs of the modules: the constants that are not
  -- mapped keep their implicit arguments, which #HIDE lines of out/<M>-hide.dkgf
  -- hide in the readings, and coercions are kept (#COERCION); the definitions
  -- export (--definitions) shows the explicit arguments only, as before
  keepImplicit : Bool := false
  keepAll : Std.HashSet Name := {}   -- mapped to rules of nd.dk, which take all arguments
  opers : Std.HashMap FVarId (String × String) := {}  -- binary operations of a structure: name, carrier

abbrev M := StateRefT St MetaM

/-- The coercions: the identity in the readings (#COERCION), the casts
between number types, the values of subtypes and of bundled sets. -/
def coercions : List Name :=
  [``Nat.cast, ``Int.cast, ``NatCast.natCast, ``IntCast.intCast, ``Subtype.val, `SetLike.coe,
   `Fin.val, `Subgroup.toSubmonoid, `AddSubgroup.toAddSubmonoid, `Submonoid.toSubsemigroup, ``Subtype.mk]

/-- A sort, or a sort as an outParam (the collection type of Membership). -/
def sortish (t : Expr) : Bool :=
  t.isSort || (t.isAppOfArity ``outParam 1 && t.appArg!.isSort)

/-- A variable name in ASCII as Informath reads it: a Greek letter by its name
(ε as epsilon, which Informath shows as \epsilon), a subscript digit as a digit
(x₀ as x0, shown as x_{0}). -/
def asciiName (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | 'α' => "alpha" | 'β' => "beta" | 'γ' => "gamma" | 'δ' => "delta" | 'ε' => "epsilon"
    | 'ζ' => "zeta" | 'η' => "eta" | 'θ' => "theta" | 'ι' => "iota" | 'κ' => "kappa"
    | 'λ' => "lambda" | 'μ' => "mu" | 'ν' => "nu" | 'ξ' => "xi" | 'π' => "pi" | 'ρ' => "rho"
    | 'σ' => "sigma" | 'τ' => "tau" | 'υ' => "upsilon" | 'φ' => "phi" | 'χ' => "chi"
    | 'ψ' => "psi" | 'ω' => "omega" | 'Γ' => "Gamma" | 'Δ' => "Delta" | 'Θ' => "Theta"
    | 'Λ' => "Lambda" | 'Ξ' => "Xi" | 'Π' => "Pi" | 'Σ' => "Sigma" | 'Φ' => "Phi"
    | 'Ψ' => "Psi" | 'Ω' => "Omega"
    | '₀' => "0" | '₁' => "1" | '₂' => "2" | '₃' => "3" | '₄' => "4" | '₅' => "5"
    | '₆' => "6" | '₇' => "7" | '₈' => "8" | '₉' => "9"
    | c => c.toString) ""

/-- A variable name for a binder: the user's name if it is a plain identifier
and free, else a fresh one. -/
def freshName (n : Name) (prop : Bool) (sort : Bool := false) : M String := do
  let raw := (n.eraseMacroScopes.toString (escape := false))
  -- the name the user gave, in ASCII, except a type's, which gets a Latin capital (below)
  let base0 := if sort then raw else asciiName raw
  let ok := !base0.isEmpty && base0.all (fun c => c.isAlphanum || c == '_' || c == '\'') &&
    !(base0.toList.head?.map Char.isDigit |>.getD false) && !n.hasMacroScopes
  -- a Greek type variable (α : Type u) gets the Latin capital a textbook would
  -- use for a set: "Let X and Y be sets"
  let latin := match raw with
    | "α" => "X" | "β" => "Y" | "γ" => "Z" | "δ" => "W" | "ι" => "I" | "κ" => "J"
    | "σ" => "S" | "τ" => "T" | "ω" => "U" | _ => "X"
  let base := if ok then base0 else if prop then "h" else if sort && !n.hasMacroScopes then latin else "x"
  let st ← get
  if !st.names.contains base then
    modify fun s => { s with names := s.names.insert base }
    return base
  let mut i := 1
  while (← get).names.contains s!"{base}{i}" do i := i + 1
  let nm := s!"{base}{i}"
  modify fun s => { s with names := s.names.insert nm }
  return nm

/-- The positions of the explicit arguments of a constant. -/
def explicitArgs (c : Name) : MetaM (Array Bool) := do
  let info ← getConstInfo c
  forallTelescope info.type fun xs _ => do
    xs.mapM fun x => return (← x.fvarId!.getBinderInfo) == .default

/-- The positions of the arguments of a constant that are not instances. -/
def nonInstanceArgs (c : Name) : MetaM (Array Bool) := do
  let info ← getConstInfo c
  forallTelescope info.type fun xs _ => do
    xs.mapM fun x => return (← x.fvarId!.getBinderInfo) != .instImplicit

/-- A numeral in Informath's base: a digit, or nn d (...) for more digits. -/
def numeral (n : Nat) : String :=
  let ds := Nat.toDigits 10 n
  match ds with
  | [d] => d.toString
  | _ =>
    let rec go : List Char → String
      | [d] => s!"(nd {d})"
      | d :: rest => s!"(nn {d} {go rest})"
      | [] => "0"
    go ds

def paren (s : String) : String := if s.contains ' ' then s!"({s})" else s

/-- A class whose instances a statement never names: decidability, which is
computational, and the technical classes that a textbook never states (the
coercion classes FunLike and SetLike, the compatibility of an order or an
action with the operations, the bare notation classes Zero, Add, ...). -/
def technicalClass (ty : Expr) : Bool :=
  match ty.getAppFn.constName? with
  | some c =>
    let s := c.toString
    s.startsWith "Decidable" || technicalClasses.contains s ||
    ["PosMul", "MulPos", "Covariant", "Contravariant"].any (s.startsWith ·) ||
    ["LeftMono", "RightMono", "LeftStrictMono", "RightStrictMono", "LeftReflectLT",
     "RightReflectLT", "LeftReflectLE", "RightReflectLE", "HomClass"].any (s.endsWith ·)
  | none => false
where
  technicalClasses : List String :=
    ["FunLike", "DFunLike", "EquivLike", "SetLike", "SMulCommClass", "IsScalarTower",
     "ContinuousSMul", "ContinuousConstSMul", "RingHomSurjective", "IsRCLikeNormedField",
     "Zero", "One", "Add", "Mul", "Neg", "Inv", "Sub", "Div", "SMul", "VAdd", "Pow",
     "Nontrivial", "Inhabited", "Nonempty", "NatCast", "IntCast", "CharZero",
     "SummationFilter.NeBot", "SummationFilter.IsCountablyGenerated"]

/-- A class whose instances are never named structures (see givenInstance),
though statements assume them: the technical ones, the heterogeneous
notation classes, whose instances on sets are the scoped pointwise ones
(a • s), the casts, and the classes whose instances are all the same as far
as a statement goes (the cardinality of a Fintype). -/
def unnamedClass (ty : Expr) : Bool :=
  technicalClass ty ||
  match ty.getAppFn.constName? with
  | some c => ["HSMul", "HVAdd", "HMul", "HAdd", "HSub", "HDiv", "HPow", "HMod", "HAnd", "HOr",
               "RatCast", "NNRatCast", "Fintype", "Finite", "Encodable", "Countable",
               "Unique", "Membership", "Function.HasUncurry"].contains c.toString
  | none => false

/-- A given instance without the parent projections around it: the `LE` of a
preorder `A`, `Preorder.toLE A`, is `A`, as a textbook says "≤ in A". -/
partial def stripParents (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  match e.getAppFn with
  | .const (.str cls field) _ =>
    if e.getAppNumArgs > 0 && field.startsWith "to" && isClass (← getEnv) cls then
      let a := e.appArg!
      if (← whnfR (← inferType a)).getAppFn.constName? == some cls then
        return ← stripParents a
    return e
  | _ => return e

/-- The positions of the instance arguments of a constant. -/
def instanceArgs (c : Name) : MetaM (Array Bool) := do
  let info ← getConstInfo c
  forallTelescope info.type fun xs _ => do
    xs.mapM fun x => return (← x.fvarId!.getBinderInfo) == .instImplicit

/-- Whether an instance argument is given by the statement rather than found
by instance resolution, so that it has to be kept: `IsOpen[f]` beside
`IsOpen[g]`, `IsOpen[t.induced f]`, `𝓤[U]` beside `m.toUniformSpace`.  A
statement is translated twice (see statement).  The first pass (collecting)
asks instance resolution, in the statement's context, for each instance
argument, and notes the type of any argument it would not find; the second
keeps every instance argument of a type so noted, on both sides of
`IsOpen[f] = IsOpen[g]`, and notes the locals in it as named structures
(`namedLocals`), which become elements of the set of the class's structures.
Decidability and the technical classes are never kept. -/
def givenInstance (a : Expr) : M Bool := do
  let ty ← instantiateMVars (← inferType a)
  if unnamedClass ty || (← isProp ty) then return false
  let key := toString (← ppExpr ty)
  if (← get).collecting then
    let found ← try synthInstance? ty catch _ => pure none
    let same ← match found with
      | some i => (try isDefEq i a catch _ => pure false)
      | none => pure false
    if !same then
      if (← IO.getEnv "EXPORT_DEBUG_GIVEN").isSome then
        let fs ← match found with
          | some i => do pure (toString (← ppExpr i))
          | none => pure "none"
        IO.eprintln s!"GIVEN {key} | {← ppExpr a} | {fs}"
      modify fun st => { st with givenKeys := st.givenKeys.insert key }
    return false
  if !(← get).givenKeys.contains key then return false
  let lctx ← getLCtx
  for id in (collectFVars {} (← stripParents a)).fvarIds do
    if let some d := lctx.find? id then
      if (← isClass? d.type).isSome && !(← isProp d.type) then
        modify fun st => { st with namedLocals := st.namedLocals.insert id }
  return true

/-- Whether an expression has a given instance argument (see givenInstance). -/
partial def hasGivenInstance (e : Expr) : M Bool := do
  let .const c _ := e.getAppFn | return false
  let inst ← try instanceArgs c catch _ => pure #[]
  let args := e.getAppArgs
  for i in [0:args.size] do
    if inst.getD i false then
      if ← givenInstance args[i]! then return true
    else if ← hasGivenInstance args[i]! then return true
  return false

mutual

/-- An expression of type Prop, an object, or a type, in Dedukti. -/
partial def tr (e : Expr) : M String := do
  match e with
  | .mdata _ b => tr b
  | .fvar id =>
    if let some (nm, _) := (← get).opers.get? id then return nm
    return (← id.getUserName).toString (escape := false)  -- names are fixed when bound
  | .sort .zero => return "Prop"
  | .sort _ => return "Set"
  | .lit (.natVal n) => return numeral n
  | .lit (.strVal s) => return s!"\"{s}\""
  | .const c _ => app c #[] e
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ => app c args e
    | _ => do
      -- a binary operation of a structure applied: appOper G op a b
      if let .fvar id := f then
        if let some (nm, carrier) := (← get).opers.get? id then
          if args.size == 2 then
            let app := if nm == "{|≤|}" || nm == "{|<|}" then "appRel"
              else if nm == "{|•|}" then "appAction" else "appOper"
            return s!"{app} {carrier} {nm} {paren (← tr args[0]!)} {paren (← tr args[1]!)}"
          if args.size == 1 then
            let app := if nm == "{|-|}" then "appPrefixUOper" else "appUOper"
            return s!"{app} {carrier} {nm} {paren (← tr args[0]!)}"
      if (← get).proofMode && f.isFVar && (← isProp (← inferType e)) then
        -- a hypothesis applied: an elimination rule for each argument
        let mut cur ← tr f
        let mut ty ← inferType f
        for a in args do
          ty ← whnf ty
          match ty with
          | .forallE n A B _ =>
            if (← isProp A) then
              cur := s!"ifE {paren (← tr A)} {paren (← tr (B.instantiate1 a))} {paren cur} {paren (← tr a)}"
            else
              let nm ← freshName n false
              let bs ← withLocalDecl (Name.mkSimple nm) .default A fun x => tr (B.instantiate1 x)
              cur := s!"forallE {paren (← tr A)} ({nm} => {bs}) {paren cur} {paren (← tr a)}"
            ty := B.instantiate1 a
          | _ => cur := s!"{paren cur} {paren (← tr a)}"
        return cur
      let fs ← tr f
      let as ← args.mapM tr
      return " ".intercalate (paren fs :: (as.map paren).toList)
  | .lam n t b bi => binder n t b bi true
  | .forallE n t b bi => binder n t b bi false
  | .letE _ _ v b _ => tr (b.instantiate1 v)
  | .proj s i b => do
    if (s == ``And || s == ``Iff) && i < 2 then
      let as := (← whnf (← inferType b)).getAppArgs
      if as.size == 2 then
        let r := if s == ``And then (if i == 0 then "andEl" else "andEr")
                 else (if i == 0 then "iffEl" else "iffEr")
        return s!"{r} {paren (← tr as[0]!)} {paren (← tr as[1]!)} {paren (← tr b)}"
    return s!"{mangle s}__proj{i} {paren (← tr b)}"
  | _ => return "UNSUPPORTED"

/-- A λ or a Π / ∀: a quantifier or an implication in a Prop, a function
type elsewhere. -/
partial def binder (n : Name) (t b : Expr) (bi : BinderInfo) (isLam : Bool)
    (plain : Nat := 0) : M String := do
  let prop ← isProp t
  let nm ← freshName n prop (sortish t)
  -- in a proof, a λ that proves an implication or a ∀ is its introduction
  -- rule, ifI or forallI; but not the λs that rules take as arguments (plain)
  let intro ← if isLam && plain == 0 && (← get).proofMode then isProp (← inferType (.lam n t b bi))
              else pure false
  -- the local gets the chosen name, so that tr of its fvar prints it
  withLocalDecl (Name.mkSimple nm) bi t fun y => do
      let body := b.instantiate1 y
      let bs ← match body with
        | .lam n2 t2 b2 bi2 => if plain > 1 then binder n2 t2 b2 bi2 true (plain - 1) else tr body
        | _ => tr body
      if isLam then
        if intro then
          let bodyTy ← inferType body
          if prop then
            return s!"ifI {paren (← tr t)} {paren (← tr bodyTy)} ({nm} => {bs})"
          return s!"forallI {paren (← tr t)} ({nm} => {← tr bodyTy}) ({nm} => {bs})"
        return s!"{nm} => {bs}"
      let bodyProp ← isProp body
      if bodyProp then
        if prop && !b.hasLooseBVars then
          return s!"if {paren (← tr t)} {paren bs}"
        if prop then
          return s!"forall (Proof {paren (← tr t)}) ({nm} => {bs})"
        -- a named structure (see givenInstance) ranges over the set of the structures
        let named := (← get).namedLocals.contains y.fvarId!
        let dom ← if named then typeOf t else tr t
        return s!"forall {paren dom} ({nm} => {bs})"
      if !b.hasLooseBVars then
        return s!"{← hypoType t} -> {bs}"
      return s!"({nm} : {← hypoType t !((← get).namedLocals.contains y.fvarId!)}) -> {bs}"

/-- The Set an object of type t belongs to: Nat for ℕ, and for a class, the
set of its structures (TopologicalSpace X: TopologicalSpace__on X). -/
partial def typeOf (t : Expr) : M String := do
  if let some s ← structureSet t then return s
  tr t

/-- For a class C applied to its parameters, the set of its structures on
them, C__on (the topologies on X), declared in the deps with the class's
parameters but its instances: none if t is not a class. -/
partial def structureSet (t : Expr) : M (Option String) := do
  let t ← instantiateMVars t
  let some n := t.getAppFn.constName? | return none
  unless isClass (← getEnv) n do return none
  -- a Prop-valued class (Nontrivial, DenselyOrdered) is a predicate, and the
  -- instances of the technical classes are never named (Decidable p); and
  -- only a class applied to all its parameters is a type
  if (← isProp t) || unnamedClass t then return none
  unless (← whnf (← inferType t)).isSort do return none
  let nm := mangle n ++ "__on"
  let inst ← try instanceArgs n catch _ => pure #[]
  let params := (t.getAppArgs.toList.zip (inst.toList ++ List.replicate t.getAppNumArgs false)).filter (!·.2)
                  |>.map (·.1)
  if !((← get).derived.contains nm) then
    let (ty, _) ← derivedDecl (← getConstInfo n).type (!inst.getD · false) (fun _ => false) true
    modify fun st => { st with derived := st.derived.insert nm ty }
  let as ← params.mapM tr
  return some (" ".intercalate (nm :: as.map paren))

/-- The binders of a derived constant (c__in, C__on) from the type of c: those
at the kept positions, the given instances as elements of the sets of the
structures; the positions of the implicit ones among them (for #HIDE); and
the result, Set for C__on. -/
partial def derivedType (t : Expr) (keptAt givenAt : Nat → Bool) (setResult : Bool) (i k : Nat) :
    M (List String × List Nat × String) := do
  match t with
  | .forallE n ty b bi =>
    let nm ← freshName n (← isProp ty) (sortish ty)
    withLocalDecl (Name.mkSimple nm) bi ty fun y => do
      let k' := if keptAt i then k + 1 else k
      let (hs, hid, res) ← derivedType (b.instantiate1 y) keptAt givenAt setResult (i + 1) k'
      if !keptAt i then return (hs, hid, res)
      let named := givenAt i || (← get).namedLocals.contains y.fvarId!
      let h := s!"({nm} : {← hypoType ty (!named)})"
      return (h :: hs, if bi == .implicit || bi == .strictImplicit then k' :: hid else hid, res)
  | body =>
    if setResult then return ([], [], "Set")
    let res ← if (← isProp body) then pure s!"Proof {paren (← tr body)}" else hypoType body false
    return ([], [], res)

/-- The declared type of a derived constant and its hidden arguments, its
variables named afresh as in a declaration of its own. -/
partial def derivedDecl (t : Expr) (keptAt givenAt : Nat → Bool) (setResult : Bool) :
    M (String × Array Nat) := do
  -- in two passes, as a statement (see givenInstance), in a state of its own
  let s0 ← get
  set { s0 with names := {}, collecting := true, givenKeys := {}, namedLocals := {} }
  discard <| derivedType t keptAt givenAt setResult 0 0
  let keys := (← get).givenKeys
  modify fun st => { st with names := {}, collecting := false, givenKeys := keys, namedLocals := {} }
  let (hs, hid, res) ← derivedType t keptAt givenAt setResult 0 0
  let derived := (← get).derived
  let derivedHide := (← get).derivedHide
  let used := (← get).used
  set { s0 with derived, derivedHide, used }
  return (" -> ".intercalate (hs ++ [res]), hid.toArray)

/-- The type of a hypothesis: Elem α, Proof P, or Set.  An instance of a
class is a proof of it, as classes are predicates here; a variable of a class
type that is not an instance (inst false), a named structure, is an element
of the set of its structures. -/
partial def hypoType (t : Expr) (inst : Bool := true) : M String := do
  if (← isProp t) then return s!"Proof {paren (← tr t)}"
  if (← isClass? t).isSome then
    if !inst then
      if let some s ← structureSet t then return s!"Elem {paren s}"
    return s!"Proof {paren (← tr t)}"
  if t.isProp then return "Prop"
  if sortish t then return "Set"
  if (← isType t) then
    -- t is a type of types (α → Type): a function into Set
    if (← whnf t).isForall then return s!"({← tr t})"
  return s!"Elem {paren (← tr t)}"

/-- An application of a constant, with the special cases of the mapping. -/
partial def app (c : Name) (args : Array Expr) (whole : Expr) : M String := do
  -- pattern matching on a conjunction or an existential (fun δ ⟨δ_pos, Hf⟩ => t,
  -- match h with | ⟨w, hw⟩ => t), which Lean compiles to a matcher: the matcher
  -- unfolded to casesOn, and that to the elimination rules, And.left and
  -- And.right in the body, or Exists.elim (existsE) with the body as its function
  if ← Meta.isMatcher c then
    if let some m ← Meta.matchMatcherApp? whole then
      if m.discrs.size == 1 && m.alts.size == 1 && m.remaining.isEmpty then
        let d := m.discrs[0]!
        let dty ← whnfR (← inferType d)
        let alt := m.alts[0]!
        if dty.isAppOfArity ``And 2 then
          let (a, b) := (dty.appFn!.appArg!, dty.appArg!)
          let l := mkApp3 (.const ``And.left []) a b d
          let r := mkApp3 (.const ``And.right []) a b d
          return ← tr (← Core.betaReduce (mkApp2 alt l r))
        if dty.isAppOfArity ``Exists 2 then
          let (α, p) := (dty.appFn!.appArg!, dty.appArg!)
          return ← tr (mkApp5 (.const ``Exists.elim [← getLevel α]) α p (← inferType whole) d alt)
  if c == ``And.casesOn && args.size == 5 then
    let (a, b, t, f) := (args[0]!, args[1]!, args[3]!, args[4]!)
    let l := mkApp3 (.const ``And.left []) a b t
    let r := mkApp3 (.const ``And.right []) a b t
    return ← tr (← Core.betaReduce (mkApp2 f l r))
  if c == ``Exists.casesOn && args.size == 5 then
    let (α, p, t, f) := (args[0]!, args[1]!, args[3]!, args[4]!)
    let u ← getLevel α
    return ← tr (mkApp5 (.const ``Exists.elim [u]) α p (← inferType whole) t f)
  -- a coercion to a function, DFunLike.coe f x (n.factorization p): when f is
  -- an application of a constant, the constant applied to its explicit
  -- arguments and to x, as one constant c__app declared in the deps
  if c == `DFunLike.coe && args.size ≥ 6 then
    let f := args[4]!
    let rest := args.extract 5 args.size
    match f.getAppFn with
    | .const fc _ => do
      let fexpl ← try explicitArgs fc catch _ => pure (f.getAppArgs.map fun _ => true)
      let fshown := (f.getAppArgs.toList.zip (fexpl.toList ++ List.replicate f.getAppNumArgs true)).filter (·.2)
                     |>.map (·.1)
      let all := fshown ++ rest.toList
      let nm := mangle fc ++ "__app"
      if !((← get).derived.contains nm) then
        let mut hs := #[]
        let mut i := 0
        for a in all do
          i := i + 1
          hs := hs.push s!"(a{i} : {← hypoType (← inferType a)})"
        let ty := " -> ".intercalate (hs.toList ++ [← hypoType (← inferType whole)])
        modify fun st => { st with derived := st.derived.insert nm ty }
      let as ← all.mapM tr
      return " ".intercalate (nm :: as.map paren)
    | _ => do
      let fs ← tr f
      let as ← rest.mapM tr
      return " ".intercalate (paren fs :: (as.map paren).toList)
  -- the order on sets and finite sets is inclusion, and its lattice operations
  -- union and intersection: s ⊆ t is LE.le (Set α) s t, s ∪ t is Max.max
  let setLike (t : Expr) : Bool := match t.getAppFn.constName? with
    | some n => n == `Set || n == `Finset
    | none => false
  if args.size ≥ 1 && setLike args[0]! then
    let setOp : Option Name :=
      if c == ``LE.le && args.size == 4 then some `Set.Subset
      else if c == ``LT.lt && args.size == 4 then some `HasSSubset.SSubset
      else if c == ``Max.max && args.size == 4 then some `Union.union
      else if c == ``Min.min && args.size == 4 then some `Inter.inter
      else none
    -- with keepImplicit, as the applications they are, with their implicit
    -- arguments, if Lean can build them
    if (← get).keepImplicit then
      let built? : Option Expr ← try
          if let some op := setOp then pure (some (← mkAppM op #[args[2]!, args[3]!]))
          else if c == `Top.top && args.size == 2 then pure (some (← mkAppOptM `Set.univ #[some (args[0]!.appArg!)]))
          else if c == `Bot.bot && args.size == 2 then pure (some (← mkAppOptM `EmptyCollection.emptyCollection #[some args[0]!, none]))
          else pure none
        catch _ => pure none
      if let some e := built? then return ← tr e
    -- else (finite sets) by hand, with the type argument that #HIDE hides: the
    -- elements' type for Set.Subset and Set.univ, the collection's for the others
    let ty (elem : Bool) : M String := do
      if !(← get).keepImplicit then return ""
      let t := if elem then args[0]!.appArg! else args[0]!
      return " " ++ paren (← tr t)
    if let some op := setOp then
      modify fun s => { s with used := s.used.insert op }
      return s!"{mangle op}{← ty (op == `Set.Subset)} {paren (← tr args[2]!)} {paren (← tr args[3]!)}"
    if c == `Top.top && args.size == 2 then
      modify fun s => { s with used := s.used.insert `Set.univ }
      return s!"{mangle `Set.univ}{← ty true}"
    if c == `Bot.bot && args.size == 2 then
      modify fun s => { s with used := s.used.insert `EmptyCollection.emptyCollection }
      return s!"{mangle `EmptyCollection.emptyCollection}{← ty false}"
  -- the coercion of a bundled function not applied (⇑OrderDual.ofDual,
  -- f ∘ ⇑e) is the function itself
  if c == `DFunLike.coe && args.size == 5 then
    return ← tr args[4]!
  -- a composition applied, (f ∘ g) x, is f (g x) by definition, and a textbook
  -- writes it so (a symbol table entry words the composition itself, f ∘ g)
  if c == ``Function.comp && args.size ≥ 6 then
    return ← tr (mkAppN (.app args[3]! (.app args[4]! args[5]!)) (args.extract 6 args.size))
  -- outParam α is α, a hint to the elaborator
  if (c == ``outParam || c == ``semiOutParam) && args.size == 1 then
    return ← tr args[0]!
  -- numerals: OfNat.ofNat α n inst
  if c == ``OfNat.ofNat && args.size ≥ 2 then
    if let .lit (.natVal n) := args[1]!.consumeMData then return numeral n
  -- casts between number types are the identity in Informath's Num; with
  -- keepImplicit they are kept, and #COERCION lines say which argument the
  -- readings show
  if coercions.contains c && args.size ≥ 1 && !(← get).keepImplicit then
    return ← tr args.back!
  -- an element of a subtype, Subtype.mk x h, is x
  if c == ``Subtype.mk && args.size == 4 && !(← get).keepImplicit then
    return ← tr args[2]!
  -- ∃ x, p x  /  Exists (fun x => p x)
  if c == ``Exists && args.size == 2 then
    let p := args[1]!
    match p with
    | .lam n t b bi => do
      let s ← binder n t b bi true
      return s!"exists {paren (← typeOf t)} ({s})"
    | _ => return s!"exists {paren (← typeOf args[0]!)} (x => {paren (← tr p)} x)"
  -- equality: Eq on numbers, Eqt elsewhere
  if c == ``Eq && args.size == 3 then
    -- an equality of functions that differ in a given instance (IsOpen[f] =
    -- IsOpen[g], dist[x] = dist[y]): pointwise, as the functions are the
    -- operations of the structures, read as applied ("for all s, s is open in
    -- f iff s is open in g"); equivalent by funext and propext
    let fty ← whnf args[0]!
    let pointwise ← if !fty.isForall then pure false
      else if ← hasGivenInstance args[1]! then pure true
      else hasGivenInstance args[2]!
    if pointwise then
      let e ← forallTelescope fty fun xs cod => do
        let l := (mkAppN args[1]! xs).headBeta
        let r := (mkAppN args[2]! xs).headBeta
        let body ← if cod.isProp then pure (mkIff l r) else mkEq l r
        mkForallFVars xs body
      return ← tr e
    let ty ← typeOf args[0]!
    let a ← tr args[1]!; let b ← tr args[2]!
    if ty == "Nat" || ty == "Int" || ty == "Real" || ty == "Rat" then
      return s!"Eq {paren a} {paren b}"
    return s!"Eqt {paren ty} {paren a} {paren b}"
  -- an instance argument that the statement gives (IsOpen[f] s, x ≤ y in a
  -- preorder A) is kept: the constant is its variant c__in (IsOpen__in X f s),
  -- declared in the deps with the instance as an element of the set of the
  -- structures, and its implicit arguments hidden by #HIDE as the others'
  let isThmConst := match (← getEnv).find? c with
    | some (.thmInfo _) => true
    | _ => false
  if !isThmConst && !(← get).keepAll.contains c then
    let inst ← try instanceArgs c catch _ => pure #[]
    let mut given : Array Nat := #[]
    for i in [0:args.size] do
      if inst.getD i false then
        if ← givenInstance args[i]! then given := given.push i
    if !given.isEmpty then
      let present := (List.range args.size).filter (inst.getD · false)
      let nm := mangle c ++ "__in" ++
        (if given.toList == present then "" else "_" ++ "_".intercalate (given.toList.map (toString ·.succ)))
      let kept (i : Nat) : Bool := !(inst.getD i false) || given.contains i
      if !((← get).derived.contains nm) then
        let (ty, hidden) ← derivedDecl (← getConstInfo c).type kept given.contains false
        modify fun st => { st with derived := st.derived.insert nm ty,
                                   derivedHide := st.derivedHide.insert nm hidden }
      let mut as := #[]
      for i in [0:args.size] do
        if !kept i then continue
        let a ← if given.contains i then stripParents args[i]! else pure args[i]!
        as := as.push (paren (← tr a))
      return " ".intercalate (nm :: as.toList)
  let target := (← get).mapping.get? c
  let expl ← try explicitArgs c catch _ => pure (args.map fun _ => true)
  -- in a proof, a theorem is a rule whose premisses -proof-text reads off its
  -- type: so its arguments are kept, but for the instances of type classes,
  -- which the base of the proof texts leaves out of the rules' types; so is
  -- any other constant that is a proof (Equivalence.mk, propext), as its type
  -- is stated with its implicit arguments too
  let isThm ← match (← getEnv).find? c with
    | some (.thmInfo _) => pure true
    | some ci => if (← get).proofMode then (try isProp ci.type catch _ => pure false) else pure false
    | none => pure false
  let keep := (← get).keepAll.contains c
  let expl ← if keep then pure (args.map fun _ => true)
    else if ((← get).proofMode && isThm) || (target.isNone && (← get).keepImplicit) then
      try nonInstanceArgs c catch _ => pure (args.map fun _ => true)
    else pure expl
  let shown := (args.toList.zip (expl.toList ++ List.replicate args.size true)).filter (·.2) |>.map (·.1)
  let head ← match target with
    | some t => pure t
    | none => do
      modify fun s => { s with used := s.used.insert c }
      pure (mangle c)
  if shown.isEmpty then return head
  -- the function arguments of a binder constant are λs, eta-expanded if need be
  let isBinder := (← get).binders.contains c
  let as ← shown.mapM fun a => do
    if keep then
      -- the function arguments of the rules: of one argument, or of two for
      -- existsE (the witness and the proof that it is one)
      if let .lam n t b bi := a then
        return ← binder n t b bi true (if c == ``Exists.elim then 2 else 1)
    if isBinder then
      -- all its arguments, as the macro shows each bound variable: f to x y => f x y
      let ty ← whnf (← inferType a)
      if ty.isForall then
        return ← tr (← Core.betaReduce (← etaExpand a))
    -- a class as a type argument (⊥ of TopologicalSpace X): the set of its structures
    if (← isClass? a).isSome then
      if let some s ← structureSet a then return s
    tr a
  return " ".intercalate (head :: as.map paren)

end

/-- An instance hypothesis that a statement leaves out: decidability, which
is computational, and the technical classes that a textbook never states
(the coercion classes FunLike and SetLike, the compatibility of an order or
an action with the operations, the bare notation classes Zero, Add, ...).
Its λ in the definiens is left out too, so that the proof still fits. -/
def droppedInstance (ty : Expr) (bi : BinderInfo) : Bool :=
  bi == .instImplicit && technicalClass ty

/-- The statement of a declaration as a Dedukti type: its binders as
hypotheses, its conclusion as Proof P (a theorem) or as the type of the
object it defines. -/
partial def statementGo (explicitOnly : Bool) (t : Expr) : M String := do
    match t with
    | .forallE n ty b bi => do
      let prop ← isProp ty
      let nm ← freshName n prop (sortish ty)
      withLocalDecl (Name.mkSimple nm) bi ty fun y => do
        let rest ← statementGo explicitOnly (b.instantiate1 y)
        if explicitOnly && bi != .default && (bi == .instImplicit || !(← get).keepImplicit) then return rest
        -- decidability and technical instances are not hypotheses of the statement
        if droppedInstance ty bi then
          return rest
        -- a named structure (see givenInstance) is an element of the set of the
        -- structures, with its name also when it was an instance (𝓤[U])
        let h ← if (← get).namedLocals.contains y.fvarId! then do pure s!"({nm} : {← hypoType ty false})"
                 else if bi == .instImplicit then do pure s!"(_ : Proof {paren (← tr ty)})"
                 else do pure s!"({nm} : {← hypoType ty})"
        return s!"{h} -> {rest}"
    | _ => do
      if (← isProp t) then return s!"Proof {paren (← tr t)}"
      -- a definition of a structure (TopologicalSpace.induced): an element of the set of them
      hypoType t false

/-- A theorem is stated with all its hypotheses, implicit ones included, as
they are its statement; any other constant (a definition, a structure, a
primitive) with its explicit arguments only, the ones its applications show,
so that the #k of its symbol table entry count the same arguments. -/
def statement (type : Expr) : M String := do
  -- twice: the first pass notes the instance arguments to keep (see givenInstance)
  let s0 ← get
  set { s0 with collecting := true }
  discard <| statementGo (!(← isProp type)) type
  let keys := (← get).givenKeys
  set { s0 with givenKeys := keys }
  statementGo (!(← isProp type)) type

/-- The definiens of a declaration, its λs matching the binders of its type:
a definition loses those of its implicit arguments, as its type does. -/
partial def valueGo (explicitOnly : Bool) (t v : Expr) : M String := do
  match t, v with
  | .forallE n ty b bi, .lam _ _ vb _ =>
    let prop ← isProp ty
    let nm ← freshName n prop (sortish ty)
    withLocalDecl (Name.mkSimple nm) bi ty fun y => do
      let rest ← valueGo explicitOnly (b.instantiate1 y) (vb.instantiate1 y)
      if explicitOnly && bi != .default && (bi == .instImplicit || !(← get).keepImplicit) then return rest
      -- the hypotheses that the statement leaves out have no λ either
      if droppedInstance ty bi then return rest
      return s!"{nm} => {rest}"
  | _, _ => tr v

def value (type v : Expr) : M String := do
  -- twice, as statement, noting the instance arguments of the statement too
  let s0 ← get
  set { s0 with collecting := true }
  discard <| statementGo (!(← isProp type)) type
  discard <| valueGo (!(← isProp type)) type v
  let keys := (← get).givenKeys
  set { s0 with givenKeys := keys }
  valueGo (!(← isProp type)) type v

/-- The text after the top-level := of a declaration, from its name on (so
that neither its docstring nor its attributes count), or none for a
definition by equations. -/
partial def afterAssign : Nat → List Char → Option (List Char)
  | _, [] => none
  | d, ':' :: '=' :: rest => if d == 0 then some rest else afterAssign d rest
  | d, c :: rest =>
    afterAssign (if c == '(' || c == '[' || c == '{' then d + 1
                 else if c == ')' || c == ']' || c == '}' then d - 1 else d) rest

/-- Whether the definiens is a term, not a tactic proof (by ...) nor equations. -/
def termDefiniens (src : Array String) (r : DeclarationRanges) : Bool :=
  let lines := (src.extract (r.selectionRange.pos.line - 1) r.range.endPos.line).toList
  match afterAssign 0 ("\n".intercalate lines).toList with
  | none => false
  | some rest =>
    let rest := rest.dropWhile Char.isWhitespace
    match rest with
    | 'b' :: 'y' :: c :: _ => !c.isWhitespace
    | ['b', 'y'] => false
    | [] => false
    | _ => true

/-- A class is declared as a predicate: its instance arguments are exported
as hypotheses Proof (C α), "Let α be a commutative monoid". -/
def asPredicate (env : Environment) (n : Name) (s : String) : String :=
  if isClass env n && s.endsWith "Set" then String.ofList (s.toList.take (s.length - 3)) ++ "Prop" else s

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .opaqueInfo _ => "opaque"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- Declarations worth a reading: not internal, not auxiliary, not instances. -/
def wanted (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  !n.isInternal && !n.isInternalDetail && !isAuxRecursor env n && !isNoConfusion env n &&
  !(ci matches .recInfo _) && !(ci matches .quotInfo _) &&
  !(Lean.Meta.isInstanceCore env n) && !(`match_).isPrefixOf n && !n.isImplementationDetail &&
  !(Lean.Linter.isDeprecated env n)  -- old names of other declarations

def jsonStr (s : String) : String := (Json.str s).compress

def strip (s : String) : String :=
  String.ofList (s.toList.dropWhile Char.isWhitespace |>.reverse.dropWhile Char.isWhitespace |>.reverse)

def readBinders : IO (Std.HashSet Name) := do
  let path : System.FilePath := "binders.txt"
  if !(← path.pathExists) then return {}
  let mut b := {}
  for line in (← IO.FS.lines path) do
    if line.startsWith "#" || strip line == "" then continue
    b := b.insert (strip line).toName
  return b

def readMapping : IO (Std.HashMap Name String × Std.HashSet Name) := do
  let path : System.FilePath := "mapping.tsv"
  if !(← path.pathExists) then return ({}, {})
  let mut m := {}
  let mut all := {}
  for line in (← IO.FS.lines path) do
    if line.startsWith "#" || strip line == "" then continue
    match line.splitOn "\t" with
    | [l, d] => m := m.insert (strip l).toName (strip d)
    | [l, d, a] =>
      m := m.insert (strip l).toName (strip d)
      if strip a == "all" then all := all.insert (strip l).toName
    | _ => pure ()
  return (m, all)

/-- Export the declarations `names` of a module `mod`, whose source is `src`,
to `outDir`/<mod>.dk, .json and -deps.dk. -/
def exportDecls (env : Environment) (mapping : Std.HashMap Name String)
    (keepAll binders : Std.HashSet Name) (mod : Name) (names : Array Name) (src : Array String)
    (outDir : String := "out") : IO Unit := do
  let decls := names.toList.filterMap fun n =>
    match env.find? n with
    | some ci => if wanted env n ci then some (n, ci) else none
    | none => none
  let ctx : Core.Context := { fileName := "<export>", fileMap := default, maxHeartbeats := 0,
                              options := {} }
  let st : Core.State := { env }
  -- the source position of each: declarations without one (generated by
  -- Lean, as equation lemmas are) are left out, the others sorted by it
  let mut found := #[]
  for (n, ci) in decls do
    match ← ((Lean.findDeclarationRanges? n : CoreM _).toIO ctx st |>.toBaseIO) with
    | .ok (some r, _) => found := found.push (n, ci, r)
    | _ => pure ()
  let ranged := found.qsort fun (_, _, a) (_, _, b) => a.range.pos.line < b.range.pos.line
  let decls := ranged.toList.map fun (n, ci, _) => (n, ci)
  let lineOf : Std.HashMap Name DeclarationRanges :=
    ranged.foldl (fun m (n, _, r) => m.insert n r) {}
  -- the additive twins that `to_additive` makes of the module's theorems:
  -- a twin's source is its original's, whose position the twin's range does
  -- not have (it is the attribute's)
  let twinOf : Std.HashMap Name Name := decls.foldl (init := {}) fun m (n, _) =>
    match Mathlib.Tactic.Translate.findTranslationName? env Mathlib.Tactic.ToAdditive.data n with
    | some t => if t != n then m.insert t n else m
    | none => m
  let rec original (fuel : Nat) (n : Name) : Name := match fuel, twinOf.get? n with
    | fuel + 1, some m => original fuel m
    | _, _ => n
  let mut dk := s!"(; {mod}: statements exported from Mathlib by MathlibInformath/Export.lean ;)\n\n"
  let mut json := #[]
  let mut used : Std.HashSet Name := {}
  let mut derived : Std.HashMap String String := {}
  let mut derivedHide : Std.HashMap String (Array Nat) := {}
  for (n, ci) in decls do
    let act : M String := statement ci.type
    let res ← ((act.run {mapping, binders, keepAll, keepImplicit := true}).run' {} {}).toIO ctx st |>.toBaseIO
    let doc ← (Lean.findDocString? env n)
    let pp ← ((Meta.ppExpr ci.type).run' {} {}).toIO ctx st |>.toBaseIO
    let ppStr := match pp with | .ok (f, _) => toString f | .error _ => ""
    match res with
    | .ok ((s, stt), _) =>
      used := stt.used.fold (fun acc c => acc.insert c) used
      derived := stt.derived.fold (fun acc k v => acc.insert k v) derived
      derivedHide := stt.derivedHide.fold (fun acc k v => acc.insert k v) derivedHide
      let r := lineOf.get! n
      let orig := original 3 n
      -- the definiens too, where the source has a term and it translates
      let isThm := ci matches .thmInfo _
      let mut defn := ""
      if let some v := ci.value? (allowOpaque := true) then
        if termDefiniens src (lineOf.getD orig r) && !isClass env n then
          let vres ← (((value ci.type v).run {mapping, binders, keepAll, proofMode := isThm, keepImplicit := true}).run' {} {}).toIO ctx st
                     |>.toBaseIO
          if (← IO.getEnv "EXPORT_DEBUG").isSome then
            match vres with
            | .ok ((vs, _), _) => IO.eprintln s!"DEFN {n}: {vs.length} {vs}"
            | .error e => IO.eprintln s!"DEFN {n}: ERROR {e}"
          if let .ok ((vs, vst), _) := vres then
            -- compiled pattern matching (match_ functions, recursors) is not an
            -- expression of the source: such a definiens is not kept
            let compiled := ["UNSUPPORTED", "match_", "casesOn", "__rec ", "_private"].any
                              fun w => (vs.splitOn w).length > 1
            if compiled then pure () else
            -- (6000: the implicit arguments, which the readings hide, are counted too)
            if vs.length ≤ 6000 then
              defn := vs
              used := vst.used.fold (fun acc c => acc.insert c) used
              derived := vst.derived.fold (fun acc k v => acc.insert k v) derived
              derivedHide := vst.derivedHide.fold (fun acc k v => acc.insert k v) derivedHide
      dk := dk ++ (if defn.isEmpty then s!"(; //LEAN:{n} ;)\n{mangle n} : {asPredicate env n s}.\n\n"
                   else s!"(; //LEAN:{n} ;)\ndef {mangle n} : {asPredicate env n s} :=\n  {defn}.\n\n")
      json := json.push s!"\{\"lean\": {jsonStr n.toString}, \"dk\": {jsonStr (mangle n)}, \"kind\": {jsonStr (kindOf ci)}, \"doc\": {jsonStr (doc.getD "")}, \"statement\": {jsonStr ppStr}, \"line\": {r.range.pos.line}, \"nameLine\": {r.selectionRange.pos.line}, \"endLine\": {r.range.endPos.line}, \"definiens\": {if defn.isEmpty then "false" else "true"}{if orig != n then s!", \"additiveOf\": {jsonStr orig.toString}" else ""}}"
    | .error e =>
      dk := dk ++ s!"(; //LEAN:{n} ;)\n(; NOT EXPORTED: {toString e} ;)\n\n"
  -- the constants used but neither exported nor mapped
  let exported : Std.HashSet Name := decls.foldl (fun acc (n, _) => acc.insert n) {}
  let mut deps := s!"(; constants used by {mod}, declared with their translated types ;)\n\n"
  for (nm, ty) in derived.toList.toArray.qsort (·.1 < ·.1) do
    let why := if nm.endsWith "__on" then "the structures of a class on its parameters"
      else if nm.endsWith "__app" then "a constant applied as a function: DFunLike.coe"
      else "a constant with an instance argument that the statement gives"
    deps := deps ++ s!"(; {why} ;)\n{nm} : {ty}.\n\n"
  for c in used.toList.toArray.qsort (·.toString < ·.toString) do
    if exported.contains c then continue
    let some ci := env.find? c | continue
    let res ← (((statement ci.type).run {mapping, binders, keepAll, keepImplicit := true}).run' {} {}).toIO ctx st |>.toBaseIO
    match res with
    | .ok ((s, _), _) =>
      let doc := ((← Lean.findDocString? env c).getD "").replace "\n" " " |>.replace ";)" "; )"
      let docLine := if doc.isEmpty then "" else s!"(; doc: {doc} ;)\n"
      deps := deps ++ s!"{docLine}(; //LEAN:{c} ;)\n{mangle c} : {asPredicate env c s}.\n\n"
    | .error _ => deps := deps ++ s!"(; NOT EXPORTED: {c} ;)\n\n"
  -- the arguments that the readings hide, as Lean's elaborator fills them in
  -- (#HIDE c i j: the i'th and j'th arguments, counting those Dedukti has, which
  -- are all but the instances), and the coercions (#COERCION c k: c is read as
  -- its k'th argument)
  let mut hide := s!"# {mod}: the implicit arguments of its constants and the coercions (Export.lean)\n"
  let consts := (exported.toList ++ used.toList).toArray.qsort (·.toString < ·.toString)
  let mut seen : Std.HashSet Name := {}
  for c in consts do
    -- not the constants that tr writes otherwise (Eq as Eq or Eqt, Exists as exists);
    -- OfNat.ofNat is a numeral when applied to a literal, else a constant
    if seen.contains c || mapping.contains c || [``Eq, ``Exists, `DFunLike.coe, ``outParam,
        ``semiOutParam].contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let r ← (((do
        forallTelescope ci.type fun xs _ => do
          let mut hidden := #[]
          let mut firstExpl : Option Nat := none
          let mut i := 0
          for x in xs do
            let bi ← x.fvarId!.getBinderInfo
            if bi == .instImplicit then continue
            i := i + 1
            if bi == .default then
              if firstExpl.isNone then firstExpl := some i
            else hidden := hidden.push i
          return (hidden, firstExpl) : MetaM (Array Nat × Option Nat))).run' {} {}).toIO ctx st |>.toBaseIO
    match r with
    | .ok ((hidden, firstExpl), _) =>
      if !hidden.isEmpty then
        hide := hide ++ s!"#HIDE {mangle c} {" ".intercalate (hidden.toList.map toString)}\n"
      if coercions.contains c then
        if let some k := firstExpl then hide := hide ++ s!"#COERCION {mangle c} {k}\n"
    | .error _ => pure ()
  IO.FS.createDirAll outDir
  IO.FS.writeFile s!"{outDir}/{mod}.dk" dk
  for (nm, hidden) in derivedHide.toList.toArray.qsort (·.1 < ·.1) do
    if !hidden.isEmpty then
      hide := hide ++ s!"#HIDE {nm} {" ".intercalate (hidden.toList.map toString)}\n"
  IO.FS.writeFile s!"{outDir}/{mod}-hide.dkgf" hide
  IO.FS.writeFile s!"{outDir}/{mod}-deps.dk" deps
  IO.FS.writeFile s!"{outDir}/{mod}.json" ("[\n" ++ ",\n".intercalate json.toList ++ "\n]\n")
  IO.println s!"{mod}: {decls.length} declarations -> {outDir}/{mod}.dk, {outDir}/{mod}.json; {used.size} constants used"

def exportModule (env : Environment) (mapping : Std.HashMap Name String)
    (keepAll binders : Std.HashSet Name) (mod : Name) : IO Unit := do
  let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"module {mod} not loaded"
  -- in the order of the source, as the module records them
  let names := env.header.moduleData[idx.toNat]!.constNames
  let mathlib := (← IO.getEnv "MATHLIB").getD "../mathlib4"
  let srcPath : System.FilePath := mathlib ++ "/" ++ (mod.toString.replace "." "/") ++ ".lean"
  let src ← if ← srcPath.pathExists then IO.FS.lines srcPath else pure #[]
  exportDecls env mapping keepAll binders mod names src


/-! ## Algebraic structures

`lake exe export --structures` reads `structures.txt`, whose lines are
`<Name> <Module> <Class> ...`, imports each Module and writes
out/<Name>.dk, .json and -deps.dk: for each class, a structure declaration
whose clauses are its carrier, its parent's predicate and its own fields,

    Monoid__structure : (M : Set) -> (h : Proof (Semigroup M)) -> ({|1|} : Elem M) ->
      (one_mul : Proof (forall M (a => Eqt M (times {|1|} a) a))) -> ... -> Structure.

which Informath reads as a definition by extension ("A monoid is a semigroup
M with an element 1 of M such that ..."), and the class as a predicate of its
carrier, defined by its parent and its new fields (`def Monoid : (M : Set) ->
Prop := M => and (Semigroup M) (exists M (e => ...))`), as the statements
use it ("Assume that G is a group"); doc/structures has the options.

The parent is the one the docstring names ("A `Monoid` is a `Semigroup` with
..."), if it is one of the classes exported, else the exported ancestor with
the most fields; a class without one (`Mul`) states all its fields, flattened
through `extends`. Left out are the fields with a default value (`npow`, `div`,
`zpow` and their laws), which Mathlib adds for definitional convenience. In the
types of the fields, the operations of the instance (`a * b`, `1`, `a⁻¹`, found
by instance resolution in Lean) become the variables of the fields before, or,
for the parent's, are written as the statements write them (`times a b`). An
operation is named by its notation: a binary one is an `Oper G`, applied with
`appOper`, a unary one a `UOper G`, applied with `appUOper` (a⁻¹) or
`appPrefixUOper` (-a). An additive class whose multiplicative version is
exported before it is derived from it by `to_additive`'s translations. -/

/-- The notation that names a binary operation field. -/
def operName (f : Name) : String :=
  match f.toString with
  | "mul" => "{|*|}" | "add" => "{|+|}" | "div" => "{|/|}" | "sub" => "{|-|}"
  | "one" => "{|1|}" | "zero" => "{|0|}" | "inv" => "{|⁻¹|}" | "neg" => "{|-|}"
  | "le" => "{|≤|}" | "lt" => "{|<|}" | "sup" => "{|⊔|}" | "inf" => "{|⊓|}"
  | "max" => "{|⊔|}" | "min" => "{|⊓|}" | "top" => "{|⊤|}" | "bot" => "{|⊥|}"
  | "smul" => "{|•|}" | "vadd" => "{|+ᵥ|}"
  | s => s

/-- The function that applies a unary operation named by its notation:
a⁻¹ (appUOper), -a (appPrefixUOper). -/
def uoperApp (nm : String) : String :=
  if nm == "{|-|}" then "appPrefixUOper" else "appUOper"

/-- The fields a structure definition states: all fields, flattened through
`extends`, except those with a default value. -/
def statedFields (env : Environment) (c : Name) : Array Name × Array Name :=
  (getStructureFieldsFlattened env c (includeSubobjectFields := false)).partition fun f =>
    (getEffectiveDefaultFnForField? env c f).isNone

/-- `e` with the operations of the instance replaced by the field variables:
an application of a projection (Mul.mul, HMul.hMul, OfNat.ofNat, Inv.inv ...)
whose part up to its instance argument is a field's value. -/
def replaceFields (fields : Array (Expr × Expr)) (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    let f := e.getAppFn
    let some c := f.constName? | return .continue
    let some info := (← getEnv).getProjectionFnInfo? c | return .continue
    let args := e.getAppArgs
    let k := info.numParams + 1
    if args.size < k then return .continue
    let pre := mkAppN f (args.extract 0 k)
    let ty ← inferType pre
    for (v, x) in fields do
      if (← isDefEq (← inferType v) ty) && (← isDefEq v pre) then
        return .visit (mkAppN x (args.extract k args.size))
    return .continue)

/-- The type of a data field: Elem G, or a function type of such. -/
partial def fieldType (t : Expr) : M String := do
  match t with
  | .forallE _ a b _ =>
    if b.hasLooseBVars then hypoType t
    else return s!"{← hypoType a} -> {← fieldType b}"
  | _ => hypoType t

/-- A type argument, also as an out-parameter (α of `FunLike F α β`). -/
def sortLike (t : Expr) : Bool :=
  t.isSort || (t.isAppOfArity ``outParam 1 && t.appArg!.isSort)

/-- The type with its k-th binder renamed. -/
def renameBinder (t : Expr) (k : Nat) (n : Name) : MetaM Expr :=
  match t, k with
  | .forallE _ a b bi, 0 => pure (.forallE n a b bi)
  | .forallE m a b bi, k + 1 => do pure (.forallE m a (← renameBinder b k n) bi)
  | t, _ => pure t

/-- A type made of the carrier only: G, G → G, G → G → G. -/
partial def carrierOnly (g t : Expr) : MetaM Bool := do
  match t with
  | .forallE _ a b _ =>
    if b.hasLooseBVars then return false
    return (← isDefEq a g) && (← carrierOnly g b)
  | _ => isDefEq t g

/-- The structure declaration of a class, the names of the fields left
out, and the definition of the class as a predicate of its carrier. With
a parent `P`, the structure takes `P`'s predicate as a clause and only the
fields that `P` does not have (option B of doc/structures), and the
predicate is `P` and the new fields: their data exist and their laws hold
(option D). Left out are the fields with a default value, and the laws
that mention them or (without a parent) any other operation of the
instance that the stated fields do not give. -/
def structureDecl (c : Name) (parent : Option Name := none) (instParent : Bool := false) :
    M (String × Array Name × Option String) := do
  let env ← getEnv
  let ci ← getConstInfo c
  let (stated0, defaulted) := statedFields env c
  -- the fields that the parent has are its own, not this structure's (a parent
  -- that is an instance argument of the carrier, as AddCommMonoid M of Module R M,
  -- has none of them)
  let inherited := match parent with
    | some p => if instParent then #[] else getStructureFieldsFlattened env p (includeSubobjectFields := false)
    | none => #[]
  let stated := stated0.filter (!inherited.contains ·)
  -- the carrier is the last type argument (M in Module R M), but not an
  -- out-parameter (F of a hom class, not β); the others are parameters
  let carrierIdx ← forallTelescope ci.type fun xs _ => do
    let mut k := none
    let mut kIn := none
    for i in [0:xs.size] do
      let t ← inferType xs[i]!
      if t.isSort then kIn := some i
      if sortLike t then k := some i
    pure (kIn.orElse fun _ => k)
  let some k := carrierIdx | throwError "{c} has no carrier"
  -- the carrier as Mathlib names it, but for a Greek letter (Mul α) the textbook's
  -- letter: R for a ring, K for a field, M for a monoid or a module, G otherwise
  let cs := c.toString
  let letter : Name := if (cs.splitOn "Field").length > 1 then `K
    else if (cs.splitOn "Module").length > 1 then `M
    else if (cs.splitOn "ing").length > 1 then `R
    else if (cs.splitOn "Monoid").length > 1 then `M else `G
  -- Mathlib's name kept, if it is not Greek
  let orig ← forallTelescope ci.type fun xs _ => do
    pure (← xs[k]!.fvarId!.getUserName).eraseMacroScopes.toString
  let ascii (s : String) := s.all (fun (ch : Char) => ch.isAlphanum && ch.toNat < 128)
  let ty ← if ascii orig then pure ci.type else renameBinder ci.type k letter
  -- the other Greek arguments too (α of MulAction α β): R, S, T, A, B
  let names ← forallTelescope ty fun xs _ => xs.mapM fun x => do
    pure ((← x.fvarId!.getUserName).eraseMacroScopes.toString, sortLike (← inferType x))
  let mut used := names.toList.map (·.1) ++ [letter.toString]
  let mut ty := ty
  for i in [0:names.size] do
    let (nm, isSort) := names[i]!
    if i == k || ascii nm then continue
    -- a Greek argument of another kind (φ, κ): r, s, f, ...
    let letters := if isSort then ["R", "S", "T", "A", "B", "C"] else ["r", "s", "f", "g", "p", "q", "u", "v"]
    if let some l := letters.find? (!used.contains ·) then
      used := l :: used
      ty ← renameBinder ty i l.toName
  forallTelescope ty fun xs _ => do
    let carrierE := xs[k]!
    let n0 := (← carrierE.fvarId!.getUserName).eraseMacroScopes.toString
    let carrier ← freshName (if n0.all (fun (ch : Char) => ch.isAlphanum && ch.toNat < 128) then n0.toName else letter) false
    -- the parameters (R : Set) and their instances (hR : Proof (Semiring R))
    let mut paramClauses : Array String := #[]
    let mut params : Array (Expr × String) := #[]
    let mut argFields : Array Expr := #[]
    for i in [0:xs.size] do
      let x := xs[i]!
      let xt ← inferType x
      if i == k then continue
      if sortLike xt then
        let pn ← freshName (← x.fvarId!.getUserName).eraseMacroScopes false
        params := params.push (x, pn)
        paramClauses := paramClauses.push s!"({pn} : Set)"
      else if (← x.fvarId!.getBinderInfo).isInstImplicit && !xt.containsFVar carrierE.fvarId! then
        let pn := match params.back? with | some (_, n) => n | none => "x"
        paramClauses := paramClauses.push s!"(h{pn} : Proof {paren (← tr xt)})"
      -- an argument of the carrier, as the relation r of IsPreorder α r: a field
      else if i > k && (← x.fvarId!.getBinderInfo).isExplicit then
        argFields := argFields.push x
    let g := carrierE
    do
      let cls := mkAppN (mkConst c (ci.levelParams.map Level.param)) xs
      withLocalDecl `inst .instImplicit cls fun inst => do
        -- the defaulted fields as variables too, to see which laws mention them
        let dvs ← defaulted.mapM fun f => (mkProjection inst f : MetaM Expr)
        let dtys ← dvs.mapM fun v => (inferType v : MetaM Expr)
        withLocalDeclsDND (defaulted.zip dtys) fun dxs => do
        let marks := dxs.map (·.fvarId!)
        -- and the parent's fields, which the laws may use but the structure does not state
        let inh := inherited.filter (!defaulted.contains ·)
        let ivs ← inh.mapM fun f => (mkProjection inst f : MetaM Expr)
        let itys ← ivs.mapM fun v => (inferType v : MetaM Expr)
        withLocalDeclsDND ((inh.map (·.appendBefore "parent_")).zip itys) fun ixs => do
        -- the fields stated: (name, type) as declared, and whether data
        let rec go (i : Nat) (done : Array (Expr × Expr)) (acc : Array (String × String × Bool))
            (left : Array Name) (extra : Array FVarId := #[]) : M (Array (String × String × Bool) × Array Name) := do
          if h : i < stated.size then
            let f := stated[i]
            let v ← mkProjection inst f
            let ty0 ← instantiateMVars (← inferType v)
            let ty ← replaceFields (done ++ dvs.zip dxs) ty0
            -- a law about a defaulted field, or about any other operation of the
            -- instance than the stated ones and the parent's (x ^ n is npow, its
            -- arguments swapped); the parent's operations are written as the
            -- statements write them (a * b as times a b)
            let tyAll ← replaceFields (done ++ dvs.zip dxs ++ ivs.zip ixs) ty0
            if tyAll.containsFVar inst.fvarId! || (marks ++ extra).any (fun (m : FVarId) => tyAll.containsFVar m) then
              return ← go (i + 1) done acc (left.push f) extra
            -- data of other types than the carrier (natCast : ℕ → R, qsmul : ℚ → K → K)
            -- serve the implementation: left out, with the laws that mention them
            let rel ← isDefEq ty (← mkArrow g (← mkArrow g (mkSort .zero)))
            -- an action of a parameter on the carrier: r • x
            let mut actor : Option String := none
            for (p, pn) in params do
              if ← isDefEq ty (← mkArrow p (← mkArrow g g)) then actor := some pn
            let act := actor.isSome
            if !rel && !act && !(← isProp ty) && !(← carrierOnly g ty) then
              return ← withLocalDecl f.eraseMacroScopes .default ty fun x =>
                go (i + 1) (done.push (v, x)) acc (left.push f) (extra.push x.fvarId!)
            let binop ← isDefEq ty (← mkArrow g (← mkArrow g g))
            let unop ← isDefEq ty (← mkArrow g g)
            let prop ← isProp ty
            -- the bound variables of each field are named afresh
            let names := (← get).names
            let symbolic := operName f != f.toString
            let oper := binop || rel || act || (unop && symbolic)
            let nm ← if binop || rel || act || symbolic then pure (operName f) else freshName f prop
            withLocalDecl (Name.mkSimple nm) .default ty fun x => do
              if oper then
                let on := match actor with | some pn => s!"{pn} {carrier}" | none => carrier
                modify fun s => { s with opers := s.opers.insert x.fvarId! (nm, on) }
              let t ← if act then pure s!"Action {actor.getD ""} {carrier}"
                      else if rel then pure s!"Rel {carrier}"
                      else if binop then pure s!"Oper {carrier}"
                      else if unop && symbolic then pure s!"UOper {carrier}"
                      else if prop then pure s!"Proof {paren (← tr ty)}"
                      -- in parentheses: in Dedukti, (f : A -> B) is the type (f : A) -> B
                      else do let t ← fieldType ty; pure (if (t.splitOn " -> ").length > 1 then s!"({t})" else t)
              modify fun s => { s with names := names.insert nm }
              go (i + 1) (done.push (v, x)) (acc.push (nm, t, !prop)) left extra
          else return (acc, left)
        let (fs, left) ← go 0 #[] #[] defaulted
        -- the parent applied to as many of the parameters and the carrier as it
        -- has type arguments, the last ones: DistribMulAction R M of Module R M
        let parentArgs ← match parent with
          | some p => do
            let pci ← getConstInfo p
            let n ← forallTelescope pci.type fun ys _ => do
              let mut n := 0
              for y in ys do
                if sortLike (← inferType y) && (← y.fvarId!.getBinderInfo).isExplicit then n := n + 1
              pure n
            let names := params.toList.map (·.2) ++ [carrier]
            pure (names.drop (names.length - max n 1))
          | none => pure []
        let parentClause := match parent with
          | some p => [s!"(h : Proof ({mangle p} {" ".intercalate parentArgs}))"]
          | none => []
        let args ← argFields.toList.mapM fun x => do
          let t ← fieldType (← inferType x)
          pure s!"({← tr x} : {if (t.splitOn " -> ").length > 1 then s!"({t})" else t})"
        let decl := " -> ".intercalate (paramClauses.toList ++ [s!"({carrier} : Set)"] ++ parentClause ++
          args ++ (fs.toList.map fun (nm, t, _) => s!"({nm} : {t})") ++ ["Structure"])
        -- not with arguments of the carrier, which the predicate's binders do not have
        let pdef := if argFields.isEmpty then
          predicateDef c parent carrier fs (params.map (·.2)) (paramClauses.filter (·.startsWith "(h")) parentArgs else none
        return (s!"{mangle c}__structure : {decl}.", left, pdef)

where
  /-- The class as a predicate (option D): `def C : (G : Set) -> Prop := G =>
  and (P G) (exists ... (and ...))`, its new data quantified, named as a
  textbook names them (e for the identity element, i for the inverse);
  none without a parent or without laws of its own. -/
  predicateDef (c : Name) (parent : Option Name) (carrier : String)
      (fs : Array (String × String × Bool)) (params : Array String := #[])
      (paramHyps : Array String := #[]) (parentArgs : List String := []) : Option String := do
    let p ← parent
    let laws := fs.filter (!·.2.2) |>.map (·.2.1)
    guard (!laws.isEmpty)
    let data := fs.filter (·.2.2)
    -- the data as variables of a function type: a⁻¹ as i(a)
    let rename (nm : String) : String × String := match nm with
      | "{|1|}" | "{|0|}" => ("e", "e")
      | "{|⁻¹|}" | "{|-|}" => ("i", s!"{uoperApp nm} {carrier} {nm}")
      | _ => (nm, nm)
    let setOf (t : String) : Option String :=
      if t.startsWith "Action " then some s!"({(t.drop 7).toString.takeWhile (· != ' ')} -> {carrier} -> {carrier})"
      else if t.startsWith "Rel " then some s!"({carrier} -> {carrier} -> Prop)"
      else if t.startsWith "UOper " then some s!"({carrier} -> {carrier})"
      else if t.startsWith "Oper " then some s!"({carrier} -> {carrier} -> {carrier})"
      else if t == s!"Elem {carrier}" then some carrier else none
    -- the names of the data are distinctive ({|1|}, {|⁻¹|}): plain replacement
    let subst (law : String) : String := data.foldl (fun l (nm, _, _) =>
      let (v, pat) := rename nm
      (l.replace pat v).replace nm v) law
    -- a law is Proof (P): its proposition P
    let unparen (l : String) : String :=
      if l.startsWith "(" && l.endsWith ")" then ((l.drop 1).dropRight 1).toString else l
    let conj := (laws.map fun t => subst (unparen (t.drop 6).toString)).toList
    let body := match conj.reverse with
      | [] => "true"
      | last :: rest => rest.foldl (fun acc l => s!"and {paren l} {paren acc}") last
    let mut body := body
    for (nm, t, _) in data.reverse do
      let some set := setOf t | none
      body := s!"exists {set} ({(rename nm).1} => {body})"
    -- the parameters' instances first: R is a semiring
    let hyps := paramHyps.toList.map fun h => (((h.splitOn "Proof ").getD 1 "").toList.dropLast |> String.ofList)
    let whole := hyps.foldr (fun h acc => s!"and {paren h} {paren acc}") s!"and ({mangle p} {" ".intercalate (if parentArgs.isEmpty then [carrier] else parentArgs)}) {paren body}"
    let binders := (params.toList ++ [carrier]).map (s!"({·} : Set) -> ")
    return s!"def {mangle c} : {String.join binders}Prop :=\n  {String.join ((params.toList ++ [carrier]).map (s!"{·} => "))}{whole}."

/-- The base of the structure declarations, for out/<Name>-deps.dk. -/
def structureBase : String :=
  "Structure : Type.\n\nOper : (A : Set) -> Type.\n\n" ++
  "appOper : (A : Set) -> (op : Oper A) -> (x : Elem A) -> (y : Elem A) -> Elem A.\n\n" ++
  "UOper : (A : Set) -> Type.\n\n" ++
  "appUOper : (A : Set) -> (op : UOper A) -> (x : Elem A) -> Elem A.\n\n" ++
  "appPrefixUOper : (A : Set) -> (op : UOper A) -> (x : Elem A) -> Elem A.\n\n" ++
  "Rel : (A : Set) -> Type.\n\n" ++
  "appRel : (A : Set) -> (r : Rel A) -> (x : Elem A) -> (y : Elem A) -> Prop.\n\n" ++
  "latticeSup : (A : Set) -> Elem A -> Elem A -> Elem A.\n\n" ++
  "latticeInf : (A : Set) -> Elem A -> Elem A -> Elem A.\n\n" ++
  "Action : (A : Set) -> (B : Set) -> Type.\n\n" ++
  "appAction : (A : Set) -> (B : Set) -> (op : Action A B) -> (r : Elem A) -> (x : Elem B) -> Elem B.\n"

/-- The nouns that name the structures, from structures.dkgf: noun -> class. -/
def readNouns : IO (List (String × Name)) := do
  let path : System.FilePath := "structures.dkgf"
  if !(← path.pathExists) then return []
  let mut out := []
  for l in ← IO.FS.lines path do
    match l.splitOn "__structure : \"" with
    | [c, rest] => out := out ++ [((rest.splitOn "\"").head!, c.toName)]
    | _ => pure ()
  return out

/-- The classes that `c` extends, directly or not, nearest first. -/
partial def ancestors (env : Environment) (c : Name) : Array Name :=
  let ps := (getStructureParentInfo env c).map (·.structName)
  ps ++ ps.foldl (fun acc p => acc ++ ancestors env p) #[]

/-- The parent that the docstring names, as a textbook would: "A `Monoid` is
a `Semigroup` with ...", "A commutative group is a group with ...". -/
def docParent (doc : String) (nouns : List (String × Name)) : Option Name := Id.run do
  let first := (doc.splitOn "\n\n").head!.replace "\n" " "
  for sep in [" is an ", " is a "] do
    match first.splitOn sep with
    | _ :: r :: rs =>
      let rest := sep.intercalate (r :: rs)
      if rest.startsWith "`" then
        return some ((rest.drop 1).takeWhile (· != '`')).toString.toName
      -- the longest phrase that is a noun: "monoid", "commutative monoid"
      let words := rest.splitOn " "
      for k in (List.range (min 4 words.length)).reverse do
        if let some (_, cl) := nouns.find? (·.1 == " ".intercalate (words.take (k + 1))) then
          return some cl
      return none
    | _ => pure ()
  return none

/-- The primary parent of a class (doc/structures, "Choosing the parent"):
the one its docstring names, if it is one of the structures exported; else
the exported ancestor with the most fields, the nearest first. -/
def primaryParent (env : Environment) (c : Name) (classes : List Name)
    (nouns : List (String × Name)) (doc : String) : Option Name :=
  let anc := ancestors env c
  let ok (p : Name) := p != c && anc.contains p && classes.contains p
  match docParent doc nouns with
  | some p => if ok p then some p else fallback anc ok
  | none => fallback anc ok
where
  fallback (anc : Array Name) (ok : Name → Bool) : Option Name :=
    let size (p : Name) := (statedFields env p).1.size
    anc.foldl (fun best p => if !ok p then best else match best with
      | some b => if size p > size b then some p else best
      | none => some p) none

/-- A class among the instance arguments of the carrier that names a
structure (`AddCommMonoid M` in `Module R M`): the parent of a class that
extends no exported structure. -/
def instanceParent (env : Environment) (c : Name) (known : List Name) : Option Name := Id.run do
  let some ci := env.find? c | return none
  -- the binders: their types and whether instances; the carrier is the last sort
  let rec binders (t : Expr) (acc : Array (Expr × Bool)) : Array (Expr × Bool) :=
    match t with
    | .forallE _ a b bi => binders b (acc.push (a, bi.isInstImplicit))
    | _ => acc
  let bs := binders ci.type #[]
  let mut last := none
  for i in [0:bs.size] do
    if bs[i]!.1.isSort then last := some i
  let some k := last | return none
  for i in [k+1:bs.size] do
    let (t, inst) := bs[i]!
    if !inst then continue
    -- the carrier is the variable bound i - 1 - k binders up
    if t.getAppArgs.back? == some (.bvar (i - 1 - k)) then
      if let some cl := t.getAppFn.constName? then
        if known.contains cl then return some cl
  return none

/-- The tokens of a Dedukti text mapped, its spaces and parentheses kept. -/
def mapTokens (f : String → String) (s : String) : String := Id.run do
  let mut out := ""
  let mut tok := ""
  for ch in s.toList do
    if ch == ' ' || ch == '(' || ch == ')' || ch == '\n' then
      out := out ++ f tok |>.push ch
      tok := ""
    else tok := tok.push ch
  return out ++ f tok

/-- The additive version of a multiplicative class's declarations, by
to_additive's translations of its names (the class, its parent, its fields)
and its notation: + for *, 0 for 1, -a for a⁻¹. -/
def additiveText (env : Environment) (m c : Name) (fields : Array Name) (s : String) : String :=
  let tr (n : Name) : Option Name :=
    Mathlib.Tactic.Translate.findTranslationName? env Mathlib.Tactic.ToAdditive.data n
  let names : List (String × String) :=
    [(mangle m ++ "__structure", mangle c ++ "__structure"), (mangle m, mangle c)] ++
    (ancestors env m).toList.filterMap (fun p => (tr p).map fun q => (mangle p, mangle q)) ++
    fields.toList.filterMap (fun f => (tr (m ++ f)).map fun g => (f.toString, g.getString!))
  let notationMap : List (String × String) :=
    [("{|*|}", "{|+|}"), ("{|1|}", "{|0|}"), ("{|⁻¹|}", "{|-|}"), ("appUOper", "appPrefixUOper"),
     ("times", "plus"), ("1", "0")]
  mapTokens (fun t => match (names ++ notationMap).lookup t with | some u => u | none => t) s

def exportStructures (env : Environment) (outName : Name) (classes : List Name)
    (mapping : Std.HashMap Name String) (keepAll binders : Std.HashSet Name)
    (outDir : String := "out") : IO Unit := do
  let ctx : Core.Context := { fileName := "<export>", fileMap := default, maxHeartbeats := 0,
                              options := {} }
  let st : Core.State := { env }
  let mathlib := (← IO.getEnv "MATHLIB").getD "../mathlib4"
  let sysroot ← findSysroot
  let nouns ← readNouns
  let mut dk := s!"(; {outName}: Mathlib's classes as Informath's structures, by MathlibInformath/Export.lean ;)\n\n"
  let mut json := #[]
  -- the declarations made: class -> structure, left out, predicate, parent
  let mut made : Std.HashMap Name (String × Array Name × Option String × Option Name) := {}
  for c in classes do
    let some _ := env.find? c | IO.eprintln s!"{c}: not found"; continue
    let doc := (← Lean.findDocString? env c).getD ""
    -- an additive class is the to_additive translation of a multiplicative one exported before
    let mult := classes.find? fun m => m != c && made.contains m &&
      Mathlib.Tactic.Translate.findTranslationName? env Mathlib.Tactic.ToAdditive.data m == some c
    let res ← match mult with
      | some m => do
        let (decl, left, pdef, parent) := made[m]!
        let fields := getStructureFieldsFlattened env m (includeSubobjectFields := false)
        let add := additiveText env m c fields
        let tr (n : Name) := Mathlib.Tactic.Translate.findTranslationName? env Mathlib.Tactic.ToAdditive.data n
        pure (Except.ok (add decl, left.map fun f => ((tr (m ++ f)).map (·.getString!.toName)).getD f,
                         pdef.map add, parent.bind tr))
      | none => do
        let fromInstance := (primaryParent env c classes nouns doc).isNone
        let parent := match primaryParent env c classes nouns doc with
          | some p => some p
          | none => instanceParent env c (classes ++ nouns.map (·.2))
        let r ← (((structureDecl c parent (fromInstance && parent.isSome)).run {mapping, binders, keepAll, keepImplicit := true}).run' {} {}).toIO ctx st |>.toBaseIO
        pure (match r with
          | .ok (((decl, left, pdef), _), _) => Except.ok (decl, left, pdef, parent)
          | .error e => Except.error (toString e))
    let some m := (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
      | IO.eprintln s!"{c}: no module"; continue
    -- the source: Mathlib's, or Lean's own (Mul is in Init.Prelude)
    let rel := m.toString.replace "." "/" ++ ".lean"
    let (file, url) := if m.getRoot == `Mathlib then
        ((mathlib : System.FilePath) / rel, s!"https://github.com/leanprover-community/mathlib4/blob/COMMIT/{rel}")
      else (sysroot / "src" / "lean" / rel, s!"https://github.com/leanprover/lean4/blob/v{Lean.versionString}/src/{rel}")
    let src ← if ← file.pathExists then IO.FS.lines file else pure #[]
    let ranges ← match ← ((Lean.findDeclarationRanges? c : CoreM _).toIO ctx st |>.toBaseIO) with
      | .ok (some r, _) => pure r
      | _ => IO.eprintln s!"{c}: no source position"; continue
    -- the class as written, its docstring apart, up to the end of its fields
    let lines := (src.extract (ranges.range.pos.line - 1) ranges.range.endPos.line).toList
    let lines := if lines.head?.any (fun l => (strip l).startsWith "/--") then
        (lines.dropWhile (fun l => !(l.splitOn "-/").length > 1 )).drop 1 else lines
    let parents := (getStructureParentInfo env c).map (·.structName.toString)
    let common := s!"\"doc\": {jsonStr doc}, \"statement\": \"\", \"line\": {ranges.range.pos.line}, \"nameLine\": {ranges.selectionRange.pos.line}, \"endLine\": {ranges.range.endPos.line}, \"sourceModule\": {jsonStr m.toString}, \"source\": {jsonStr (strip ("\n".intercalate lines))}, \"url\": {jsonStr (url ++ s!"#L{ranges.selectionRange.pos.line}")}, \"extends\": [{", ".intercalate (parents.toList.map jsonStr)}]"
    -- in structures, the lattice operations: max and min are ⊔ and ⊓
    let lattice := mapTokens fun t => match t with
      | "Max__max" => "latticeSup" | "Min__min" => "latticeInf" | _ => t
    let res := res.map fun (decl, left, pdef, parent) => (lattice decl, left, pdef.map lattice, parent)
    match res with
    | .ok (decl, defaulted, pdef, parent) =>
      made := made.insert c (decl, defaulted, pdef, parent)
      let parentJson := match parent with | some p => jsonStr p.toString | none => "null"
      let derived := match mult with | some m => jsonStr m.toString | none => "null"
      dk := dk ++ s!"(; //LEAN:{c} ;)\n{decl}\n\n"
      json := json.push s!"\{\"lean\": {jsonStr c.toString}, \"dk\": {jsonStr (mangle c ++ "__structure")}, \"kind\": \"structure\", {common}, \"definiens\": false, \"structure\": true, \"parent\": {parentJson}, \"additiveOf\": {derived}, \"defaulted\": [{", ".intercalate (defaulted.toList.map (jsonStr ·.toString))}]}"
      if let some p := pdef then
        dk := dk ++ s!"(; //LEAN:{c} (predicate) ;)\n{p}\n\n"
        json := json.push s!"\{\"lean\": {jsonStr (c.toString ++ " (predicate)")}, \"dk\": {jsonStr (mangle c)}, \"kind\": \"class\", {common}, \"definiens\": true, \"structure\": false, \"parent\": {parentJson}, \"additiveOf\": {derived}}"
    | .error e =>
      dk := dk ++ s!"(; //LEAN:{c} ;)\n(; NOT EXPORTED: {e} ;)\n\n"
      IO.eprintln s!"{c}: {e}"
  IO.FS.createDirAll outDir
  IO.FS.writeFile s!"{outDir}/{outName}.dk" dk
  IO.FS.writeFile s!"{outDir}/{outName}-deps.dk" structureBase
  IO.FS.writeFile s!"{outDir}/{outName}.json" ("[\n" ++ ",\n".intercalate json.toList ++ "\n]\n")
  IO.println s!"{outName}: {json.size} structures and predicates -> {outDir}/{outName}.dk, {outDir}/{outName}.json"

/-- The lines of structures.txt: name, module, classes. -/
def readStructures : IO (List (Name × Name × List Name)) := do
  let path : System.FilePath := "structures.txt"
  if !(← path.pathExists) then return []
  let mut out := []
  for line in (← IO.FS.lines path) do
    if line.startsWith "#" || strip line == "" then continue
    match (line.splitOn " ").filter (· != "") |>.map String.toName with
    | n :: m :: cs => out := out ++ [(n, m, cs)]
    | _ => pure ()
  return out

/-! ## All definitions

`lake exe export --definitions [Prefix ...]` imports all of Mathlib and writes
out/definitions.jsonl: for each declaration of a Mathlib module (of one whose
name starts with a given prefix) that may need a symbol table entry (a
definition, structure, class, field, constructor, opaque constant or axiom,
not a theorem, an instance, a parent projection toX or an auxiliary or
deprecated declaration), one line with its Lean name, its Dedukti name, its
kind, its module, its docstring and its type translated as the statements are,
with the explicit arguments only. -/

/-- The nouns of the classes worded as "#1 is a monoid" in the symbol
tables, and the nouns of structures.dkgf: noun -> class. -/
def readClassNouns (classes : List Name) : IO (List (String × Name)) := do
  let byDk : Std.HashMap String Name := classes.foldl (fun m c => m.insert (mangle c) c) {}
  let mut out ← readNouns
  for file in ["mathlib.dkgf", "definitions.dkgf"] do
    let path : System.FilePath := file
    if !(← path.pathExists) then continue
    for l in ← IO.FS.lines path do
      match l.splitOn " : \"#1 is " with
      | [c, rest] =>
        if let some cl := byDk[c]? then
          let w := (rest.splitOn "\"").head!
          for art in ["a ", "an "] do
            if w.startsWith art then out := out ++ [((w.drop art.length).toString, cl)]
      | _ => pure ()
  return out

/-- Lean's notation as LaTeX, token by token; none for a token without one. -/
def latexToken (t : String) : Option String :=
  match t with
  | "≤" => "\\leq" | "≥" => "\\geq" | "<" => "<" | ">" => ">" | "≠" => "\\neq"
  | "∣" => "\\mid" | "⊆" => "\\subseteq" | "⊂" => "\\subset" | "⊇" => "\\supseteq"
  | "∩" => "\\cap" | "∪" => "\\cup" | "∈" => "\\in" | "∉" => "\\notin" | "\\" => "\\setminus"
  | "×" => "\\times" | "∘" => "\\circ" | "⊔" => "\\sqcup" | "⊓" => "\\sqcap"
  | "⊤" => "\\top" | "⊥" => "\\bot" | "•" => "\\cdot" | "∅" => "\\emptyset" | "∆" => "\\Delta"
  | "⊗" => "\\otimes" | "⊕" => "\\oplus" | "≃" => "\\simeq" | "≅" => "\\cong" | "≈" => "\\approx"
  | "≡" => "\\equiv" | "⋆" => "\\star" | "∗" => "\\ast" | "∞" => "\\infty"
  | "‖" => "\\|" | "⌊" => "\\lfloor" | "⌋" => "\\rfloor" | "⌈" => "\\lceil" | "⌉" => "\\rceil"
  | "⁻¹" => "^{-1}" | "ᶜ" => "^{c}" | "ᵀ" => "^{T}" | "ᵒᵖ" => "^{op}" | "ᵒᵈ" => "^{\\mathrm{od}}"
  | "⁺" => "^{+}" | "⁻" => "^{-}" | "√" => "\\sqrt" | "!" => "!" | "|" => "|"
  | "+" => "+" | "-" => "-" | "*" => "\\cdot" | "/" => "/" | "%" => "\\bmod" | "^" => "^"
  | "=" => "=" | "(" => "(" | ")" => ")" | "[" => "[" | "]" => "]" | "," => ","
  | "ℕ" => "\\mathbb{N}" | "ℤ" => "\\mathbb{Z}" | "ℚ" => "\\mathbb{Q}" | "ℝ" => "\\mathbb{R}"
  | "ℂ" => "\\mathbb{C}" | "0" => "0" | "1" => "1" | "2" => "2"
  | "≃*" => "\\simeq_{*}" | "≃+" => "\\simeq_{+}" | "≃+*" => "\\simeq_{+*}"
  | "ℚ≥0" => "\\mathbb{Q}_{\\geq 0}" | "ℝ≥0" => "\\mathbb{R}_{\\geq 0}" | "ℝ≥0∞" => "[0, \\infty]"
  | "#" => "\\#" | "ℕ∞" => "\\mathbb{N}_{\\infty}" | "ℕ+" => "\\mathbb{N}^{+}"
  | "⁅" => "[" | "⁆" => "]" | "∫" => "\\int" | "⟪" => "\\langle" | "⟫" => "\\rangle"
  | "+ᵥ" => "+_{v}" | "-ᵥ" => "-_{v}" | "×ˢ" => "\\times" | "⋃₀" => "\\bigcup" | "⋂₀" => "\\bigcap"
  | "ˣ" => "^{\\times}" | "ᵐᵒᵖ" => "^{\\mathrm{mop}}" | "ᵃᵒᵖ" => "^{\\mathrm{aop}}" | "ᵈ" => "^{\\mathrm{d}}"
  | "→" => "\\to" | "→*" => "\\to_{*}" | "→+" => "\\to_{+}" | "→+*" => "\\to_{+*}" | "→*₀" => "\\to_{*0}"
  | "→ₗ" => "\\to_{l}" | "→ₐ" => "\\to_{a}" | "≃ₗ" => "\\simeq_{l}" | "≃ₐ" => "\\simeq_{a}" | "→₀" => "\\to_{0}"
  | "↪" => "\\hookrightarrow" | "⇔" => "\\Leftrightarrow" | "∼" => "\\sim" | "~" => "\\sim" | "≌" => "\\simeq"
  | "⊗ₜ" => "\\otimes" | "⨁" => "\\bigoplus" | "⋊" => "\\rtimes" | "⨿" => "\\amalg" | "∐" => "\\coprod"
  | "⊙" => "\\odot" | "⊼" => "\\barwedge" | "⊻" => "\\veebar" | "⇨" => "\\Rightarrow" | "⊑" => "\\sqsubseteq"
  | "≼" => "\\preceq" | "⋖" => "\\lessdot" | "∠" => "\\angle" | "∡" => "\\measuredangle" | "∂" => "\\partial"
  | "ℵ₀" => "\\aleph_{0}" | "ℵ" => "\\aleph" | "ℶ" => "\\beth" | "ℍ" => "\\mathbb{H}" | "†" => "^{\\dagger}"
  | "ε" => "\\varepsilon" | "ω" => "\\omega" | "η" => "\\eta" | "σ" => "\\sigma" | "μ" => "\\mu"
  | "λ" => "\\lambda" | "ρ" => "\\rho" | "θ" => "\\theta" | "ζ" => "\\zeta" | "α" => "\\alpha"
  | "β" => "\\beta" | "π" => "\\pi" | "ψ" => "\\psi" | "φ" => "\\varphi" | "τ" => "\\tau"
  | "Γ" => "\\Gamma" | "Δ" => "\\Delta" | "Ω" => "\\Omega" | "Λ" => "\\Lambda"
  | _ => if t.startsWith "#" && (t.drop 1).all Char.isDigit then some t else none

/-- The notation of a definition, as Lean prints its application to its
arguments, in LaTeX with #k for the k-th explicit argument; none if Lean
prints it as an application of the name, or with binders or words. -/
def notationOf (n : Name) (ci : ConstantInfo) : MetaM (Option String) := do
  -- the explicit binders named ARG1, ARG2, ... to find them in the output
  let rec rename (t : Expr) (k : Nat) : Expr :=
    match t with
    | .forallE nm a b bi =>
      if bi.isExplicit then .forallE (.mkSimple s!"ARG{k}") a (rename b (k + 1)) bi
      else .forallE nm a (rename b k) bi
    | _ => t
  -- the scoped notations of its namespaces too (n ! of Nat)
  let rec prefixes (m : Name) : List Name := match m with
    | .str p _ => if p.isAnonymous then [] else p :: prefixes p
    | _ => []
  for ns in n :: prefixes n do activateScoped ns
  forallTelescope (rename ci.type 1) fun xs _ => do
    let e := mkAppN (mkConst n (ci.levelParams.map Level.param)) xs
    let fmt ← withOptions (fun o => (o.setBool `pp.fieldNotation false).setBool `pp.notation true) (ppExpr e)
    let out := toString fmt
    if out.contains '\n' || (out.splitOn ((n.componentsRev.headD .anonymous).toString)).length > 1 then
      return none
    -- tokens: the arguments ARGk, words, brackets, and runs of other symbols
    -- (≃+*, ℝ≥0, ⁻¹), which are tokens of their own
    let isWord (c : Char) := c.isAlphanum || c == '_'
    let brackets := "()[]|‖⌊⌋⌈⌉,".toList
    let mut toks : Array String := #[]
    let mut cur := ""
    for ch in out.toList do
      let kind (c : Char) : Nat := if isWord c then 0 else 1
      if ch == ' ' || brackets.contains ch then
        if cur != "" then toks := toks.push cur
        cur := ""
        if ch != ' ' then toks := toks.push ch.toString
      else if cur != "" && kind ch != kind (cur.back) then
        toks := toks.push cur; cur := ch.toString
      else cur := cur.push ch
    if cur != "" then toks := toks.push cur
    -- the digit of a symbol run (ℝ≥0) is part of it
    let mut joined : Array String := #[]
    for t in toks do
      match joined.back? with
      | some prev => if t.all Char.isDigit && !(prev.all isWord) && !brackets.contains prev.front
                       && prev != "+" && prev != "-" && prev != "*" && prev != "/" && prev != "^" && prev != "=" then
                       joined := joined.pop.push (prev ++ t)
                     else joined := joined.push t
      | none => joined := joined.push t
    let args := joined.map fun t => if t.startsWith "ARG" && (t.drop 3).all Char.isDigit then "#" ++ (t.drop 3).toString else t
    let mut parts : Array String := #[]
    for t in args do
      match latexToken t with
      | some l => parts := parts.push l
      | none =>
        -- the tokens without LaTeX, to be added to latexToken
        if (← IO.getEnv "EXPORT_NOTATION_TOKENS").isSome then IO.eprintln s!"NOTATION-TOKEN {t}"
        return none
    -- at least one symbol, not the arguments alone or brackets
    if parts.all (fun p => p.startsWith "#" || ["(", ")", ",", "[", "]"].contains p) then return none
    -- an exponent in braces: #1 ^ #2 as {#1}^{#2}
    let mut res := ""
    let mut i := 0
    while i < parts.size do
      let p := parts[i]!
      if p == "^" && i + 1 < parts.size then
        res := res ++ "^{" ++ parts[i+1]! ++ "}"; i := i + 2
      else
        res := (if res == "" || p.startsWith "^" || p == "!" then res else res ++ " ") ++ p; i := i + 1
    -- the arguments of a root in braces; [0, ∞] for ℝ≥0∞
    let res' := (List.range 9).foldl (fun r k => r.replace s!"\\sqrt #{k+1}" s!"\\sqrt\{#{k+1}}") res
    let fin := res'.replace "\\mathbb{R}_{\\geq 0} \\infty" "[0, \\infty]"
    -- not brackets as Lean's subscripts (⊗[R], μ[f|m], f^[n]), which LaTeX writes otherwise
    if (fin.splitOn " [ ").length > 1 || (fin.splitOn "[ ]").length > 1 || (fin.splitOn "^{[}").length > 1
       || (fin.splitOn "\\lfloor /").length > 1 || (fin.splitOn "\\lceil /").length > 1 then return none
    return some s!"${fin}$"

/-- A class as a structure, as on the Structures pages: its structure
declaration and its predicate definition, or the error. -/
def classStructure (env : Environment) (mapping : Std.HashMap Name String)
    (keepAll binders : Std.HashSet Name) (ctx : Core.Context) (st : Core.State)
    (classes : List Name) (nouns : List (String × Name)) (n : Name) (doc : String) :
    IO (Except String (String × Option String × Option Name)) := do
  let primary := primaryParent env n classes nouns doc
  let parent := match primary with
    | some p => some p
    | none => instanceParent env n (nouns.map (·.2))
  let r ← (((structureDecl n parent (primary.isNone && parent.isSome)).run {mapping, binders, keepAll}).run' {} {}).toIO ctx st |>.toBaseIO
  -- in structures, the lattice operations: max and min are ⊔ and ⊓
  let lattice := mapTokens fun t => match t with
    | "Max__max" => "latticeSup" | "Min__min" => "latticeInf" | _ => t
  return match r with
    | .ok (((decl, _, pdef), _), _) => .ok (lattice decl, pdef.map lattice, parent)
    | .error e => .error (toString e)

def definitionLine (env : Environment) (mapping : Std.HashMap Name String)
    (keepAll binders : Std.HashSet Name) (ctx : Core.Context) (st : Core.State)
    (classes : List Name) (nouns : List (String × Name))
    (mod n : Name) (ci : ConstantInfo) : IO (Option String) := do
  let res ← (((statement ci.type).run {mapping, binders, keepAll}).run' {} {}).toIO ctx st |>.toBaseIO
  let .ok ((s, _), _) := res | return none
  let doc := (← Lean.findDocString? env n).getD ""
  let field := (env.getProjectionFnInfo? n).isSome
  -- the definiens, as the modules' definitions have it: not a compiled pattern
  -- matching or recursion, not a class, and not too big to read
  let mut defn := ""
  if let some v := ci.value? (allowOpaque := false) then
    if !isClass env n then
      let vres ← (((value ci.type v).run {mapping, binders, keepAll}).run' {} {}).toIO ctx st |>.toBaseIO
      if let .ok ((vs, _), _) := vres then
        let compiled := ["UNSUPPORTED", "match_", "casesOn", "__rec ", "_private", "_proof_"].any
                          fun w => (vs.splitOn w).length > 1
        if !compiled && vs.length ≤ 3000 then defn := vs
  -- a class as a structure by extension of its parent, and as a predicate
  let mut asStructure := ""
  if isClass env n && isStructure env n then
    asStructure := match ← classStructure env mapping keepAll binders ctx st classes nouns n doc with
      | .ok (decl, pdef, parent) =>
        s!", \"structureDecl\": {jsonStr decl}, \"predicateDef\": {jsonStr (pdef.getD "")}, \"parent\": {jsonStr ((parent.map toString).getD "")}"
      | .error e => s!", \"structureError\": {jsonStr e}"
  -- Lean's notation for it, in LaTeX
  let notat := match ← ((notationOf n ci).run' {} {}).toIO ctx st |>.toBaseIO with
    | .ok (some l, _) => s!", \"notation\": {jsonStr l}"
    | _ => ""
  return some s!"\{\"lean\": {jsonStr n.toString}, \"dk\": {jsonStr (mangle n)}, \"kind\": {jsonStr (kindOf ci)}, \"module\": {jsonStr mod.toString}, \"class\": {isClass env n}, \"structure\": {isStructure env n}, \"field\": {field}, \"doc\": {jsonStr doc}, \"type\": {jsonStr (asPredicate env n s)}, \"definiens\": {jsonStr defn}{asStructure}{notat}}"

def exportDefinitions (prefixes : List String) (mapping : Std.HashMap Name String)
    (keepAll binders : Std.HashSet Name) : IO Unit := do
  let env ← importModules #[{ module := `Mathlib }] {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<export>", fileMap := default, maxHeartbeats := 0,
                              options := {} }
  let st : Core.State := { env }
  let inScope (m : String) := m.startsWith "Mathlib." &&
    (prefixes.isEmpty || prefixes.any fun p => m == p || m.startsWith (p ++ "."))
  -- the classes, for the parents of the classes read as structures
  let classes := env.constants.fold (fun acc n _ => if isClass env n && isStructure env n then n :: acc else acc) []
  let nouns ← readClassNouns classes
  let mut out := #[]
  let mut failed := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if !inScope mod.toString then continue
    for n in data.constNames do
      let some ci := env.find? n | continue
      if ci matches .thmInfo _ then continue
      if !wanted env n ci then continue
      -- the projections to parent structures are coercions, not words
      if let some sname := env.getProjectionStructureName? n then
        if let .str _ f := n then
          if (isSubobjectField? env sname (.mkSimple f)).isSome then continue
      match ← definitionLine env mapping keepAll binders ctx st classes nouns mod n ci with
      | some l => out := out.push l
      | none => failed := failed + 1
  IO.FS.createDirAll "out"
  IO.FS.writeFile "out/definitions.jsonl" ("\n".intercalate out.toList ++ "\n")
  IO.println s!"{out.size} definitions -> out/definitions.jsonl; {failed} not translated"

/-! ## Tactic proofs

`lake exe export --tactics <Module>` elaborates the module again from its
source with info trees, and writes out/<Module>-tactics.json: for each step of
a tactic proof (a tactic of a tactic sequence, written in the source), its
position and text, the main goal before it and the goals after it, each with
its hypotheses and target translated to Dedukti. -/

open Lean.Elab in
/-- The goal as JSON: its hypotheses (name and Dedukti type) and target;
translated by `to_additive` as many times as `translate` says, for the
additive twin of a theorem (twice for the twin of a twin). -/
def goalJson (ci : ContextInfo) (mctx : MetavarContext) (g : MVarId)
    (mapping : Std.HashMap Name String) (keepAll binders : Std.HashSet Name)
    (translate : Nat := 0) : IO String := do
  let act : MetaM String := do
    let decl ← g.getDecl
    withLCtx decl.lctx decl.localInstances do
      let locals := decl.lctx.foldl (init := #[]) fun acc d =>
        if d.isImplementationDetail then acc else acc.push d
      let m (ds : Array LocalDecl) (target : Expr) : M String := do
        let mut hs := #[]
        for d in ds do
          let nm := d.userName.eraseMacroScopes.toString (escape := false)
          let ty ← hypoType (← Core.betaReduce (← instantiateMVars d.type))
          hs := hs.push s!"[{jsonStr nm}, {jsonStr ty}, {if d.userName.hasMacroScopes then "true" else "false"}]"
        -- β-reduced: a goal often has (fun x => P x) a after a rewrite
        let tgt ← tr (← Core.betaReduce (← instantiateMVars target))
        return s!"\{\"hyps\": [{", ".intercalate hs.toList}], \"target\": {jsonStr tgt}}"
      let run (ds : Array LocalDecl) (target : Expr) : MetaM String :=
        (m ds target).run' {mapping, binders, keepAll, proofMode := true, keepImplicit := true}
      if translate == 0 then run locals decl.type else
      let mut e ← instantiateMVars (← mkForallFVars (locals.map (·.toExpr)) decl.type)
      for _ in [0:translate] do
        e := (← Mathlib.Tactic.Translate.applyReplacementForall Mathlib.Tactic.ToAdditive.data [] e).1
      forallTelescope e fun xs body => do
        run (← xs.mapM (·.fvarId!.getDecl)) body
  try
    ({ ci with mctx := mctx }).runMetaM decl0 act
  catch e => return s!"\{\"error\": {jsonStr (toString e)}}"
where decl0 : LocalContext := {}

def seqKinds : List Name :=
  [``Lean.Parser.Tactic.tacticSeq, ``Lean.Parser.Tactic.tacticSeq1Indented,
   ``Lean.Parser.Tactic.tacticSeqBracketed]

open Lean.Elab in
/-- The steps of the tactic proofs in an info tree: the tactics directly
inside a tactic sequence, written in the source (not made by a macro). -/
partial def tacticSteps (ctx? : Option ContextInfo) (inSeq : Bool) :
    InfoTree → StateT (Array (ContextInfo × TacticInfo)) IO Unit
  | .context pci t => tacticSteps (pci.mergeIntoOuter? ctx?) inSeq t
  | .node i cs => do
    match i with
    | .ofTacticInfo ti =>
      if seqKinds.contains ti.stx.getKind then
        cs.forM (tacticSteps ctx? true)
      else
        if inSeq && (ti.stx.getPos? (canonicalOnly := true)).isSome then
          if let some ci := ctx? then modify (·.push (ci, ti))
        cs.forM (tacticSteps ctx? false)
    | _ => cs.forM (tacticSteps ctx? inSeq)
  | .hole _ => pure ()

open Lean.Elab in
/-- Elaborate a source file with info trees: the environment it makes, its
messages, and the steps of its tactic proofs as JSON lines. -/
def elaborate (path : System.FilePath) (mapping : Std.HashMap Name String)
    (keepAll binders : Std.HashSet Name) : IO (Environment × MessageLog × Array String) := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let cmdState := { Command.mkState env messages {} with infoState := { enabled := true } }
  let s ← IO.processCommands inputCtx parserState cmdState
  let fileMap := inputCtx.fileMap
  let mut out := #[]
  for t in s.commandState.infoState.trees do
    let ((), steps) ← (tacticSteps none false t).run #[]
    for (ci, ti) in steps do
      let some pos := ti.stx.getPos? (canonicalOnly := true) | continue
      let endPos := (ti.stx.getTailPos? (canonicalOnly := true)).getD pos
      let p := fileMap.toPosition pos
      let e := fileMap.toPosition endPos
      let text := (String.Pos.Raw.extract input pos endPos)
      -- the theorem the step proves, and its additive twins (`to_additive`
      -- makes them from its proof): the step once for each, its goals
      -- translated for a twin
      let decl := ci.parentDecl?.getD .anonymous
      let mut decls := #[decl]
      while decls.size < 3 do
        match Mathlib.Tactic.Translate.findTranslationName? s.commandState.env
                Mathlib.Tactic.ToAdditive.data decls.back! with
        | some t => decls := decls.push t
        | none => break
      for k in [0:decls.size] do
        let before ← match ti.goalsBefore with
          | g :: _ => goalJson ci ti.mctxBefore g mapping keepAll binders k
          | [] => pure "null"
        let mut after := #[]
        for g in ti.goalsAfter do
          after := after.push (← goalJson ci ti.mctxAfter g mapping keepAll binders k)
        out := out.push s!"\{\"line\": {p.line}, \"col\": {p.column}, \"endLine\": {e.line}, \"decl\": {jsonStr decls[k]!.toString}, \"kind\": {jsonStr ti.stx.getKind.toString}, \"nBefore\": {ti.goalsBefore.length}, \"tactic\": {jsonStr text}, \"before\": {before}, \"after\": [{", ".intercalate after.toList}]}"
  return (s.commandState.env, s.commandState.messages, out)

def writeTactics (outDir : String) (mod : Name) (steps : Array String) : IO Unit := do
  IO.FS.createDirAll outDir
  IO.FS.writeFile s!"{outDir}/{mod}-tactics.json" ("[\n" ++ ",\n".intercalate steps.toList ++ "\n]\n")
  IO.println s!"{mod}: {steps.size} tactic steps -> {outDir}/{mod}-tactics.json"

def exportTactics (mod : Name) (mapping : Std.HashMap Name String)
    (keepAll binders : Std.HashSet Name) : IO Unit := do
  let mathlib := (← IO.getEnv "MATHLIB").getD "../mathlib4"
  let path : System.FilePath := mathlib ++ "/" ++ (mod.toString.replace "." "/") ++ ".lean"
  let (_, _, steps) ← elaborate path mapping keepAll binders
  writeTactics "out" mod steps

/-! ## Any Lean file

`lake exe export --file <File.lean> <outDir>` elaborates a Lean file (one that
imports Mathlib, say) and exports the declarations it makes as a module named
after the file: <outDir>/<File>.dk, .json, -deps.dk and -tactics.json. Its
error messages go to standard error, and the exit code is 1 if there are any. -/

def exportFile (path : System.FilePath) (outDir : String) (mapping : Std.HashMap Name String)
    (keepAll binders : Std.HashSet Name) : IO UInt32 := do
  let (env, messages, steps) ← elaborate path mapping keepAll binders
  let mut errors := 0
  for m in messages.toList do
    if m.severity == .error then
      errors := errors + 1
      IO.eprintln (← m.toString)
  let mod := (path.fileStem.getD "Input").toName
  -- the constants that the file adds, not the imported ones
  let names := env.constants.map₂.toList.map (·.1) |>.toArray
  let src ← IO.FS.lines path
  exportDecls env mapping keepAll binders mod names src outDir
  writeTactics outDir mod steps
  return if errors > 0 then 1 else 0

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake exe export <Module> ..."
    return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  if args.head? == some "--file" then
    let [path, outDir] := args.tail | do
      IO.eprintln "usage: lake exe export --file <File.lean> <outDir>"; return 1
    let (mapping, keepAll) ← readMapping
    let binders ← readBinders
    return ← exportFile path outDir mapping keepAll binders
  if args.head? == some "--definitions" then
    let (mapping, keepAll) ← readMapping
    let binders ← readBinders
    exportDefinitions args.tail mapping keepAll binders
    return 0
  if args.head? == some "--structures" then
    let (mapping, keepAll) ← readMapping
    let binders ← readBinders
    -- the modules of all the pages at once: Lean imports only once in a process
    let pages ← readStructures
    let env ← importModules (pages.map fun (_, m, _) => { module := m }).toArray {} (loadExts := true)
    for (n, _, cs) in pages do
      exportStructures env n cs mapping keepAll binders
    return 0
  if args.head? == some "--tactics" then
    -- only the first file elaborated in a process gets its info trees, so
    -- several modules are exported by one process each
    if args.tail.length > 1 then
      for m in args.tail do
        let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["--tactics", m] }
        IO.print out.stdout
        IO.eprint out.stderr
      return 0
    let (mapping, keepAll) ← readMapping
    let binders ← readBinders
    for m in args.tail.map String.toName do
      exportTactics m mapping keepAll binders
    return 0
  -- the names of structures.txt are exported by --structures, not as modules
  let structs := (← readStructures).map (·.1)
  let mods := (args.map String.toName).filter (!structs.contains ·)
  let env ← importModules (mods.map fun m => { module := m }).toArray {} (loadExts := true)
  let (mapping, keepAll) ← readMapping
  let binders ← readBinders
  for m in mods do
    exportModule env mapping keepAll binders m
  return 0
