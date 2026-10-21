/-
Export the statements of Mathlib declarations to Informath's Dedukti dialect.

    lake exe export Mathlib.Data.Nat.Prime.Defs [more modules]   # -> out/<Module>.dk, .json

For each declaration of the given modules (theorems, definitions, axioms, and
structures and classes with their fields), the type is translated:

* a binder `(x : α)` with `α : Type` becomes `(x : Elem α)`, one with `α : Prop`
  becomes `(h : Proof α)`, and `(α : Type u)` becomes `(α : Set)`;
* an instance binder `[Group G]` becomes a hypothesis `(_ : Proof (Group G))`;
* in applications, implicit and instance arguments are dropped, so that only the
  arguments a reader sees in Mathlib remain;
* the constants of `mapping.tsv` become Informath's own (`Dvd.dvd` is `divide`,
  `Nat.Prime` is `prime`, ...), so that Informath's base readings apply, and the
  logical constants become `and`, `or`, `if`, `not`, `iff`, `forall`, `exists`;
* any other constant keeps its Lean name, with `.` written `__`.

Each declaration is preceded by `(; //LEAN:<name> ;)`.  out/<Module>.json has,
for each declaration, its Lean name, its Dedukti name, its kind, its docstring
and Lean's own statement, for the index and for comparing the readings.
out/<Module>-deps.dk declares the constants that the statements use but that
are neither exported nor mapped, with their types translated the same way.

The output is meant to be read by Informath, not checked by Dedukti: dropping
implicit arguments loses information that a type checker would need.
-/
import Lean

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
  derived : Std.HashMap String String := {}  -- c__app constants and their types
  binders : Std.HashSet Name := {}   -- constants of binders.txt
  names : Std.HashSet String := {}   -- variable names in use

abbrev M := StateRefT St MetaM

/-- A variable name for a binder: the user's name if it is a plain identifier
and free, else a fresh one. -/
def freshName (n : Name) (prop : Bool) : M String := do
  let base0 := (n.eraseMacroScopes.toString (escape := false))
  let ok := !base0.isEmpty && base0.all (fun c => c.isAlphanum || c == '_' || c == '\'') &&
    !(base0.toList.head?.map Char.isDigit |>.getD false) && !n.hasMacroScopes
  let base := if ok then base0 else if prop then "h" else "x"
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

mutual

/-- An expression of type Prop, an object, or a type, in Dedukti. -/
partial def tr (e : Expr) : M String := do
  match e with
  | .mdata _ b => tr b
  | .fvar id => return (← id.getUserName).toString  -- names are fixed when bound
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
      let fs ← tr f
      let as ← args.mapM tr
      return " ".intercalate (paren fs :: (as.map paren).toList)
  | .lam n t b bi => binder n t b bi true
  | .forallE n t b bi => binder n t b bi false
  | .letE _ _ v b _ => tr (b.instantiate1 v)
  | .proj s i b => return s!"{mangle s}__proj{i} {paren (← tr b)}"
  | _ => return "UNSUPPORTED"

/-- A λ or a Π / ∀: a quantifier or an implication in a Prop, a function
type elsewhere. -/
partial def binder (n : Name) (t b : Expr) (bi : BinderInfo) (isLam : Bool) : M String := do
  let prop ← isProp t
  let nm ← freshName n prop
  -- the local gets the chosen name, so that tr of its fvar prints it
  withLocalDecl (Name.mkSimple nm) bi t fun y => do
      let body := b.instantiate1 y
      let bs ← tr body
      if isLam then
        return s!"{nm} => {bs}"
      let bodyProp ← isProp body
      if bodyProp then
        if prop && !b.hasLooseBVars then
          return s!"if {paren (← tr t)} {paren bs}"
        if prop then
          return s!"forall (Proof {paren (← tr t)}) ({nm} => {bs})"
        return s!"forall {paren (← typeOf t)} ({nm} => {bs})"
      if !b.hasLooseBVars then
        return s!"{← hypoType t} -> {bs}"
      return s!"({nm} : {← hypoType t}) -> {bs}"

/-- The Set an object of type t belongs to: Nat for ℕ. -/
partial def typeOf (t : Expr) : M String := tr t

/-- The type of a hypothesis: Elem α, Proof P, or Set. -/
partial def hypoType (t : Expr) : M String := do
  if (← isProp t) then return s!"Proof {paren (← tr t)}"
  if t.isProp then return "Prop"
  if t.isSort then return "Set"
  if (← isType t) then
    -- t is a type of types (α → Type): a function into Set
    if (← whnf t).isForall then return s!"({← tr t})"
  return s!"Elem {paren (← tr t)}"

/-- An application of a constant, with the special cases of the mapping. -/
partial def app (c : Name) (args : Array Expr) (whole : Expr) : M String := do
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
  -- numerals: OfNat.ofNat α n inst
  if c == ``OfNat.ofNat && args.size ≥ 2 then
    if let .lit (.natVal n) := args[1]!.consumeMData then return numeral n
  -- casts between number types are the identity in Informath's Num
  if (c == ``Nat.cast || c == ``Int.cast || c == ``NatCast.natCast || c == ``IntCast.intCast
      || c == ``Subtype.val || c == `SetLike.coe)
      && args.size ≥ 1 then
    return ← tr args.back!
  -- an element of a subtype, Subtype.mk x h, is x
  if c == ``Subtype.mk && args.size == 4 then
    return ← tr args[2]!
  -- ∃ x, p x  /  Exists (fun x => p x)
  if c == ``Exists && args.size == 2 then
    let p := args[1]!
    match p with
    | .lam n t b bi => do
      let s ← binder n t b bi true
      return s!"exists {paren (← tr t)} ({s})"
    | _ => return s!"exists {paren (← tr args[0]!)} (x => {paren (← tr p)} x)"
  -- equality: Eq on numbers, Eqt elsewhere
  if c == ``Eq && args.size == 3 then
    let ty ← tr args[0]!
    let a ← tr args[1]!; let b ← tr args[2]!
    if ty == "Nat" || ty == "Int" || ty == "Real" || ty == "Rat" then
      return s!"Eq {paren a} {paren b}"
    return s!"Eqt {paren ty} {paren a} {paren b}"
  let target := (← get).mapping.get? c
  let expl ← try explicitArgs c catch _ => pure (args.map fun _ => true)
  let shown := (args.toList.zip (expl.toList ++ List.replicate args.size true)).filter (·.2) |>.map (·.1)
  let head ← match target with
    | some t => pure t
    | none => do
      modify fun s => { s with used := s.used.insert c }
      pure (mangle c)
  if shown.isEmpty then return head
  -- the function arguments of a binder constant are λs, eta-expanded if need be
  let binder := (← get).binders.contains c
  let as ← shown.mapM fun a => do
    if binder then
      -- all its arguments, as the macro shows each bound variable: f to x y => f x y
      let ty ← whnf (← inferType a)
      if ty.isForall then
        return ← tr (← Core.betaReduce (← etaExpand a))
    tr a
  return " ".intercalate (head :: as.map paren)

end

/-- The statement of a declaration as a Dedukti type: its binders as
hypotheses, its conclusion as Proof P (a theorem) or as the type of the
object it defines. -/
partial def statementGo (explicitOnly : Bool) (t : Expr) : M String := do
    match t with
    | .forallE n ty b bi => do
      let prop ← isProp ty
      let nm ← freshName n prop
      withLocalDecl (Name.mkSimple nm) bi ty fun y => do
        let rest ← statementGo explicitOnly (b.instantiate1 y)
        if explicitOnly && bi != .default then return rest
        let h ← if bi == .instImplicit then do pure s!"(_ : Proof {paren (← tr ty)})"
                 else do pure s!"({nm} : {← hypoType ty})"
        return s!"{h} -> {rest}"
    | _ => do
      if (← isProp t) then return s!"Proof {paren (← tr t)}"
      hypoType t

/-- A theorem is stated with all its hypotheses, implicit ones included, as
they are its statement; any other constant (a definition, a structure, a
primitive) with its explicit arguments only, the ones its applications show,
so that the #k of its symbol table entry count the same arguments. -/
def statement (type : Expr) : M String := do
  statementGo (!(← isProp type)) type

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

def readMapping : IO (Std.HashMap Name String) := do
  let path : System.FilePath := "mapping.tsv"
  if !(← path.pathExists) then return {}
  let mut m := {}
  for line in (← IO.FS.lines path) do
    if line.startsWith "#" || strip line == "" then continue
    match line.splitOn "\t" with
    | [l, d] => m := m.insert (strip l).toName (strip d)
    | _ => pure ()
  return m

def exportModule (env : Environment) (mapping : Std.HashMap Name String)
    (binders : Std.HashSet Name) (mod : Name) :
    IO Unit := do
  let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"module {mod} not loaded"
  -- in the order of the source, as the module records them
  let names := env.header.moduleData[idx.toNat]!.constNames
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
  let mut dk := s!"(; {mod}: statements exported from Mathlib by MathlibInformath/Export.lean ;)\n\n"
  let mut json := #[]
  let mut used : Std.HashSet Name := {}
  let mut derived : Std.HashMap String String := {}
  for (n, ci) in decls do
    let act : M String := statement ci.type
    let res ← ((act.run {mapping, binders}).run' {} {}).toIO ctx st |>.toBaseIO
    let doc ← (Lean.findDocString? env n)
    let pp ← ((Meta.ppExpr ci.type).run' {} {}).toIO ctx st |>.toBaseIO
    let ppStr := match pp with | .ok (f, _) => toString f | .error _ => ""
    match res with
    | .ok ((s, stt), _) =>
      used := stt.used.fold (fun acc c => acc.insert c) used
      derived := stt.derived.fold (fun acc k v => acc.insert k v) derived
      dk := dk ++ s!"(; //LEAN:{n} ;)\n{mangle n} : {asPredicate env n s}.\n\n"
      let r := lineOf.get! n
      json := json.push s!"\{\"lean\": {jsonStr n.toString}, \"dk\": {jsonStr (mangle n)}, \"kind\": {jsonStr (kindOf ci)}, \"doc\": {jsonStr (doc.getD "")}, \"statement\": {jsonStr ppStr}, \"line\": {r.range.pos.line}, \"nameLine\": {r.selectionRange.pos.line}, \"endLine\": {r.range.endPos.line}}"
    | .error e =>
      dk := dk ++ s!"(; //LEAN:{n} ;)\n(; NOT EXPORTED: {toString e} ;)\n\n"
  -- the constants used but neither exported nor mapped
  let exported : Std.HashSet Name := decls.foldl (fun acc (n, _) => acc.insert n) {}
  let mut deps := s!"(; constants used by {mod}, declared with their translated types ;)\n\n"
  for (nm, ty) in derived.toList.toArray.qsort (·.1 < ·.1) do
    deps := deps ++ s!"(; a constant applied as a function: DFunLike.coe ;)\n{nm} : {ty}.\n\n"
  for c in used.toList.toArray.qsort (·.toString < ·.toString) do
    if exported.contains c then continue
    let some ci := env.find? c | continue
    let res ← (((statement ci.type).run {mapping, binders}).run' {} {}).toIO ctx st |>.toBaseIO
    match res with
    | .ok ((s, _), _) =>
      let doc := ((← Lean.findDocString? env c).getD "").replace "\n" " " |>.replace ";)" "; )"
      let docLine := if doc.isEmpty then "" else s!"(; doc: {doc} ;)\n"
      deps := deps ++ s!"{docLine}(; //LEAN:{c} ;)\n{mangle c} : {asPredicate env c s}.\n\n"
    | .error _ => deps := deps ++ s!"(; NOT EXPORTED: {c} ;)\n\n"
  IO.FS.createDirAll "out"
  IO.FS.writeFile s!"out/{mod}.dk" dk
  IO.FS.writeFile s!"out/{mod}-deps.dk" deps
  IO.FS.writeFile s!"out/{mod}.json" ("[\n" ++ ",\n".intercalate json.toList ++ "\n]\n")
  IO.println s!"{mod}: {decls.length} declarations -> out/{mod}.dk, out/{mod}.json; {used.size} constants used"

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake exe export <Module> ..."
    return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods := args.map String.toName
  let env ← importModules (mods.map fun m => { module := m }).toArray {} (loadExts := true)
  let mapping ← readMapping
  let binders ← readBinders
  for m in mods do
    exportModule env mapping binders m
  return 0
