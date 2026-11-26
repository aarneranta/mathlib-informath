/-
The declarations of grh-lean/grh-compact that its five main theorems depend
on, with what each one uses, for the book (../make-book.py).

    lake exe deps > ../work/deps.json

Starting from the five theorems of `Main`, every constant of the project (of
the modules `Statements`, `Main`, `Lib.*`, `New.*`) that their statements or
proofs use is collected, transitively. A constant made by Lean itself (an
auxiliary lemma `_proof_1`, a `match_1`, an equation lemma) is not listed:
it is looked through, and what it uses counts as used by the declaration it
belongs to. Each declaration is printed as a JSON object:

* `name`, `module`, `kind` (theorem, def, axiom, structure, class,
  inductive, instance, constructor, opaque), `line`, `endLine`;
* `stmt`: the project constants its statement (type) uses;
* `uses`: the project constants its proof or definiens uses;
* `mathlib`: the theorems of Mathlib that its proof or definiens names;
* `doc`: its docstring, if any.
-/
import Main
import Lean

open Lean Meta

def projectModule (m : Name) : Bool :=
  m == `Statements || m == `Main || m.getRoot == `Lib || m.getRoot == `New

/-- Constants made by Lean: looked through, not listed. -/
def isAux (env : Environment) (n : Name) : Bool :=
  n.isInternal || isAuxRecursor env n || isNoConfusion env n ||
  (n.components.any fun c => match c with
    | .str _ s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s == "eq_def" ||
        s.startsWith "eq_" && (s.drop 3).all Char.isDigit
    | _ => false)

/-- The definiens or the proof of a constant (`value?` leaves out theorems). -/
def bodyOf : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

def constsOf (e : Expr) : NameSet :=
  e.foldConsts {} fun c acc => acc.insert c

def jstr (s : String) : String := (Json.str s).compress

def jarr (ns : List Name) : String :=
  "[" ++ ", ".intercalate (ns.map fun n => jstr n.toString) ++ "]"

def kindOf (env : Environment) (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"
  | .inductInfo _ => if isClass env ci.name then "class" else if isStructure env ci.name then "structure" else "inductive"
  | .defnInfo _ => if isInstanceCore env ci.name then "instance" else "def"

unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Main}] {} (trustLevel := 1024) (loadExts := true)
  let modOf (n : Name) : Option Name := do
    let i ← env.getModuleIdxFor? n
    env.header.moduleNames[i.toNat]?
  let isProject (n : Name) : Bool := match modOf n with
    | some m => projectModule m
    | none => false
  -- the constants that an expression uses, looking through Lean's auxiliary ones
  let rec expand (fuel : Nat) (seen : NameSet) (todo : List Name) (acc : NameSet) : NameSet :=
    match fuel, todo with
    | 0, _ => acc
    | _, [] => acc
    | f + 1, c :: rest =>
      if seen.contains c then expand f seen rest acc
      else if isAux env c && isProject c then
        match env.find? c with
        | some ci =>
          let inner := (constsOf ci.type).toList ++ ((bodyOf ci).map (fun v => (constsOf v).toList)).getD []
          expand f (seen.insert c) (inner ++ rest) acc
        | none => expand f (seen.insert c) rest acc
      else expand f (seen.insert c) rest (acc.insert c)
  let direct (e : Expr) : NameSet := expand 100000 {} (constsOf e).toList {}
  let roots := [`riemannHypothesis, `riemannZeta_eq_zero_re, `LFunction_ne_zero_of_half_lt_re,
                `LFunction_eq_zero_re, `LFunction_eq_zero_re_of_isPrimitive]
  -- the closure over the project's constants
  let mut done : NameSet := {}
  let mut todo := roots
  let mut order : Array Name := #[]
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if done.contains c then continue
    done := done.insert c
    let some ci := env.find? c | continue
    order := order.push c
    let deps := direct ci.type ++ (((bodyOf ci).map direct).getD {})
    -- a structure's or inductive's constructors and fields come with it
    let extra : List Name := match ci with
      | .inductInfo ii => ii.ctors
      | .ctorInfo ci' => [ci'.induct]
      | _ => []
    for d in deps.toList ++ extra do
      if isProject d && !done.contains d then todo := d :: todo
  IO.eprintln s!"{order.size} project declarations in the closure of the five theorems"
  IO.println "["
  let mut first := true
  let mut mathSeen : NameSet := {}
  let mut mathLoc : Array String := #[]
  for c in order do
    let some ci := env.find? c | continue
    let stmt := (direct ci.type).toList.filter fun d => isProject d && d != c
    let body := ((bodyOf ci).map direct).getD {}
    let uses := body.toList.filter fun d => isProject d && d != c
    -- the theorems of Mathlib that the proof applies (not Lean's logic, nor definitions)
    let lib := body.toList.filter fun d =>
      !isProject d && !isAux env d && !(isInstanceCore env d) &&
      (match env.find? d with | some (.thmInfo _) => true | _ => false) &&
      (match modOf d with | some m => m.getRoot == `Mathlib | none => false)
    let mod := (modOf c).getD .anonymous
    let rng := declRangeExt.find? env c
    let (l0, l1) := match rng with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    let doc ← findDocString? env c
    -- where the Mathlib theorems cited are: module and line, for the links
    for d in lib do
      unless mathSeen.contains d do
        mathSeen := mathSeen.insert d
        let r := declRangeExt.find? env d
        mathLoc := mathLoc.push s!"{jstr d.toString}: [{jstr ((modOf d).getD .anonymous).toString}, {(r.map (·.range.pos.line)).getD 0}]"
    let line := s!"\{\"name\": {jstr c.toString}, \"module\": {jstr mod.toString}, \"kind\": {jstr (kindOf env ci)}, \"line\": {l0}, \"endLine\": {l1}, \"stmt\": {jarr stmt}, \"uses\": {jarr uses}, \"mathlib\": {jarr lib}, \"doc\": {jstr (doc.getD "")}}"
    IO.println ((if first then "" else ",\n") ++ line)
    first := false
  IO.println "]"
  IO.FS.writeFile "../work/mathlib-locations.json" ("{" ++ ",\n".intercalate mathLoc.toList ++ "}\n")
