/-
`#verbalize` writes an ordinary Lean tactic proof as a Verbose Lean proof
(https://github.com/PatrickMassot/verbose-lean4), which Lean with Verbose can
check again.  A prototype: see README.md, "Verbose as an output style".

    cd ~/claude/verbose-lean4 && lake env lean <this directory>/SeqContVerbose.lean

Each step of the proof is one Verbose sentence, as Verbose's own help writes
them:

* `intro`: "Fix ε > 0" for an object with a condition named as Verbose names
  it (ε_pos, n_ge), else "Fix x" and "Assume h : P";
* `rcases e with ...`, `obtain ... := e`: "By hf applied to ε using ε_pos we
  get δ such that (δ_pos : δ > 0) and (Hf : ...)";
* `use t`: "Let's prove that t works";
* `exact e`: "We conclude by Hf applied to u n using Hu n n_ge";
* any other tactic as it is (a Verbose proof may use Lean's tactics).

The statement is written as Verbose's `Example`, its objects under Given:,
its hypotheses under Assume:.  Formulas are printed by Lean, with the
notations in scope (Verbose's ⇒, `u converges to l`).
-/
import Verbose.English.ExampleLib

open Lean Elab Command Term Meta

namespace VerboseGen

/-- The name Verbose's `Fix x rel e` gives to the hypothesis (Verbose/Tactics/Fix.lean). -/
def fixHypName (x : Name) (rel : String) (zero : Bool) : String :=
  let s := x.toString
  if zero then
    match rel with
    | "<" | "≤" => s ++ "_neg"
    | _ => s ++ "_pos"
  else
    match rel with
    | "<" => s ++ "_lt" | ">" => s ++ "_gt" | "≤" => s ++ "_le" | "≥" => s ++ "_ge"
    | _ => s ++ "_mem"

def pp (e : Expr) : MetaM String := do
  return toString (← ppExpr (← instantiateMVars e))

/-- `x rel e` for a hypothesis about the variable x, as `Fix` takes it. -/
def relation? (x : FVarId) (t : Expr) : MetaM (Option (String × Expr)) := do
  let t ← instantiateMVars t
  let args := t.getAppArgs
  let some c := t.getAppFn.constName? | return none
  let rel? : Option String := match c with
    | ``GT.gt => some ">" | ``LT.lt => some "<" | ``GE.ge => some "≥" | ``LE.le => some "≤"
    | _ => none
  match rel? with
  | some rel =>
    if args.size == 4 && args[2]! == .fvar x then return some (rel, args[3]!) else return none
  | none =>
    if c == ``Membership.mem && args.size == 5 && args[4]! == .fvar x then
      return some ("∈", args[3]!)
    return none

/-- A term as Verbose's `maybeApplied` ("hf applied to ε using ε_pos"): the
function and its arguments as the source writes them, an argument that is a
proof after "using", the others after "applied to".  The elaborated term tells
which are proofs: its last explicit arguments are those of the source. -/
def maybeApplied (stx : Syntax) (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  let shown (s : Syntax) : String :=
    let s := if s.isOfKind ``Lean.Parser.Term.paren then s[1] else s
    s.prettyPrint.pretty.trim
  unless stx.isOfKind ``Lean.Parser.Term.app do return shown stx
  let argStx := stx[1].getArgs
  let explicitPos ← forallTelescopeReducing (← inferType e.getAppFn) fun xs _ => xs.mapM fun x => do
    return (← x.fvarId!.getBinderInfo).isExplicit
  let args := e.getAppArgs
  let explicitArgs := (List.range args.size).filter (explicitPos.getD · true) |>.map (args[·]!)
  let tail := explicitArgs.drop (explicitArgs.length - argStx.size)
  let mut objs := #[]
  let mut prfs := #[]
  for (s, arg) in argStx.toList.zip tail do
    if ← isProof arg then prfs := prfs.push (shown s) else objs := objs.push (shown s)
  let appliedTxt := if objs.isEmpty then "" else " applied to " ++ " and ".intercalate objs.toList
  let usingTxt := if prfs.isEmpty then "" else " using " ++ " and ".intercalate prfs.toList
  return shown stx[0] ++ appliedTxt ++ usingTxt

/-- The locals of `after` that are not in `before`, in order. -/
def newLocals (before after : LocalContext) : Array LocalDecl :=
  after.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail || before.contains d.fvarId then acc else acc.push d

def typed (d : LocalDecl) : MetaM String := do
  return s!"({d.userName} : {← pp d.type})"

/-- "Fix ..." and "Assume ..." for the locals that an intro adds. -/
def introLines (ds : Array LocalDecl) : MetaM (Array String) := do
  let mut out := #[]
  let mut i := 0
  while i < ds.size do
    let d := ds[i]!
    if ← isProp d.type then
      out := out.push s!"Assume {← typed d}"
      i := i + 1
      continue
    -- an object followed by a condition on it, named as Fix names it
    if h : i + 1 < ds.size then
      let h := ds[i+1]
      if let some (rel, rhs) ← relation? d.fvarId h.type then
        let zero := (← pp rhs) == "0"
        if h.userName.toString == fixHypName d.userName rel zero then
          out := out.push s!"Fix {d.userName} {rel} {← pp rhs}"
          i := i + 2
          continue
    out := out.push s!"Fix {d.userName}"
    i := i + 1
  return out

/-- "we get δ such that (δ_pos : δ > 0) and (Hf : ...)" -/
def weGet (ds : Array LocalDecl) : MetaM String := do
  let objs ← ds.filterM fun d => return !(← isProp d.type)
  let hyps ← ds.filterM fun d => isProp d.type
  let hs ← hyps.mapM typed
  if objs.isEmpty then return " ".intercalate hs.toList
  let os := " and ".intercalate (objs.toList.map (·.userName.toString))
  return s!"{os} such that " ++ " and ".intercalate hs.toList

/-- The Verbose sentences of one tactic step, or none to keep the tactic as it is. -/
def stepLines (ci : ContextInfo) (ti : TacticInfo) : IO (Option (Array String)) := do
  let some gb := ti.goalsBefore.head? | return none
  let kind := ti.stx.getKind
  let some declB := ti.mctxBefore.findDecl? gb | return none
  let run {α} (lctx : LocalContext) (mctx : MetavarContext) (x : MetaM α) : IO α :=
    ({ ci with mctx } : ContextInfo).runMetaM lctx x
  -- the goal after the step that continues the same goal (the first one)
  let after? := ti.goalsAfter.head?.bind (ti.mctxAfter.findDecl? ·)
  if kind == ``Lean.Parser.Tactic.intro then
    let some declA := after? | return none
    let ds := newLocals declB.lctx declA.lctx
    return some (← run declA.lctx ti.mctxAfter (introLines ds))
  if kind == ``Lean.Parser.Tactic.rcases || kind == ``Lean.Parser.Tactic.obtain then
    let some declA := after? | return none
    let ds := newLocals declB.lctx declA.lctx
    -- the term destructed: rcases e with ..., obtain ... := e
    let termStx : Syntax :=
      if kind == ``Lean.Parser.Tactic.rcases then ti.stx[1][0][1] else ti.stx[3][1][0]
    let line ← run declB.lctx ti.mctxBefore do
      let e ← (Term.elabTerm termStx none).run'
      let e ← instantiateMVars e
      return s!"By {← maybeApplied termStx e} we get "
    let got ← run declA.lctx ti.mctxAfter (weGet ds)
    return some #[line ++ got]
  if kind == ``Mathlib.Tactic.useSyntax then
    let t := ti.stx[3][0]
    return some #[s!"Let's prove that {t.prettyPrint.pretty.trim} works"]
  if kind == ``Lean.Parser.Tactic.exact then
    let line ← run declB.lctx ti.mctxAfter do
      let e ← instantiateMVars (.mvar gb)
      return s!"We conclude by {← maybeApplied ti.stx[1] e}"
    return some #[line]
  return none

/-- The tactic steps of a tactic block, in order: the tactics of its sequences. -/
partial def steps (t : InfoTree) (ci? : Option ContextInfo := none) :
    Array (ContextInfo × TacticInfo) :=
  match t with
  | .context ctx t => steps t (ctx.mergeIntoOuter? ci?)
  | .node (.ofTacticInfo ti) children =>
    let here : Array (ContextInfo × TacticInfo) :=
      match ci? with
      | some ci =>
        let k := ti.stx.getKind
        if [``Lean.Parser.Tactic.intro, ``Lean.Parser.Tactic.rcases, ``Lean.Parser.Tactic.obtain,
            ``Mathlib.Tactic.useSyntax, ``Lean.Parser.Tactic.exact].contains k
           || (ti.stx.isOfKind ``Lean.Parser.Tactic.tacticSeq1Indented == false && false)
        then #[(ci, ti)] else #[]
      | none => #[]
    -- the steps inside an intro or exact are not steps of the proof
    if here.isEmpty then children.foldl (fun acc c => acc ++ steps c ci?) #[] else here
  | .node _ children => children.foldl (fun acc c => acc ++ steps c ci?) #[]
  | .hole _ => #[]

/-- The tactics of the proof as they are written, for the steps not translated. -/
partial def tacticsOf (stx : Syntax) : Array Syntax :=
  if stx.isOfKind ``Lean.Parser.Tactic.tacticSeq1Indented then
    stx[0].getSepArgs
  else
    stx.getArgs.foldl (fun acc s => acc ++ tacticsOf s) #[]

syntax (name := verbalize) "#verbalize " str ppLine command : command

@[command_elab verbalize] def elabVerbalize : CommandElab := fun stx => do
  let title := stx[1]
  let cmd := stx[2]
  let before := (← getInfoState).trees.size
  -- the proof elaborated at once (not in a task of its own), so that its info trees are here
  withScope (fun sc => { sc with opts := sc.opts.setBool `Elab.async false }) do
    withEnableInfoTree true (elabCommand cmd)
  let trees := (← getInfoState).trees.toArray.extract before (← getInfoState).trees.size
  -- inside the command, its trees are not yet in the command's context
  let ci0 : ContextInfo := {
    env := (← getEnv), fileMap := (← getFileMap), mctx := {}, options := (← getOptions),
    currNamespace := (← getCurrNamespace), openDecls := (← getOpenDecls), ngen := (← getThe Command.State).ngen }
  let allSteps := trees.foldl (fun acc t => acc ++ steps t (some ci0)) #[]
  -- the statement: the theorem just declared
  let declId := cmd[1][1]
  let name := (← getCurrNamespace) ++ declId[0].getId
  let env ← getEnv
  let some ci := env.find? name | throwError "#verbalize: {name} not declared"
  let header ← liftTermElabM do
    forallTelescope ci.type fun xs concl => do
      let mut given := #[]
      let mut assume := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        let s := s!"({d.userName} : {← pp d.type})"
        if ← isProp d.type then assume := assume.push s else given := given.push s
      return s!"  Given: {" ".intercalate given.toList}\n  Assume: {" ".intercalate assume.toList}\n  Conclusion: {← pp concl}"
  -- one line or more per tactic of the proof, in the order of the source
  let tactics := tacticsOf cmd
  let mut lines := #[]
  for tac in tactics do
    let pos? := tac.getPos?
    match allSteps.find? (fun (_, ti) => ti.stx.getPos? == pos? && pos?.isSome) with
    | some (ci, ti) =>
      match ← stepLines ci ti with
      | some ls => lines := lines ++ ls
      | none => lines := lines.push tac.prettyPrint.pretty.trim
    | none => lines := lines.push tac.prettyPrint.pretty.trim
  let body := "\n".intercalate (lines.toList.map ("  " ++ ·))
  -- the proofs name their hypotheses ("Assume h : P"), as Verbose.Named lets them
  logInfo m!"open Verbose.Named in\nExample {title}\n{header}\nProof:\n{body}\nQED"

end VerboseGen
