import NavierStokes
import Euler
open Lean

/-! For each Lean name of a file (one per line), the module that declares it:
`lake env lean --run checks/Origins.lean <file> <Module> ...` prints name, tab,
module, tab, kind (theorem or constant), with the given modules imported besides NavierStokes and Euler. -/

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let mods := [`NavierStokes, `Euler] ++ args.tail.map String.toName
  let env ← importModules (mods.map fun m => { module := m }).toArray {} (loadExts := true)
  for line in (← IO.FS.lines args.head!) do
    if line.isEmpty then continue
    let n := line.toName
    -- and whether it is a theorem (a proof, which the counts leave out)
    let kind := match env.find? n with
      | some (.thmInfo _) => "theorem"
      | some _ => "constant"
      | none => "?"
    match env.getModuleIdxFor? n with
    | some i => IO.println s!"{line}\t{env.header.moduleNames[i.toNat]!}\t{kind}"
    | none => IO.println s!"{line}\t{if env.contains n then "(this module)" else "(not found)"}\t{kind}"
