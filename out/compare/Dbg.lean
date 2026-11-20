import Mathlib
open Lean Meta Elab Command in
#eval show CommandElabM Unit from do
  liftTermElabM do
    let ci ← getConstInfo ``Set.mem_inter
    forallTelescope ci.type fun _ b => do
      logInfo m!"{b}"
      let some (_, _, s) := b.app2? ``Membership.mem | logInfo "no"
      logInfo m!"fn {s.getAppFn} args {s.getAppNumArgs} a0 {s.getAppArgs[0]!} head {s.getAppArgs[0]!.getAppFn.constName?}"
