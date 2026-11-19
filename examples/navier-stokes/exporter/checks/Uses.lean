import NavierStokes.ComparatorSolution
open Lean Meta

/-- The constants that the value of `root` uses, transitively (types and values). -/
partial def usedBy (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.type.getUsedConstants do todo := todo.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do todo := todo.push c
  return seen

#eval show MetaM Unit from do
  let env ← getEnv
  let s := usedBy env `NavierStokes.Comparator.navier_stokes_breakdown_R3
  let t := usedBy env `NavierStokes.Comparator.navier_stokes_breakdown_periodic
  IO.println s!"R3 uses {s.size} constants, periodic {t.size}"
  for n in [`NavierStokes.SmoothFamilyTorusInverse.inverse_finiteJets,
            `NavierStokes.SmoothFamilyTorusInverse.norm_derivativeWord_inverse_le,
            `NavierStokes.SmoothFamilyTorusInverse.mixedJet_inverse_bound,
            `NavierStokes.ParametricTorusInverse.mixedJet_inverse_bound,
            `NavierStokes.SmoothFourierData.coefficient_seminorm_bound,
            `NavierStokesR3.PressureFlux.exists_uniform_actual_pressure_flux_bound] do
    IO.println s!"{n}: R3 {s.contains n}, periodic {t.contains n}"
