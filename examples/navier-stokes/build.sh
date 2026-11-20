#!/bin/sh
# Informalize the modules of NavierStokesAndEuler listed in MODULES:
# export (Lean), symbol tables, readings (Informath), pages.
# Needs ../../../NavierStokesAndEuler built (lake exe cache get; lake build)
# and Informath in $INFORMATH_ROOT (default: ../informath beside mathlib-informath).
set -e
cd "$(dirname "$0")"
MODULES="NavierStokes.ComparatorDefinitions NavierStokes.ComparatorSolution
 Euler.SolutionDefinitions Euler.Solution
 NavierStokes.SmoothFamilyTorusInverse NavierStokes.ParametricTorusInverse
 NavierStokes.SmoothFourierData NavierStokes.TorusInverse
 NavierStokes.R3.PressureFlux NavierStokes.R3.PressureFluxTest
 NavierStokes.R3.RieszTestOperators NavierStokes.R3.RieszL2Bounds
 NavierStokes.R3.SmoothSobolevL6 NavierStokes.R3.ComparisonSetup
 NavierStokes.R3.ComparisonCutoffs"
# the exporter reads the sources (for the definientia) from $MATHLIB
export MATHLIB="${NAVIER_STOKES:-$(cd ../.. && pwd)/../NavierStokesAndEuler}"
[ -d "$MATHLIB/NavierStokes" ] || { echo "no NavierStokesAndEuler in $MATHLIB"; exit 1; }
# the exporter is mathlib-informath's Export.lean; it reads the hand-written
# tables and the generated names table for the argument counts of the entries
# (partial applications as c__part<m>, image(f, ·)): the names table is made
# from a first export, and the modules are exported again with it
export ENTRY_TABLES="../../../mathlib.dkgf:../../../structures.dkgf:../navier-stokes-names.dkgf:../navier-stokes.dkgf"
(cd exporter && lake build export && lake exe export $MODULES)
python3 scripts/name-table.py
(cd exporter && lake exe export $MODULES)
python3 scripts/read-modules.py work/index.json $MODULES
python3 scripts/build-pages.py work/index.json
python3 scripts/build-comparison.py work/index.json
python3 scripts/constants-table.py
# the constants of Lemma 8.6: the Lean statements the article compares with it,
# and the definitions they rest on
python3 scripts/constants-table.py --out constants-lemma86.tsv --roots NavierStokes.SmoothFamilyTorusInverse.inverse_finiteJets,NavierStokes.SmoothFamilyTorusInverse.norm_derivativeWord_inverse_le,NavierStokes.SmoothFamilyTorusInverse.mixedJet_inverse_bound,NavierStokes.ParametricTorusInverse.mixedJet_inverse_bound
# the same as a symbol table to edit, with mock-ups for the missing entries
python3 scripts/dkgf-subtable.py constants-lemma86.tsv lemma86.dkgf
