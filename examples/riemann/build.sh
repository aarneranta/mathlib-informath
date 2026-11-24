#!/bin/sh
# Informalize the modules of riemann-hypothesis-original listed in MODULES:
# export (Lean), symbol tables, readings (Informath), pages.
# Needs ../../../riemann-hypothesis-original ($RIEMANN) with Mathlib's compiled
# files (lake exe mathlib/cache get) and those of the modules read here
# (./build.sh fetch, or scripts/fetch-cache.py), and Informath in
# $INFORMATH_ROOT (default: ../informath beside mathlib-informath).
set -e
cd "$(dirname "$0")"
# the claims (Challenge), the step from them to the proof's own statement,
# the hypotheses of the proof's last step, and the modules that declare the
# notions these use (without GlobalTwisting.APerTw and .DRS, which the
# exporter does not finish)
MODULES="\
 Challenge \
 Development.AutomorphicArithmetic.CharacterBoxes.HalfPlane \
 Formalism.GammaFactorNonvanishing.RhOfRight \
 Formalism.GammaFactorNonvanishing.CritLine \
 Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter \
 Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN \
 Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis \
 Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec \
 Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecT \
 Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow \
 Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd \
 Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter \
 Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace \
 Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff \
 Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff \
 Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff \
 Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace \
 Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable \
 Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne \
 Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound \
 Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum \
 Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands \
 Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne \
 Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd \
 Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff \
 Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic \
 Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors \
 Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff \
 Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL \
 Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia \
 Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal \
 Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters \
 Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient \
 Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible \
 Development.AutomorphicArithmetic.CharacterBoxes.Supply \
 Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG \
 Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj \
 Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjAlt \
 Formalism.ConjugateSelfDual.Statement \
 Formalism.GaloisCohomology.Statement \
 Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied \
 Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf \
 Formalism.SharpRestriction.GlobalTheoremInputs \
 Formalism.SharpRestriction.LevelLetterCocycles.DataN \
 Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc \
 Formalism.SharpRestriction.ParamsHeightRankConstant \
 Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions \
 Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition \
 ReciprocityTheory.GaloisValuations.Global"
export RIEMANN="${RIEMANN:-$(cd ../.. && pwd)/../riemann-hypothesis-original}"
[ -d "$RIEMANN/src/Development" ] || { echo "no riemann-hypothesis-original in $RIEMANN"; exit 1; }
if [ "$1" = fetch ]; then python3 scripts/fetch-cache.py "$RIEMANN" $MODULES; fi
# the exporter reads the sources (for the definientia) from $MATHLIB
export MATHLIB="$RIEMANN/src"
# as in ../navier-stokes: the names table is made from a first export, and the
# modules are exported again with it (one process: the imports, about 8 GB,
# are loaded once; scripts/export-each.sh exports each module in its own
# process with a time limit, to find a module that the exporter does not finish)
export ENTRY_TABLES="../../../mathlib.dkgf:../../../structures.dkgf:../riemann-names.dkgf:../riemann.dkgf"
(cd exporter && lake build export && lake exe export $MODULES)
python3 scripts/name-table.py
(cd exporter && lake exe export $MODULES)
python3 scripts/read-modules.py work/index.json $MODULES
python3 scripts/build-pages.py work/index.json
python3 scripts/constants-table.py
