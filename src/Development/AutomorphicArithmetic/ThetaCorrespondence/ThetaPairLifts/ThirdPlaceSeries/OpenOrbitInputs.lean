import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible

namespace GlobalTheory.Fc.S0

/-- Precisely the premises directly consumed by the open-orbit proof.
Unlike the full 60-field literature bundle, this interface admits
the geometric lemma directly rather than demanding a particular
Bernstein-Zelevinsky/filtration derivation of it. -/
structure OpenOrbitInputs : Prop where
  casselmanWallach : GlobalTheory.Published.CasselmanWallach
  cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  doublingMethod : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  greenCuspidal : GlobalTheory.Published.GreenCuspidal
  greenRegularCharacters : GlobalTheory.Published.GreenRegularCharacters
  harishChandraAnalyticity : GlobalTheory.Published.HarishChandraAnalyticity
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt
  siegelWeilUnitaryConvergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  siegelWeilUnitaryConvergent2 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL
  weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  geometricLemma : GlobalTheory.Published.GeometricLemma

/-- Every original literature bundle supplies the weaker open-orbit interface. -/
theorem UnitaryGroupThirdPlaceHypotheses.toOpenOrbitInputs
    (P : UnitaryGroupThirdPlaceHypotheses) : OpenOrbitInputs where
  casselmanWallach := P.casselmanWallach
  cuspRapidDecay := P.cuspRapidDecay
  cuspTraceClass := P.cuspTraceClass
  discreteSeriesClassification := P.discreteSeriesClassification
  discreteSeriesCover := P.discreteSeriesCover
  discreteSeriesExists := P.discreteSeriesExists
  dixmierMalliavinFactorisation := P.dixmierMalliavinFactorisation
  doublingMethod := P.doublingMethod
  flathFactorisation := P.flathFactorisation
  greenCuspidal := P.greenCuspidal
  greenRegularCharacters := P.greenRegularCharacters
  harishChandraAnalyticity := P.harishChandraAnalyticity
  harishChandraFinite := P.harishChandraFinite
  harishChandraModules := P.harishChandraModules
  rayClassFieldSt := P.rayClassFieldSt
  siegelWeilUnitaryConvergent := P.siegelWeilUnitaryConvergent
  siegelWeilUnitaryConvergent2 := P.siegelWeilUnitaryConvergent2
  strongApproxSU := P.strongApproxSU
  unramifiedDoublingGL := P.unramifiedDoublingGL
  weilRepresentationUnitaryPair := P.weilRepresentationUnitaryPair
  weilSiegelFormulaUnitary := P.weilSiegelFormulaUnitary
  zelevinskyPolynomialRing := P.zelevinskyPolynomialRing
  geometricLemma := P.geometricLemma

end GlobalTheory.Fc.S0
