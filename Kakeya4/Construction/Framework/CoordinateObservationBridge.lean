import Kakeya4.Construction.Framework.ObservedCoordinates
import Kakeya4.Construction.Framework.CoordinateSemialgebraicPrior

/-!
# Standard-coordinate prior certificates at the observation-law consumer

This module combines the reverse-transport adapter for semialgebraic prior certificates with
the already proved observation pushforward formula. A caller can provide the exact pushed-prior
certificates in the canonical `Fin 5` or `Fin 8` coordinates and obtain the world-tagged
observation density directly. No density is inferred from the prior type alone.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- Direct observation-law consumer for caller-certified semialgebraic densities in the
canonical standard coordinates. The per-world pushed-prior density equations, finite
semialgebraic partitions, and complexity bounds remain explicit inputs; the result is the actual
world-tagged law on `(world, time, spatial point, hidden bin)` relative to counting times
`dt dy` times hidden-bin counting measure. -/
theorem worldTaggedObservationBaseBinLaw_eq_withDensity_of_standardSemialgebraic
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (pieceBound variableBound atomBound degreeBound : ℕ) (densityBound : ℝ≥0∞)
    (C : ∀ γ : Fin I.priors.worldCount,
      SemialgebraicPiecewiseDensityCertificate
        (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ))
        ((I.priors.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
        pieceBound variableBound atomBound degreeBound densityBound) :
    worldTaggedObservationBaseBinLaw I seq depth n worldData =
      ((Measure.count : Measure (Fin I.priors.worldCount)).prod
        ((observedBaseReference v).prod (Measure.count : Measure (HiddenBin v)))).withDensity
        (fun p => (I.priors.weight p.1 : ℝ≥0∞) *
          observedCoordinateHiddenBinSliceDensity v (unobservedFiberReference v)
            (selectedObservedCoordinateDensity I
              (trajectoryPriorDensityCertificates_of_standardSemialgebraic v I.priors
                pieceBound variableBound atomBound degreeBound densityBound C) p.1)
            (dyadicRoundedWidth
              (seq.depthScale depth n / worldDerivativeScale v (worldData p.1))) p.2) := by
  exact worldTaggedObservationBaseBinLaw_eq_withDensity I
    (trajectoryPriorDensityCertificates_of_standardSemialgebraic v I.priors
      pieceBound variableBound atomBound degreeBound densityBound C)
    seq depth n worldData

end Kakeya4.Framework
