import Kakeya4.Construction.Framework.WorldTemperedObservationBridge
import Kakeya4.Construction.Framework.ObservedCoordinates

/-!
# Spatial marginal mass conservation for scale-indexed world-tempered priors

The existing observation-coordinate API integrates hidden bins, coefficient fibers, and time,
then pushes the selected law to spatial volume. This module transports a world-tempered
certificate family through that API and records the resulting unnormalized mass identity at
each scale.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- Turn each scale's shared-envelope coordinate certificates into the trajectory certificates
required by the observation marginal formulas. -/
noncomputable def WorldTemperedSemialgebraicPriorFamily.trajectoryDensityCertificates
    {v : ModelVersion}
    (I : ℕ → @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence)
    (pieceBound atomBound : ∀ n, Fin ((I n).priors.worldCount) → ℕ)
    (densityBound : ∀ n, Fin ((I n).priors.worldCount) → ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).priors.worldCount)
      (fun _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ => ((I n).priors.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) : TrajectoryPriorDensityCertificates v (I n).priors :=
  trajectoryPriorDensityCertificates_of_standardSemialgebraic v (I n).priors
    (C.pieceEnvelope n) variableBound (C.atomEnvelope n) degreeBound
    (C.densityEnvelope n)
    (fun γ => C.standardCoordinateCertificate I seq pieceBound atomBound densityBound
      variableBound degreeBound n γ)

/-- At every scale and for every world, the explicit spatial density integrates to the actual
unnormalized mass of that world's selected incidence event. The hidden-bin sum, fiber integral,
time integral, chart transport, and spatial pushforward are discharged by the existing marginal
theorems. -/
theorem worldTemperedSpatialDensity_lintegral_eq_measure_univ
    {v : ModelVersion}
    (I : ℕ → @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ∀ n, Fin ((I n).priors.worldCount) → VersionWorldData v)
    (pieceBound atomBound : ∀ n, Fin ((I n).priors.worldCount) → ℕ)
    (densityBound : ∀ n, Fin ((I n).priors.worldCount) → ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).priors.worldCount)
      (fun _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ => ((I n).priors.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) (γ : Fin ((I n).priors.worldCount)) :
    ∫⁻ y, selectedObservationSpatialDensity (I n)
      (C.trajectoryDensityCertificates I seq pieceBound atomBound densityBound
        variableBound degreeBound n) γ y ∂observedSpatialReference v =
      (I n).measure γ Set.univ := by
  exact (I n).selectedObservationSpatialDensity_lintegral_eq_measure_univ
    (C.trajectoryDensityCertificates I seq pieceBound atomBound densityBound
      variableBound degreeBound n) seq depth n (worldData n) γ

/-- Summing the spatial density integrals with the original world weights recovers the selected
incidence mass at every scale. No conditional renormalization is performed. -/
theorem worldTemperedWeightedSpatialDensityIntegral_eq_totalMass
    {v : ModelVersion}
    (I : ℕ → @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ∀ n, Fin ((I n).priors.worldCount) → VersionWorldData v)
    (pieceBound atomBound : ∀ n, Fin ((I n).priors.worldCount) → ℕ)
    (densityBound : ∀ n, Fin ((I n).priors.worldCount) → ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).priors.worldCount)
      (fun _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ => ((I n).priors.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) :
    (∑ γ : Fin ((I n).priors.worldCount),
      ((I n).priors.weight γ : ℝ≥0∞) *
        ∫⁻ y, selectedObservationSpatialDensity (I n)
          (C.trajectoryDensityCertificates I seq pieceBound atomBound densityBound
            variableBound degreeBound n) γ y ∂observedSpatialReference v) =
      (I n).totalMass := by
  exact (I n).weightedObservationSpatialDensityIntegral_eq_totalMass
    (C.trajectoryDensityCertificates I seq pieceBound atomBound densityBound
      variableBound degreeBound n) seq depth n (worldData n)

/-- Exact world-tagged spatial density at every scale. The reference is counting measure on the
actual world tags times observed spatial volume; original world weights and event restrictions
remain in the density. Its spatial density already integrates over the selected coefficient
fiber and observation time. -/
theorem worldTemperedWorldTaggedSpatialLaw_eq_withDensity
    {v : ModelVersion}
    (I : ℕ → @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ∀ n, Fin ((I n).priors.worldCount) → VersionWorldData v)
    (pieceBound atomBound : ∀ n, Fin ((I n).priors.worldCount) → ℕ)
    (densityBound : ∀ n, Fin ((I n).priors.worldCount) → ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).priors.worldCount)
      (fun _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ => ((I n).priors.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) :
    worldTaggedObservationSpatialLaw (I n) seq depth n (worldData n) =
      ((Measure.count : Measure (Fin ((I n).priors.worldCount))).prod
        (observedSpatialReference v)).withDensity
        (fun p => ((I n).priors.weight p.1 : ℝ≥0∞) *
          selectedObservationSpatialDensity (I n)
            (C.trajectoryDensityCertificates I seq pieceBound atomBound densityBound
              variableBound degreeBound n) p.1 p.2) := by
  exact (I n).worldTaggedObservationSpatialLaw_eq_withDensity
    (C.trajectoryDensityCertificates I seq pieceBound atomBound densityBound
      variableBound degreeBound n) seq depth n (worldData n)

end Kakeya4.Framework
