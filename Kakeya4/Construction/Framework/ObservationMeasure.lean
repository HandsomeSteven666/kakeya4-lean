import Kakeya4.Construction.Framework.IncidenceMeasure
import Kakeya4.Construction.Framework.Observation

/-!
# Pushforward laws of observations

This file records the actual observed law as the pushforward of the selected, unnormalized
trajectory-time measure. It does not assert absolute continuity with respect to `dt dy ×
counting`; that conclusion needs the coefficient-density clause of the manuscript's tempered
data and is handled separately.
-/

set_option autoImplicit false

namespace Kakeya4.Framework

open MeasureTheory
open scoped ENNReal

variable {v : ModelVersion}

/-- The world-`γ` law of the observation payload, retaining the original selected mass. -/
noncomputable def observationPushforward
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) : Measure (ObservationData v I.priors.worldCount) :=
  (I.measure γ).map
    (fun p : Trajectory v × ℝ =>
      observationAt v seq depth n worldData γ p.1 p.2)

theorem observationPushforward_univ
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) :
    observationPushforward I seq depth n worldData γ Set.univ = I.measure γ Set.univ := by
  let : MeasurableSpace (Fin I.priors.worldCount) := ⊤
  change ((I.measure γ).map
    (fun p : Trajectory v × ℝ => observationAt v seq depth n worldData γ p.1 p.2))
      Set.univ = I.measure γ Set.univ
  rw [@Measure.map_apply (Trajectory v × ℝ) (ObservationData v I.priors.worldCount)
    (inferInstance : MeasurableSpace (Trajectory v × ℝ))
    (instMeasurableSpaceObservationData v I.priors.worldCount)
    (I.measure γ) (fun p => observationAt v seq depth n worldData γ p.1 p.2)
    (observationAt_measurable v seq depth n worldData γ) Set.univ MeasurableSet.univ]
  simp

/-- The weighted mass of the worldwise pushforward laws is exactly the selected incidence mass.
No conditioning or renormalization is introduced by observing the incidences. -/
theorem weightedObservationPushforwardMass_eq
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    (∑ γ : Fin I.priors.worldCount, (I.priors.weight γ : ℝ≥0∞) *
      observationPushforward I seq depth n worldData γ Set.univ) = I.totalMass := by
  simp only [observationPushforward_univ]
  rfl

/-- On every measurable observation event, the weighted observed mass is the weighted
incidence mass of its exact pullback. This is the setwise identity that underlies any later
observation-density or fiber-Jacobian calculation; it makes no absolute-continuity claim. -/
theorem weightedObservationPushforward_apply
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (s : Set (ObservationData v I.priors.worldCount))
    (hs : MeasurableSet s) :
    (∑ γ : Fin I.priors.worldCount, (I.priors.weight γ : ℝ≥0∞) *
      observationPushforward I seq depth n worldData γ s) =
    ∑ γ : Fin I.priors.worldCount, (I.priors.weight γ : ℝ≥0∞) *
      I.measure γ ((fun p : Trajectory v × ℝ =>
        observationAt v seq depth n worldData γ p.1 p.2) ⁻¹' s) := by
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [observationPushforward,
    @Measure.map_apply (Trajectory v × ℝ) (ObservationData v I.priors.worldCount)
      (inferInstance : MeasurableSpace (Trajectory v × ℝ))
      (instMeasurableSpaceObservationData v I.priors.worldCount)
      (I.measure γ) (fun p => observationAt v seq depth n worldData γ p.1 p.2)
      (observationAt_measurable v seq depth n worldData γ) s hs]

end Kakeya4.Framework
