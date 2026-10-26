import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Basic.NNReal.Basic
import Kakeya4.Construction.Framework.Trajectory

/-!
# World priors and unnormalized incidence measures

This is the measure-theoretic layer of §2's exact problem, kept independent of the pending
fixed-sequence subpower interface. A finite world prior is a probability mixture of trajectory
laws; each world then uses the same Lebesgue time law on `[0,1]`, and selecting incidences is
implemented by restricting the product measure without renormalizing it.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace Kakeya4.Framework

/-- Lebesgue measure on the unit time interval, viewed as a measure on `ℝ`. -/
noncomputable def unitTimeMeasure : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

theorem unitTimeMeasure_isProbability : IsProbabilityMeasure unitTimeMeasure := by
  constructor
  simp [unitTimeMeasure, Measure.restrict_apply, Real.volume_Icc]

/-- A finite mixture of world weights and trajectory probability laws. -/
structure WorldPriorSystem (α : Type*) [MeasurableSpace α] where
  worldCount : ℕ
  weight : Fin worldCount → ℝ≥0
  weight_sum : ∑ γ, weight γ = 1
  prior : Fin worldCount → Measure α
  prior_isProbability : ∀ γ, IsProbabilityMeasure (prior γ)

namespace WorldPriorSystem

variable {α : Type*} [MeasurableSpace α] (P : WorldPriorSystem α)

/-- The law of trajectory and time before selecting incidences. Time is independent of the
trajectory because this is the product of the world prior and the fixed unit-time measure. -/
noncomputable def productIncidenceMeasure (γ : Fin P.worldCount) : Measure (α × ℝ) :=
  (P.prior γ).prod unitTimeMeasure

/-- Restrict the product law to the selected incidences. This measure is deliberately not
normalized after the restriction. -/
noncomputable def selectedIncidenceMeasure
    (event : Fin P.worldCount → Set (α × ℝ)) (γ : Fin P.worldCount) : Measure (α × ℝ) :=
  (P.productIncidenceMeasure γ).restrict (event γ)

/-- Total weighted mass of a finite family of measurable incidence selections. -/
noncomputable def weightedIncidenceMass
    (event : Fin P.worldCount → Set (α × ℝ)) : ℝ≥0∞ :=
  ∑ γ, (P.weight γ : ℝ≥0∞) * P.selectedIncidenceMeasure event γ Set.univ

theorem selectedIncidenceMeasure_univ_le_one
    (event : Fin P.worldCount → Set (α × ℝ)) (γ : Fin P.worldCount) :
    P.selectedIncidenceMeasure event γ Set.univ ≤ 1 := by
  letI : IsProbabilityMeasure (P.prior γ) := P.prior_isProbability γ
  letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
  calc
    P.selectedIncidenceMeasure event γ Set.univ =
        P.productIncidenceMeasure γ (event γ) := by
          simp [selectedIncidenceMeasure, productIncidenceMeasure]
    _ ≤ P.productIncidenceMeasure γ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := by
          change ((P.prior γ).prod unitTimeMeasure) Set.univ = 1
          exact measure_univ

theorem weightedIncidenceMass_le_one
    (event : Fin P.worldCount → Set (α × ℝ)) :
    P.weightedIncidenceMass event ≤ 1 := by
  calc
    P.weightedIncidenceMass event ≤
        ∑ γ, (P.weight γ : ℝ≥0∞) * 1 := by
          apply Finset.sum_le_sum
          intro γ hγ
          exact mul_le_mul_of_nonneg_left
            (P.selectedIncidenceMeasure_univ_le_one event γ) (by positivity)
    _ = ((∑ γ, P.weight γ : ℝ≥0) : ℝ≥0∞) := by
          simpa only [weightedIncidenceMass, mul_one] using
            (ENNReal.ofNNReal_finsetSum Finset.univ P.weight).symm
    _ = 1 := by
          rw [P.weight_sum]
          norm_num

end WorldPriorSystem

/-- A well-formed incidence selection over a version-indexed trajectory space. -/
structure IncidenceSelection (v : ModelVersion) [MeasurableSpace (Trajectory v)] where
  priors : WorldPriorSystem (Trajectory v)
  event : Fin priors.worldCount → Set (Trajectory v × ℝ)
  event_measurable : ∀ γ, MeasurableSet (event γ)

namespace IncidenceSelection

variable {v : ModelVersion} [MeasurableSpace (Trajectory v)] (I : IncidenceSelection v)

/-- The world-indexed measures appearing in the manuscript's incidence law. -/
noncomputable def measure (γ : Fin I.priors.worldCount) : Measure (Trajectory v × ℝ) :=
  I.priors.selectedIncidenceMeasure I.event γ

/-- The manuscript's weighted incidence mass, with no conditional normalization. -/
noncomputable def totalMass : ℝ≥0∞ := I.priors.weightedIncidenceMass I.event

theorem totalMass_le_one : I.totalMass ≤ 1 :=
  I.priors.weightedIncidenceMass_le_one I.event

end IncidenceSelection

end Kakeya4.Framework
