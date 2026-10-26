import Kakeya4.Hard.MultiplicativeConvolution.SmoothingSetTransport

/-! # Outer-mass transport from the original law through actual extraction and smoothing -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Every original set loses at most the mass discarded by the restriction, without measurability of E. -/
theorem measure_le_restriction_add_compl (μ : Measure ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) (E : Set ℝ) : μ E ≤ (μ.restrict A) E + μ Aᶜ := by
  calc
    _ ≤ μ ((E ∩ A) ∪ Aᶜ) := measure_mono (by
      intro x hx
      by_cases h : x ∈ A
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr h)
    _ ≤ μ (E ∩ A)+μ Aᶜ := measure_union_le _ _
    _ = _ := by rw [Measure.restrict_apply' hA]

/-- Normalizing a restriction of a probability does not decrease any outer mass. -/
theorem restriction_le_normalizedRestriction (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (A E : Set ℝ) : (μ.restrict A) E ≤ normalizedRestriction μ A E := by
  have hm : μ A ≤ 1 := (measure_mono (subset_univ A)).trans_eq (measure_univ : μ univ = 1)
  have hi : (1:ℝ≥0∞) ≤ (μ A)⁻¹ := by simpa only [inv_one] using ENNReal.inv_le_inv.mpr hm
  rw [normalizedRestriction, Measure.smul_apply, smul_eq_mul]
  simpa only [one_mul] using mul_le_mul_left hi ((μ.restrict A) E)

/-- Actual extraction and smoothing transport any original outer mass with only the proved discarded loss. -/
theorem original_mass_le_smoothed_thickening_add_loss (κ : SmoothKernel)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) (hA0 : μ A ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (E : Set ℝ) :
    μ E ≤ unitRescaledSmoothLaw κ r (normalizedRestriction μ A)
      (cthickening (r/2) ((fun x : ℝ ↦ x/2) '' E)) + μ Aᶜ := by
  letI : IsProbabilityMeasure (normalizedRestriction μ A) := isProbabilityMeasure_normalizedRestriction μ A hA0
  exact (measure_le_restriction_add_compl μ hA E).trans
    (add_le_add_left ((restriction_le_normalizedRestriction μ A E).trans
      (unitRescaledSmoothLaw_thickening_mass κ (normalizedRestriction μ A) hr E)) _)

end Kakeya4.Hard.MultiplicativeConvolution
