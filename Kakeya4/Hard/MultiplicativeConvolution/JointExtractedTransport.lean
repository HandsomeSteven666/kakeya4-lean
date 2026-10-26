import Kakeya4.Hard.MultiplicativeConvolution.ProductSmoothingCoupling

/-! # Joint original outer mass through the actual independent extraction/noise law -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Every finite-dimensional original outer mass is transported with the exact summed marginal loss. -/
theorem original_pi_mass_le_smoothed_add_loss {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (hA0 : ∀ i, μ i (A i) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (E : Set (ι → ℝ)) :
    Measure.pi μ E ≤ Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)))
      (cthickening (r/2) ((fun x i ↦ x i/2) '' E)) + ∑ i, μ i (A i)ᶜ := by
  letI (i : ι) : IsProbabilityMeasure (normalizedRestriction (μ i) (A i)) :=
    isProbabilityMeasure_normalizedRestriction (μ i) (A i) (hA0 i)
  exact (original_pi_mass_le_normalized_add_loss μ A hA hA0 E).trans
    (add_le_add_left (pi_smoothed_thickening_mass κ (fun i ↦ normalizedRestriction (μ i) (A i)) hr E) _)

/-- A uniform actual marginal loss costs exactly the number of coordinates in the joint estimate. -/
theorem original_pi_mass_le_smoothed_add_card_loss {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (hA0 : ∀ i, μ i (A i) ≠ 0)
    {r ε : ℝ} (hr : 0 ≤ r) (hloss : ∀ i, μ i (A i)ᶜ ≤ ENNReal.ofReal (r^ε))
    (E : Set (ι → ℝ)) :
    Measure.pi μ E ≤ Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)))
      (cthickening (r/2) ((fun x i ↦ x i/2) '' E)) +
        (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (r^ε) := by
  apply (original_pi_mass_le_smoothed_add_loss κ μ A hA hA0 hr E).trans
  apply add_le_add_right
  calc
    _ ≤ ∑ _ : ι, ENNReal.ofReal (r^ε) := Finset.sum_le_sum (fun i _ ↦ hloss i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The original four-parameter mass loses at most 4*r^epsilon under the actual extracted law. -/
theorem original_four_parameter_mass_le_smoothed (κ : SmoothKernel)
    (μ : Fin 4 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Fin 4 → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (hA0 : ∀ i, μ i (A i) ≠ 0)
    {r ε : ℝ} (hr : 0 ≤ r) (hloss : ∀ i, μ i (A i)ᶜ ≤ ENNReal.ofReal (r^ε))
    (E : Set (Fin 4 → ℝ)) :
    Measure.pi μ E ≤ Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)))
      (cthickening (r/2) ((fun x i ↦ x i/2) '' E)) + 4 * ENNReal.ofReal (r^ε) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    original_pi_mass_le_smoothed_add_card_loss κ μ A hA hA0 hr hloss E

end Kakeya4.Hard.MultiplicativeConvolution
