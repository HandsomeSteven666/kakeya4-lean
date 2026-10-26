import Kakeya4.Hard.MultiplicativeConvolution.ProductLaw

/-! The actual law of a sum of independently sampled products, as in
manuscript re:generated-coefficient. The interval flatness estimate is separate.
Reuse: fixed Mathlib characteristic functions via ProductLaw.fourier_sumLaw. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Each outer coordinate is an independent sample from the same product law. -/
def generatedProductSumLaw {n : ℕ} (μ : Fin n → Measure ℝ) (k : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin k ↦ productLaw μ)).map (fun x : Fin k → ℝ ↦ ∑ i, x i)

instance generatedProductSumLaw_isProbabilityMeasure {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] (k : ℕ) :
    IsProbabilityMeasure (generatedProductSumLaw μ k) := by
  unfold generatedProductSumLaw
  exact MeasureTheory.Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance

/-- Independent sums give the exact k-th Fourier power, with the original convention. -/
theorem fourier_generatedProductSumLaw {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] (k : ℕ) (ξ : ℝ) :
    fourier (generatedProductSumLaw μ k) ξ = fourier (productLaw μ) ξ ^ k := by
  simpa [generatedProductSumLaw] using fourier_sumLaw (fun _ : Fin k ↦ productLaw μ) ξ

theorem norm_fourier_generatedProductSumLaw {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] (k : ℕ) (ξ : ℝ) :
    ‖fourier (generatedProductSumLaw μ k) ξ‖ = ‖fourier (productLaw μ) ξ‖ ^ k := by
  rw [fourier_generatedProductSumLaw, norm_pow]

#print axioms generatedProductSumLaw
#print axioms generatedProductSumLaw_isProbabilityMeasure
#print axioms fourier_generatedProductSumLaw
#print axioms norm_fourier_generatedProductSumLaw
end Kakeya4.Hard.MultiplicativeConvolution
