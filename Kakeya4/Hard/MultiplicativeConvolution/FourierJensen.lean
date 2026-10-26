import Kakeya4.Hard.MultiplicativeConvolution.ProductLaw
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# The unconditional Jensen step toward OSS Lemma 4.1

This is an actual probability-measure inequality, without any energy, support,
absolute-continuity or sum-product input. Convexity and Jensen are reused from
fixed Mathlib. Source: arXiv:2309.03068v2, Lemma 4.1.
-/

noncomputable section
open MeasureTheory Set

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Rescaled Fourier amplitudes are bounded integrable functions for finite laws. -/
theorem integrable_norm_fourier_rescale (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (ξ : ℝ) :
    Integrable (fun x ↦ ‖fourier ν (ξ * x)‖) μ := by
  apply Integrable.of_bound
    ((measurable_charFun.comp (by fun_prop)).norm.aestronglyMeasurable) 1
  filter_upwards [] with x
  simpa only [norm_norm, fourier, Function.comp_apply] using norm_fourier_le_one ν (ξ * x)

/-- Jensen's squared-amplitude bound for the binary multiplicative law. -/
theorem norm_fourier_mconv_sq_le (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ξ : ℝ) :
    ‖fourier (μ ∗ₘ ν) ξ‖ ^ 2 ≤ ∫ x, ‖fourier ν (ξ * x)‖ ^ 2 ∂μ := by
  let f : ℝ → ℝ := fun x ↦ ‖fourier ν (ξ * x)‖
  have hf : Integrable f μ := integrable_norm_fourier_rescale μ ν ξ
  have hf2 : Integrable (fun x ↦ f x ^ 2) μ := by
    apply Integrable.of_bound
      (((measurable_charFun.comp (by fun_prop)).norm.pow_const 2).aestronglyMeasurable) 1
    filter_upwards [] with x
    have h := norm_fourier_le_one ν (ξ * x)
    have h0 := norm_nonneg (fourier ν (ξ * x))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    dsimp [f, fourier] at *
    nlinarith
  have hj : (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ :=
    (even_two.convexOn_pow (𝕜 := ℝ)).map_integral_le
      (by fun_prop) isClosed_univ (Filter.Eventually.of_forall (fun _ ↦ mem_univ _)) hf hf2
  rw [fourier_multiplicativeConvolution]
  have hb := norm_integral_le_integral_norm (μ := μ) (fun x ↦ fourier ν (ξ * x))
  have h0 := norm_nonneg (∫ x, fourier ν (ξ * x) ∂μ)
  dsimp [f] at hj
  exact (pow_le_pow_left₀ h0 hb 2).trans hj

end Kakeya4.Hard.MultiplicativeConvolution
