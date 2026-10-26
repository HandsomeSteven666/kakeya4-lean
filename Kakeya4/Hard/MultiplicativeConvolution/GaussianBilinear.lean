import Kakeya4.Hard.MultiplicativeConvolution.GaussianReproduction

/-!
# Actual positive Gaussian reduction of the bilinear oscillatory integral

The tilted law is constructed from the original input. All integral swaps are
proved absolutely convergent; no supplied cutoff or oscillatory certificate is
assumed. The remaining central/tail estimates are separate obligations.
-/

noncomputable section
open MeasureTheory

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual Gaussian envelope of the second input law. -/
def gaussianAverage (ν : Measure ℝ) (ξ u : ℝ) : ℝ :=
  ∫ y, gaussianWeight (ξ*y-u) ∂ν

/-- The envelope is pointwise nonnegative. -/
theorem gaussianAverage_nonneg (ν : Measure ℝ) (ξ u : ℝ) :
    0 ≤ gaussianAverage ν ξ u := integral_nonneg (fun _ ↦ (Real.exp_pos _).le)

/-- The full Gaussian kernel is integrable on the finite-law times Lebesgue product. -/
theorem integrable_gaussian_bilinearProfile (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ gaussianWeight (ξ*p.1-p.2)) (ν.prod volume) := by
  rw [integrable_prod_iff (by unfold gaussianWeight; fun_prop)]
  constructor
  · exact Filter.Eventually.of_forall (fun y ↦ integrable_gaussianWeight.comp_sub_left (ξ*y))
  · have h : (fun y : ℝ ↦ ∫ u, ‖gaussianWeight (ξ*y-u)‖) =
        fun _ ↦ ∫ u, gaussianWeight u := by
      funext y
      have hn : (fun u : ℝ ↦ ‖gaussianWeight (ξ*y-u)‖) =
          fun u ↦ gaussianWeight (ξ*y-u) := by
        funext u
        rw [Real.norm_eq_abs, abs_of_pos (show 0 < gaussianWeight (ξ*y-u) from Real.exp_pos _)]
      rw [hn]
      exact integral_sub_left_eq_self gaussianWeight volume (ξ*y)
    rw [h]
    exact integrable_const _

/-- Bounded finite-law Fourier amplitudes preserve absolute convergence. -/
theorem integrable_gaussian_fourierProfile (η ν : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ν] (ξ : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ gaussianWeight (ξ*p.1-p.2) * ‖fourier η p.2‖)
      (ν.prod volume) := by
  have hm : Measurable (fourier η) := measurable_charFun.comp (by fun_prop)
  apply ((integrable_gaussian_bilinearProfile ν ξ).const_mul (η.real Set.univ)).mono'
    (by unfold gaussianWeight; fun_prop)
  filter_upwards [] with p
  have hg : 0 ≤ gaussianWeight (ξ*p.1-p.2) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg (norm_nonneg _))]
  have hf : ‖fourier η p.2‖ ≤ η.real Set.univ := norm_charFun_le _
  exact (mul_le_mul_of_nonneg_left hf hg).trans_eq (mul_comm _ _)

/-- The actual product-law Fourier amplitude is reduced to a positive Gaussian integral. -/
theorem norm_fourier_mconv_le_gaussian (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : UnitSupported μ) (ξ : ℝ) :
    ‖fourier (μ ∗ₘ ν) ξ‖ ≤
      ∫ u, ‖fourier (gaussianTiltLaw μ) u‖ * gaussianAverage ν ξ u := by
  let η := gaussianTiltLaw μ
  have hprod := integrable_gaussian_fourierProfile η ν ξ
  have hm : Measurable (fourier μ) := measurable_charFun.comp (by fun_prop)
  have hleft : Integrable (fun y ↦ ‖fourier μ (ξ*y)‖) ν := by
    apply Integrable.of_bound ((hm.comp (by fun_prop)).norm.aestronglyMeasurable) (μ.real Set.univ)
    filter_upwards [] with y
    simpa only [norm_norm, fourier, Function.comp_apply] using
      (norm_charFun_le (μ := μ) (-(2*Real.pi)*(ξ*y)))
  rw [Measure.mconv_comm μ ν, fourier_multiplicativeConvolution]
  calc
    _ ≤ ∫ y, ‖fourier μ (ξ*y)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ∫ u, gaussianWeight (ξ*y-u) * ‖fourier η u‖ ∂volume ∂ν := by
      apply integral_mono_ae hleft hprod.integral_prod_left
      filter_upwards [] with y
      rw [fourier_gaussian_reproduction μ hμ]
      have h := norm_integral_le_integral_norm (μ := volume)
        (fun u : ℝ ↦ (gaussianWeight (ξ*y-u) : ℂ) * fourier η u)
      have hn (u : ℝ) : ‖(gaussianWeight (ξ*y-u) : ℂ) * fourier η u‖ =
          gaussianWeight (ξ*y-u) * ‖fourier η u‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (show 0 < gaussianWeight (ξ*y-u) from Real.exp_pos _)]
      simpa only [hn] using h
    _ = _ := by
      rw [integral_integral_swap hprod]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_mul_const]
      simp only [gaussianAverage]
      ring

end Kakeya4.Hard.MultiplicativeConvolution
