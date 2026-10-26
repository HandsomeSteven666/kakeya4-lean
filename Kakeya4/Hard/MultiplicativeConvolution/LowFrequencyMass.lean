import Kakeya4.Hard.MultiplicativeConvolution.GaussianEnergyKernel
import Kakeya4.Hard.MultiplicativeConvolution.NoiseEnergy

/-!
# Genuine low-frequency Fourier mass

A positive Gaussian window dominates the sharp frequency interval. Its moment
is the true positive pair kernel, already bounded by the original smooth energy.
No Fourier-Riesz identity or extra low-frequency certificate is a hypothesis.
-/

noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Actual Fourier squared mass on the closed frequency interval [-R,R]. -/
def lowFrequencyMass (R : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc (-R) R, ENNReal.ofReal (‖fourier μ t‖ ^ 2)

/-- A fixed positive finite Gaussian-window constant. -/
def gaussianWindowConstant : ℝ := Real.sqrt (2 * Real.pi) * Real.exp (1/2 : ℝ)

/-- The fixed window constant is positive. -/
theorem gaussianWindowConstant_pos : 0 < gaussianWindowConstant :=
  mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _)

/-- A physical frequency window is dominated by the actual Gaussian density. -/
theorem gaussian_pdf_dominates_window {R t : ℝ} (hR : 0 < R) (ht : |t| ≤ R) :
    1 ≤ (gaussianWindowConstant * R) * gaussianPDFReal 0 (frequencyVariance R) t := by
  have hsq : t^2 ≤ R^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hratio : t^2 / (2 * R^2) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*R^2)).mpr
    nlinarith
  have hsqrt : Real.sqrt (2 * Real.pi * R^2) = Real.sqrt (2 * Real.pi) * R := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi), Real.sqrt_sq_eq_abs, abs_of_pos hR]
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  calc
    1 ≤ Real.exp (1/2 : ℝ) * Real.exp (-t^2/(2*R^2)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      simpa only [neg_div, sub_eq_add_neg] using sub_nonneg.mpr hratio
    _ = _ := by
      unfold gaussianWindowConstant gaussianPDFReal
      rw [show ((frequencyVariance R) : ℝ) = R^2 by change R*R = R^2; ring]
      simp only [sub_zero]
      rw [hsqrt]
      field_simp

/-- Nonzero width gives the ordinary density branch of the Gaussian law. -/
theorem windowVariance_ne_zero {R : ℝ} (hR : 0 < R) :
    ((frequencyVariance R) : ℝ≥0) ≠ 0 := by
  intro hz
  have h := congrArg NNReal.toReal hz
  change R*R = 0 at h
  exact (mul_ne_zero hR.ne' hR.ne') h

/-- The Gaussian moment has its actual nonnegative-integral representation. -/
theorem ofReal_gaussianFourierMass (R : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ENNReal.ofReal (gaussianFourierMass R μ) =
      ∫⁻ t, ENNReal.ofReal (‖fourier μ t‖ ^ 2) ∂gaussianReal 0 (frequencyVariance R) := by
  have hm : Measurable (fun t ↦ ‖fourier μ t‖ ^ 2) := by
    unfold fourier
    exact ((measurable_charFun.comp (by fun_prop)).norm.pow_const 2)
  have hi : Integrable (fun t ↦ ‖fourier μ t‖ ^ 2)
      (gaussianReal 0 (frequencyVariance R)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (μ.real univ ^ 2)
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2
  exact ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))

/-- Actual sharp low-frequency mass is dominated by a genuine Gaussian moment. -/
theorem lowFrequencyMass_le_gaussian {R : ℝ} (hR : 0 < R)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    lowFrequencyMass R μ ≤ ENNReal.ofReal (gaussianWindowConstant * R) *
      ENNReal.ofReal (gaussianFourierMass R μ) := by
  have hv := windowVariance_ne_zero hR
  have hC : 0 ≤ gaussianWindowConstant * R := (mul_pos gaussianWindowConstant_pos hR).le
  have hf : Measurable (fun t ↦ ENNReal.ofReal (‖fourier μ t‖ ^ 2)) := by
    unfold fourier
    exact ((measurable_charFun.comp (by fun_prop)).norm.pow_const 2).ennreal_ofReal
  rw [lowFrequencyMass, ← lintegral_indicator measurableSet_Icc,
    ofReal_gaussianFourierMass, gaussianReal_of_var_ne_zero _ hv,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF _ _) hf,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro t
  by_cases ht : t ∈ Icc (-R) R
  · rw [indicator_of_mem ht]
    have hpd : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gaussianWindowConstant*R) *
        gaussianPDF 0 (frequencyVariance R) t := by
      rw [gaussianPDF, ← ENNReal.ofReal_mul hC]
      exact_mod_cast ENNReal.ofReal_le_ofReal (gaussian_pdf_dominates_window hR (abs_le.mpr ht))
    simpa only [one_mul, mul_assoc, Pi.mul_apply] using
      mul_le_mul_left hpd (ENNReal.ofReal (‖fourier μ t‖ ^ 2))
  · rw [indicator_of_notMem ht]
    exact bot_le

/-- Gaussian Fourier mass is controlled by the original, unmodified smooth energy. -/
theorem gaussianFourierMass_le_smoothEnergy (κ : SmoothKernel) {s r R : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : 0 < r) (hRr : 1 ≤ R*r)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ENNReal.ofReal (gaussianFourierMass R μ) ≤
      ENNReal.ofReal ((3*r)^s) * smoothEnergy κ.law s r μ := by
  have he := smoothEnergy_ge_capped κ.law κ.law_unitSupported μ hs hr.le
  have hcancel : ENNReal.ofReal 3 ^ s * ENNReal.ofReal 3 ^ (-s) = 1 := by
    rw [← ENNReal.rpow_add s (-s) (by norm_num) ENNReal.ofReal_ne_top]
    simp
  have hcap : cappedEnergy s r μ ≤ ENNReal.ofReal 3 ^ s * smoothEnergy κ.law s r μ := by
    simpa only [← mul_assoc, hcancel, one_mul] using mul_le_mul_right he (ENNReal.ofReal 3 ^ s)
  calc
    _ ≤ ENNReal.ofReal (r^s) * cappedEnergy s r μ :=
      gaussianFourierMass_le_cappedEnergy hs hs1 hr hRr μ
    _ ≤ ENNReal.ofReal (r^s) * (ENNReal.ofReal 3 ^ s * smoothEnergy κ.law s r μ) :=
      mul_le_mul_right hcap _
    _ = _ := by
      rw [← mul_assoc, ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 3),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr.le]
      congr 1
      congr 1
      ring

end Kakeya4.Hard.MultiplicativeConvolution
