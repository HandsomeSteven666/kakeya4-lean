import Kakeya4.Hard.MultiplicativeConvolution.GaussianEnergyCaps

/-! # A quantitative two-factor Fourier bound from the original energy caps -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The central coefficient depends only on the two energy exponents. -/
def twoFactorCentralConstant (s t : ℝ) : ℝ :=
  Real.sqrt ((gaussianWindowConstant*4*3^s*Real.exp (2*Real.pi))*3^t)

/-- The fixed tail coefficient is independent of all input laws and scales. -/
def twoFactorTailConstant : ℝ := Real.exp Real.pi * gaussianTailMoment / 2

/-- Unit probability inputs give a uniformly bounded actual tilted mass. -/
theorem gaussianTiltLaw_real_mass_le (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (gaussianTiltLaw μ).real univ ≤ Real.exp Real.pi := by
  have h : (gaussianTiltLaw μ) univ ≤ ENNReal.ofReal (Real.exp Real.pi) := by
    simpa only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using
      (gaussianTiltLaw_le μ univ)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_pos _).le] using ht

/-- Actual two-factor bound; all energy caps are at the original radius. -/
theorem norm_fourier_mconv_le_energy_powers (κ : SmoothKernel) {s t r ε ξ : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hr : 0 < r)
    (hξlo : 1 ≤ |ξ| * r) (hξhi : |ξ| ≤ 2/r)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : UnitSupported μ) (hν : UnitSupported ν)
    (heμ : smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)))
    (heν : smoothEnergy κ.law t r ν ≤ ENNReal.ofReal (r^(-ε))) :
    ‖fourier (μ ∗ₘ ν) ξ‖ ≤
      twoFactorCentralConstant s t * r^((s+t-1-2*ε)/2) + twoFactorTailConstant / |ξ| := by
  have hξ : ξ ≠ 0 := by intro h; simp only [h, abs_zero, zero_mul] at hξlo; linarith
  have hR : 2*|ξ| ≤ 4/r := by
    calc
      _ ≤ 2*(2/r) := mul_le_mul_of_nonneg_left hξhi (by norm_num)
      _ = _ := by ring
  let η := gaussianTiltLaw μ
  let A := gaussianWindowConstant*4*3^s*Real.exp (2*Real.pi)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (mul_nonneg gaussianWindowConstant_pos.le (by norm_num))
      (by positivity)) (Real.exp_pos _).le
  have ha : (∫ u in Icc (-(2*|ξ|)) (2*|ξ|), ‖fourier η u‖^2) ≤ A*r^(s-1-ε) := by
    apply le_trans ?_ (integral_fourier_sq_tilt_bound κ hs hs1 (by norm_num : (1:ℝ) ≤ 4) hr μ heμ)
    apply setIntegral_mono_set (integrableOn_fourier_sq η (4/r))
      (Filter.Eventually.of_forall (fun u ↦ sq_nonneg _))
    filter_upwards [] with u
    intro hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := integral_gaussianAverage_sq_bound κ ht ht1 hr hξlo ν heν
  have hc : Real.sqrt (∫ u in Icc (-(2*|ξ|)) (2*|ξ|), ‖fourier η u‖^2) *
      Real.sqrt (∫ u, gaussianAverage ν ξ u ^ 2) ≤
      twoFactorCentralConstant s t * r^((s+t-1-2*ε)/2) := by
    apply le_trans (mul_le_mul (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have he : (A*r^(s-1-ε))*(3^t*r^(t-ε)) = (A*3^t)*r^(s+t-1-2*ε) := by
      rw [show s+t-1-2*ε = (s-1-ε)+(t-ε) by ring, Real.rpow_add hr]
      ring
    rw [← Real.sqrt_mul (mul_nonneg hA (Real.rpow_nonneg hr.le _)), he,
      Real.sqrt_mul (mul_nonneg hA (by positivity)), Real.sqrt_eq_rpow (r^(s+t-1-2*ε)),
      ← Real.rpow_mul hr.le]
    change Real.sqrt (A*3^t) * r^((s+t-1-2*ε)*(1/2)) ≤
      Real.sqrt (A*3^t) * r^((s+t-1-2*ε)/2)
    exact le_of_eq (by congr 2; ring)
  have htail : η.real univ * gaussianTailMoment / (2*|ξ|) ≤ twoFactorTailConstant / |ξ| := by
    have hm := mul_le_mul_of_nonneg_right (gaussianTiltLaw_real_mass_le μ) gaussianTailMoment_nonneg
    have h := div_le_div_of_nonneg_right hm (by positivity : 0 ≤ 2*|ξ|)
    simpa only [twoFactorTailConstant, div_div] using h
  exact (norm_fourier_mconv_le_central_tail μ ν hμ hν hξ).trans (add_le_add hc htail)

end Kakeya4.Hard.MultiplicativeConvolution
