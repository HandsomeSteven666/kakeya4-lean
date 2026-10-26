import Kakeya4.Hard.MultiplicativeConvolution.GaussianSplit

/-! # Original energy caps for both actual factors in the central estimate -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual tilted Fourier window obeys the original input's energy cap. -/
theorem integral_fourier_sq_tilt_bound (κ : SmoothKernel) {s K r ε : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hK : 1 ≤ K) (hr : 0 < r)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (he : smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε))) :
    (∫ u in Icc (-(K/r)) (K/r), ‖fourier (gaussianTiltLaw μ) u‖^2) ≤
      (gaussianWindowConstant*K*3^s*Real.exp (2*Real.pi))*r^(s-1-ε) := by
  have hb := lowFrequencyMass_le_energy κ hs hs1 hK hr (gaussianTiltLaw μ)
  have ht := smoothEnergy_gaussianTilt_le κ.law μ s r
  have hc : 0 ≤ gaussianWindowConstant*K*3^s := by
    exact mul_nonneg (mul_nonneg gaussianWindowConstant_pos.le (by linarith)) (by positivity)
  have hbound : lowFrequencyMass (K/r) (gaussianTiltLaw μ) ≤
      ENNReal.ofReal ((gaussianWindowConstant*K*3^s*Real.exp (2*Real.pi))*r^(s-1-ε)) := by
    calc
      _ ≤ ENNReal.ofReal ((gaussianWindowConstant*K*3^s)*r^(s-1)) *
          (ENNReal.ofReal (Real.exp (2*Real.pi)) * ENNReal.ofReal (r^(-ε))) :=
        hb.trans (mul_le_mul_right (ht.trans (mul_le_mul_right he _)) _)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (mul_nonneg hc (Real.rpow_nonneg hr.le _))]
        congr 1
        rw [show s-1-ε = (s-1)+(-ε) by ring, Real.rpow_add hr]
        ring
  rw [← ofReal_integral_fourier_sq] at hbound
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ sq_nonneg _)),
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hc (Real.exp_pos _).le) (by positivity))] at h
  exact h

/-- The actual Gaussian envelope square receives the other original energy cap. -/
theorem integral_gaussianAverage_sq_bound (κ : SmoothKernel) {t r ξ ε : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hr : 0 < r) (hξr : 1 ≤ |ξ| * r)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (he : smoothEnergy κ.law t r ν ≤ ENNReal.ofReal (r^(-ε))) :
    (∫ u, gaussianAverage ν ξ u ^ 2) ≤ 3^t*r^(t-ε) := by
  have hb := gaussianAverage_sq_le_smoothEnergy κ ν ht ht1 hr hξr
  have hbound : ENNReal.ofReal (∫ u, gaussianAverage ν ξ u ^ 2) ≤
      ENNReal.ofReal (3^t*r^(t-ε)) := by
    calc
      _ ≤ ENNReal.ofReal ((3*r)^t) * ENNReal.ofReal (r^(-ε)) :=
        hb.trans (mul_le_mul_right he _)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (3*r)^t)]
        congr 1
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr.le,
          show t-ε = t+(-ε) by ring, Real.rpow_add hr]
        ring
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ sq_nonneg _)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 3^t*r^(t-ε))] at h
  exact h

end Kakeya4.Hard.MultiplicativeConvolution
