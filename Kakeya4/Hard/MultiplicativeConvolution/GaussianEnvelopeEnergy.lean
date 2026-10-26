import Kakeya4.Hard.MultiplicativeConvolution.GaussianEnvelopeL2
import Kakeya4.Hard.MultiplicativeConvolution.GaussianPowerBound
import Kakeya4.Hard.MultiplicativeConvolution.SmallBallEnergy

/-! # Original physical energy controls the actual Gaussian envelope L2 mass -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The envelope square is bounded by capped energy at the original radius. -/
theorem gaussianAverage_sq_le_cappedEnergy (ν : Measure ℝ) [IsFiniteMeasure ν]
    {s r ξ : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : 0 < r) (hξr : 1 ≤ |ξ| * r) :
    ENNReal.ofReal (∫ u, gaussianAverage ν ξ u ^ 2) ≤
      ENNReal.ofReal (r^s) * cappedEnergy s r ν := by
  let f : ℝ → ℝ → ℝ := fun y z ↦ Real.exp (-(Real.pi/2)*(ξ*y-ξ*z)^2)
  have hf1 (y z : ℝ) : f y z ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (sq_nonneg _)
  have hi : Integrable (fun p : ℝ × ℝ ↦ f p.1 p.2) (ν.prod ν) := by
    apply Integrable.of_bound (by dsimp [f]; fun_prop) 1
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_pos (show 0 < f p.1 p.2 from Real.exp_pos _)]
    exact hf1 _ _
  have heq : ENNReal.ofReal (∫ y, ∫ z, f y z ∂ν ∂ν) =
      ∫⁻ y, ∫⁻ z, ENNReal.ofReal (f y z) ∂ν ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hi.integral_prod_left
      (Filter.Eventually.of_forall (fun y ↦ integral_nonneg (fun z ↦ (Real.exp_pos _).le)))]
    apply lintegral_congr
    intro y
    have hiy : Integrable (f y) ν := by
      apply Integrable.of_bound (by dsimp [f]; fun_prop) 1
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_pos (show 0 < f y z from Real.exp_pos _)]
      exact hf1 _ _
    exact ofReal_integral_eq_lintegral_ofReal hiy
      (Filter.Eventually.of_forall (fun z ↦ (Real.exp_pos _).le))
  have hroot : ENNReal.ofReal (Real.sqrt (1/2)) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)
    have hn := Real.sqrt_nonneg (1/2 : ℝ)
    nlinarith
  rw [integral_gaussianAverage_sq, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  change ENNReal.ofReal (Real.sqrt (1/2)) * ENNReal.ofReal (∫ y, ∫ z, f y z ∂ν ∂ν) ≤ _
  calc
    _ ≤ ENNReal.ofReal (∫ y, ∫ z, f y z ∂ν ∂ν) := mul_le_of_le_one_left bot_le hroot
    _ = _ := heq
    _ ≤ ∫⁻ y, ∫⁻ z, ENNReal.ofReal (r^s) * cappedKernel s r y z ∂ν ∂ν := by
      apply lintegral_mono
      intro y
      apply lintegral_mono
      intro z
      have he : f y z = Real.exp (-(Real.pi/2)*ξ^2*(y-z)^2) := by
        dsimp [f]
        congr 1
        ring
      change ENNReal.ofReal (f y z) ≤ ENNReal.ofReal (r^s) * cappedKernel s r y z
      rw [he]
      exact ofReal_scaledGaussian_le_capped (by linarith [Real.pi_gt_three]) hs hs1 hr hξr y z
    _ = _ := by simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; rfl

/-- The original smooth energy controls the real envelope without changing scales. -/
theorem gaussianAverage_sq_le_smoothEnergy (κ : SmoothKernel)
    (ν : Measure ℝ) [IsFiniteMeasure ν] {s r ξ : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : 0 < r) (hξr : 1 ≤ |ξ| * r) :
    ENNReal.ofReal (∫ u, gaussianAverage ν ξ u ^ 2) ≤
      ENNReal.ofReal ((3*r)^s) * smoothEnergy κ.law s r ν := by
  have he := smoothEnergy_ge_capped κ.law κ.law_unitSupported ν hs hr.le
  have hcancel : ENNReal.ofReal 3 ^ s * ENNReal.ofReal 3 ^ (-s) = 1 := by
    rw [← ENNReal.rpow_add s (-s) (by norm_num) ENNReal.ofReal_ne_top]
    simp
  have hcap : cappedEnergy s r ν ≤ ENNReal.ofReal 3 ^ s * smoothEnergy κ.law s r ν := by
    simpa only [← mul_assoc, hcancel, one_mul] using mul_le_mul_right he (ENNReal.ofReal 3 ^ s)
  calc
    _ ≤ ENNReal.ofReal (r^s) * cappedEnergy s r ν :=
      gaussianAverage_sq_le_cappedEnergy ν hs hs1 hr hξr
    _ ≤ ENNReal.ofReal (r^s) * (ENNReal.ofReal 3 ^ s * smoothEnergy κ.law s r ν) :=
      mul_le_mul_right hcap _
    _ = _ := by
      rw [← mul_assoc, ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 3),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr.le]
      congr 1
      congr 1
      ring

end Kakeya4.Hard.MultiplicativeConvolution
