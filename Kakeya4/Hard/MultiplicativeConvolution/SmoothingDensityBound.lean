import Kakeya4.Hard.MultiplicativeConvolution.SmoothingBallTransport

/-! # Local-mass bounds for the actual physical smoothing density -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual density samples only an original ball of radius r. -/
theorem additiveDensity_le_local_mass (κ : SmoothKernel) (μ : Measure ℝ)
    {M r : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, κ.density x ≤ M) (hr : 0 < r) (z : ℝ) :
    additiveDensity μ (kernelProfile κ r) z ≤ ENNReal.ofReal (M/r) * μ (closedBall z r) := by
  have hheight (x : ℝ) : kernelProfile κ r (z-x) ≤ ENNReal.ofReal (M/r) := by
    have h := kernelProfile_le κ hM r (z-x)
    rw [abs_of_pos (inv_pos.mpr hr), ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)] at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  calc
    _ ≤ ∫⁻ x, (closedBall z r).indicator (fun _ ↦ ENNReal.ofReal (M/r)) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ closedBall z r
      · rw [indicator_of_mem hx]
        exact hheight x
      · rw [indicator_of_notMem hx]
        have hout : r < |z-x| := by
          have h : ¬ |x-z| ≤ r := by simpa only [mem_closedBall, Real.dist_eq] using hx
          simpa only [abs_sub_comm] using lt_of_not_ge h
        change kernelProfile κ r (z-x) ≤ 0
        rw [kernelProfile_zero_of_radius κ hr hout]
    _ = _ := by rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]

/-- A true coarse ball bound gives a uniform pointwise density bound at scale r. -/
theorem additiveDensity_le_of_ball_bound (κ : SmoothKernel) (μ : Measure ℝ)
    {M B s r : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, κ.density x ≤ M)
    (hB : 0 ≤ B) (hr : 0 < r)
    (hball : ∀ z, μ (closedBall z r) ≤ ENNReal.ofReal (B*r^s)) (z : ℝ) :
    additiveDensity μ (kernelProfile κ r) z ≤ ENNReal.ofReal (M*B*r^(s-1)) := by
  calc
    _ ≤ ENNReal.ofReal (M/r) * μ (closedBall z r) := additiveDensity_le_local_mass κ μ hM0 hM hr z
    _ ≤ ENNReal.ofReal (M/r) * ENNReal.ofReal (B*r^s) := mul_le_mul_right (hball z) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (div_nonneg hM0 hr.le), Real.rpow_sub hr, Real.rpow_one]
      congr 1
      ring

/-- Integrating the actual density gives the fine-radius linear bound. -/
theorem smoothLaw_ball_le_density_bound (κ : SmoothKernel) (μ : Measure ℝ) [SFinite μ]
    {M B s r : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, κ.density x ≤ M)
    (hB : 0 ≤ B) (hr : 0 < r)
    (hball : ∀ z, μ (closedBall z r) ≤ ENNReal.ofReal (B*r^s))
    (z R : ℝ) (hR : 0 < R) :
    smoothLaw κ.law r μ (closedBall z R) ≤ ENNReal.ofReal (2*M*B*r^(s-1)*R) := by
  rw [smoothLaw_eq_withDensity κ μ hr.ne']
  change (volume.withDensity (additiveDensity μ (kernelProfile κ r))) (closedBall z R) ≤ _
  rw [withDensity_apply _ measurableSet_closedBall]
  calc
    _ ≤ ∫⁻ _ in closedBall z R, ENNReal.ofReal (M*B*r^(s-1)) :=
      lintegral_mono (fun u ↦ additiveDensity_le_of_ball_bound κ μ hM0 hM hB hr hball u)
    _ = _ := by
      rw [setLIntegral_const, Real.volume_closedBall,
        ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hM0 hB) (by positivity))]
      congr 1
      ring

end Kakeya4.Hard.MultiplicativeConvolution
