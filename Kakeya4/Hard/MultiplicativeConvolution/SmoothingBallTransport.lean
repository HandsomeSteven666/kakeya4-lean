import Kakeya4.Hard.MultiplicativeConvolution.SmoothingProfile

/-! # Actual bounded-noise transport of ball masses and probability -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The smoothing law integrates the literal original point plus independent noise. -/
theorem lintegral_smoothLaw (κ μ : Measure ℝ) [SFinite κ] [SFinite μ]
    (r : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂smoothLaw κ r μ) = ∫⁻ x, ∫⁻ u, f (x+r*u) ∂κ ∂μ := by
  rw [smoothLaw, Measure.lintegral_conv hf]
  apply lintegral_congr
  intro x
  exact lintegral_map (hf.comp (by fun_prop)) (by fun_prop)

/-- Actual smoothing of probability laws preserves their mass. -/
instance smoothLaw_isProbabilityMeasure (κ μ : Measure ℝ)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure μ] (r : ℝ) :
    IsProbabilityMeasure (smoothLaw κ r μ) := by
  unfold smoothLaw
  infer_instance

/-- Unit-supported noise enlarges the test-ball radius by exactly r. -/
theorem smoothLaw_closedBall_le (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : UnitSupported κ) (μ : Measure ℝ) [SFinite μ] {r : ℝ} (hr : 0 ≤ r)
    (z R : ℝ) :
    smoothLaw κ r μ (closedBall z R) ≤ μ (closedBall z (R+r)) := by
  rw [← lintegral_indicator_one measurableSet_closedBall]
  change (∫⁻ a, (closedBall z R).indicator (fun _ ↦ (1:ℝ≥0∞)) a ∂smoothLaw κ r μ) ≤ _
  rw [lintegral_smoothLaw κ μ r (measurable_const.indicator measurableSet_closedBall)]
  calc
    _ ≤ ∫⁻ x, ∫⁻ _ : ℝ, (closedBall z (R+r)).indicator (fun _ ↦ (1:ℝ≥0∞)) x ∂κ ∂μ := by
      apply lintegral_mono
      intro x
      apply lintegral_mono_ae
      filter_upwards [hκ] with u hu
      by_cases hx : x ∈ closedBall z (R+r)
      · rw [indicator_of_mem hx]
        by_cases hy : x+r*u ∈ closedBall z R
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy]
          exact zero_le
      · rw [indicator_of_notMem hx]
        have hout : x+r*u ∉ closedBall z R := by
          intro hy
          have hy' : |x+r*u-z| ≤ R := by simpa only [mem_closedBall, Real.dist_eq] using hy
          have hru : |r*u| ≤ r := by
            rw [abs_mul, abs_of_nonneg hr]
            exact mul_le_of_le_one_right hr hu
          have htri := abs_add_le (x+r*u-z) (-(r*u))
          rw [show (x+r*u-z)+-(r*u) = x-z by ring, abs_neg] at htri
          apply hx
          rw [mem_closedBall, Real.dist_eq]
          linarith
        rw [indicator_of_notMem hout]
    _ = _ := by
      simp only [lintegral_const, measure_univ, mul_one]
      exact lintegral_indicator_one measurableSet_closedBall

end Kakeya4.Hard.MultiplicativeConvolution
