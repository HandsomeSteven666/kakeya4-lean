import Kakeya4.Hard.MultiplicativeConvolution.GaussianEnvelopeL2

/-! # Actual Gaussian tail bounds from the finite first absolute moment -/

noncomputable section
open MeasureTheory Set

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The first absolute moment of every positive-width Gaussian is integrable. -/
theorem integrable_abs_mul_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun u : ℝ ↦ |u| * Real.exp (-b*u^2)) := by
  have h := (integrable_mul_exp_neg_mul_sq hb).norm
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using h

/-- Tail mass is bounded by the actual first absolute moment divided by the threshold. -/
theorem integral_gaussian_tail_le {b T : ℝ} (hb : 0 < b) (hT : 0 < T) :
    (∫ u in {u : ℝ | T < |u|}, Real.exp (-b*u^2)) ≤
      (∫ u : ℝ, |u| * Real.exp (-b*u^2)) / T := by
  have hset : MeasurableSet {u : ℝ | T < |u|} :=
    measurableSet_lt measurable_const (by fun_prop : Measurable (fun u : ℝ ↦ |u|))
  rw [← integral_indicator hset, ← integral_div]
  apply integral_mono ((integrable_exp_neg_mul_sq hb).indicator hset)
    ((integrable_abs_mul_gaussian hb).div_const T)
  intro u
  by_cases hu : T < |u|
  · rw [indicator_of_mem (show u ∈ {u : ℝ | T < |u|} from hu)]
    apply (le_div_iff₀ hT).mpr
    nlinarith [Real.exp_pos (-b*u^2)]
  · rw [indicator_of_notMem (show u ∉ {u : ℝ | T < |u|} from hu)]
    positivity

/-- Unit support gives the true Gaussian envelope a uniform tail profile. -/
theorem gaussianAverage_le_tail (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : UnitSupported ν) {ξ u : ℝ} (hu : 2*|ξ| < |u|) :
    gaussianAverage ν ξ u ≤ Real.exp (-(Real.pi/4)*u^2) := by
  have hb : ∀ᵐ y ∂ν, gaussianWeight (ξ*y-u) ≤ Real.exp (-(Real.pi/4)*u^2) := by
    filter_upwards [hν] with y hy
    have hxy : |ξ*y| ≤ |ξ| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hy
    have htri : |u| ≤ |ξ*y-u| + |ξ*y| := by
      have h := abs_sub_le (ξ*y-u) 0 (ξ*y)
      simpa only [sub_zero, sub_sub_cancel_left, zero_sub, abs_neg] using h
    have hhalf : |u|/2 ≤ |ξ*y-u| := by linarith
    have hsq : u^2/4 ≤ (ξ*y-u)^2 := by
      nlinarith [sq_abs u, sq_abs (ξ*y-u), abs_nonneg u, abs_nonneg (ξ*y-u)]
    apply Real.exp_le_exp.mpr
    change -Real.pi*(ξ*y-u)^2 ≤ -(Real.pi/4)*u^2
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsq)]
  have hi : Integrable (fun y ↦ gaussianWeight (ξ*y-u)) ν := by
    apply Integrable.of_bound (by unfold gaussianWeight; fun_prop) 1
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_pos (show 0 < gaussianWeight (ξ*y-u) from Real.exp_pos _)]
    exact gaussianWeight_le_one _
  have h := integral_mono_ae hi (integrable_const (Real.exp (-(Real.pi/4)*u^2))) hb
  simpa only [gaussianAverage, integral_const, probReal_univ, one_smul] using h

end Kakeya4.Hard.MultiplicativeConvolution
