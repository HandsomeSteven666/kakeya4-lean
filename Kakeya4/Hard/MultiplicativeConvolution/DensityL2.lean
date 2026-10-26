import Kakeya4.Hard.MultiplicativeConvolution.SmoothingProfile
import Kakeya4.Hard.MultiplicativeConvolution.SmallBallEnergy

/-!
# Pair representation and close-encounter bound for the actual smoothed density

All integrals remain nonnegative extended-valued integrals until finiteness has
been established. The original law may be atomic or singular.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The squared L2 mass of the actual additive density. -/
def densityL2 (μ : Measure ℝ) (p : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ z, additiveDensity μ p z ^ 2

/-- Actual pair overlap of two translated physical profiles. -/
def densityPairKernel (p : ℝ → ℝ≥0∞) (x y : ℝ) : ℝ≥0∞ := ∫⁻ z, p (z-x) * p (z-y)

/-- Tonelli expresses density L2 exactly as a pair-overlap integral. -/
theorem densityL2_eq_pairKernel (μ : Measure ℝ) [SFinite μ]
    (p : ℝ → ℝ≥0∞) (hp : Measurable p) :
    densityL2 μ p = ∫⁻ x, ∫⁻ y, densityPairKernel p x y ∂μ ∂μ := by
  have hex (z : ℝ) : additiveDensity μ p z ^ 2 =
      ∫⁻ x, ∫⁻ y, p (z-x) * p (z-y) ∂μ ∂μ := by
    have hx : Measurable (fun x : ℝ ↦ p (z-x)) := hp.comp (by fun_prop)
    rw [additiveDensity, pow_two]
    exact (lintegral_lintegral_mul hx.aemeasurable hx.aemeasurable).symm
  calc
    _ = ∫⁻ z, ∫⁻ x, ∫⁻ y, p (z-x) * p (z-y) ∂μ ∂μ := lintegral_congr hex
    _ = ∫⁻ x, ∫⁻ z, ∫⁻ y, p (z-x) * p (z-y) ∂μ ∂volume ∂μ :=
      lintegral_lintegral_swap (by apply Measurable.aemeasurable; fun_prop)
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_lintegral_swap (by apply Measurable.aemeasurable; fun_prop)

/-- The pair overlap vanishes unless the original points are close. -/
theorem densityPairKernel_eq_zero (p : ℝ → ℝ≥0∞) {r x y : ℝ}
    (hpout : ∀ z, r < |z| → p z = 0) (hxy : ¬ |x-y| ≤ 2*r) :
    densityPairKernel p x y = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [] with z
  change p (z-x) * p (z-y) = 0
  by_cases hx : r < |z-x|
  · rw [hpout _ hx, zero_mul]
  · have hy : r < |z-y| := by
      have h := abs_sub_le x z y
      rw [abs_sub_comm x z] at h
      by_contra hy
      exact hxy (by linarith [le_of_not_gt hx, le_of_not_gt hy])
    rw [hpout _ hy, mul_zero]

/-- Height times unit integral bounds every actual pair overlap. -/
theorem densityPairKernel_le_height (p : ℝ → ℝ≥0∞) (hp : Measurable p)
    {A : ℝ≥0∞} (hpA : ∀ z, p z ≤ A) (hpone : ∫⁻ z, p z = 1) (x y : ℝ) :
    densityPairKernel p x y ≤ A := by
  calc
    _ ≤ ∫⁻ z, A * p (z-y) := lintegral_mono (fun z ↦ mul_le_mul_left (hpA _) _)
    _ = A * ∫⁻ z, p (z-y) := lintegral_const_mul _ (hp.comp (by fun_prop))
    _ = A := by rw [lintegral_sub_right_eq_self, hpone, mul_one]

/-- A bounded, normalized radius-r profile controls L2 by pair mass at 2r. -/
theorem densityL2_le_pairMass (μ : Measure ℝ) [SFinite μ] (p : ℝ → ℝ≥0∞)
    (hp : Measurable p) {A : ℝ≥0∞} (hA : A ≠ ⊤) (hpA : ∀ z, p z ≤ A)
    (hpone : ∫⁻ z, p z = 1) (r : ℝ) (hpout : ∀ z, r < |z| → p z = 0) :
    densityL2 μ p ≤ A * pairMass (2*r) μ := by
  rw [densityL2_eq_pairKernel μ p hp]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, (closedBall x (2*r)).indicator (fun _ ↦ A) y ∂μ ∂μ := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ closedBall x (2*r)
      · rw [indicator_of_mem hy]
        exact densityPairKernel_le_height p hp hpA hpone x y
      · have hxy : ¬ |x-y| ≤ 2*r := by
          simpa only [mem_closedBall, Real.dist_eq, abs_sub_comm] using hy
        rw [indicator_of_notMem hy, densityPairKernel_eq_zero p hpout hxy]
    _ = _ := by
      simp_rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
      rw [lintegral_const_mul' _ _ hA]
      rfl

end Kakeya4.Hard.MultiplicativeConvolution
