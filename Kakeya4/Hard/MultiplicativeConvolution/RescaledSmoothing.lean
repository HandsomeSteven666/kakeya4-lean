import Kakeya4.Hard.MultiplicativeConvolution.AllScaleSmoothing

/-! # Actual unit-support rescaling of the smoothed law, with all-radius ball payments -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- An a.e. assertion is transported through the actual two independent inputs. -/
theorem ae_smoothLaw_of_ae_pair (κ μ : Measure ℝ) [SFinite κ] [SFinite μ]
    (r : ℝ) {p : ℝ → Prop} (hp : MeasurableSet {z | p z})
    (h : ∀ᵐ x ∂μ, ∀ᵐ u ∂κ, p (x+r*u)) : ∀ᵐ z ∂smoothLaw κ r μ, p z := by
  unfold smoothLaw Measure.conv
  apply (ae_map_iff (by fun_prop) hp).2
  apply (Measure.ae_prod_iff_ae_ae (hp.preimage (by fun_prop))).2
  filter_upwards [h] with x hx
  exact (ae_map_iff (by fun_prop) (hp.preimage (by fun_prop))).2 hx

/-- Smooth at the original scale, then genuinely map the output by x/2. -/
def unitRescaledSmoothLaw (κ : SmoothKernel) (r : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (smoothLaw κ.law r μ).map (fun x ↦ x/2)

/-- The rescaled smoothing is a genuine probability law. -/
instance unitRescaledSmoothLaw_isProbabilityMeasure (κ : SmoothKernel) (r : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (unitRescaledSmoothLaw κ r μ) := by
  unfold unitRescaledSmoothLaw
  infer_instance

/-- The half dilation recovers unit support for all scales r<=1. -/
theorem unitRescaledSmoothLaw_unitSupported (κ : SmoothKernel) (μ : Measure ℝ) [SFinite μ]
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hμ : UnitSupported μ) :
    UnitSupported (unitRescaledSmoothLaw κ r μ) := by
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).2
  apply ae_smoothLaw_of_ae_pair κ.law μ r (measurableSet_le (by fun_prop) measurable_const)
  filter_upwards [hμ] with x hx
  filter_upwards [κ.law_unitSupported] with u hu
  have hru : |r*u| ≤ r := by rw [abs_mul, abs_of_nonneg hr]; exact mul_le_of_le_one_right hr hu
  have hadd := abs_add_le x (r*u)
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), div_le_one (by norm_num : (0:ℝ) < 2)]
  linarith

/-- Exact ball preimage under the fixed half dilation. -/
theorem unitRescaledSmoothLaw_closedBall (κ : SmoothKernel) (μ : Measure ℝ)
    (r z R : ℝ) : unitRescaledSmoothLaw κ r μ (closedBall z R) =
      smoothLaw κ.law r μ (closedBall (2*z) (2*R)) := by
  rw [unitRescaledSmoothLaw, Measure.map_apply (by fun_prop) measurableSet_closedBall]
  congr 1
  ext x
  simp only [mem_preimage, mem_closedBall, Real.dist_eq]
  rw [show x/2-z = (x-2*z)/2 by ring, abs_div,
    abs_of_pos (by norm_num : (0:ℝ) < 2), div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  rw [mul_comm R 2]

/-- Half dilation preserves all-radius nonconcentration with the explicit 2^s payment. -/
theorem exists_unitRescaledSmoothLaw_all_scale_ball_bound (κ : SmoothKernel) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ] (r B : ℝ), 0 < r → 0 ≤ B →
      (∀ (z R : ℝ), r ≤ R → μ (closedBall z R) ≤ ENNReal.ofReal (B*R^s)) →
      ∀ (z R : ℝ), 0 < R → unitRescaledSmoothLaw κ r μ (closedBall z R) ≤ ENNReal.ofReal (C*B*R^s) := by
  obtain ⟨C,hC,hbound⟩ := exists_smoothLaw_all_scale_ball_bound κ hs hs1
  refine ⟨C*(2:ℝ)^s,mul_pos hC (by positivity),?_⟩
  intro μ _ r B hr hB hball z R hR
  rw [unitRescaledSmoothLaw_closedBall]
  have h := hbound μ r B hr hB hball (2*z) (2*R) (by positivity)
  have heq : C*B*(2*R)^s = (C*(2:ℝ)^s)*B*R^s := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hR.le]
    ring
  simpa only [heq] using h

end Kakeya4.Hard.MultiplicativeConvolution
