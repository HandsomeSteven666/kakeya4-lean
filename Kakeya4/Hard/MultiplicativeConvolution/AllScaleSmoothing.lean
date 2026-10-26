import Kakeya4.Hard.MultiplicativeConvolution.SmoothingDensityBound

/-!
# Actual smoothing extends coarse nonconcentration to every positive radius

The constant is chosen from the fixed kernel height before all input measures,
scales and coarse mass coefficients. Both fine and coarse radii are proved.
-/

noncomputable section
open MeasureTheory Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The fine-radius linear density estimate is no larger than the desired power. -/
theorem fine_radius_linear_le_power {s r R : ℝ} (hs1 : s ≤ 1)
    (hr : 0 < r) (hR : 0 < R) (hRr : R ≤ r) : r^(s-1)*R ≤ R^s := by
  have h := Real.rpow_le_rpow_of_nonpos hR hRr (by linarith : s-1 ≤ 0)
  calc
    _ ≤ R^(s-1)*R := mul_le_mul_of_nonneg_right h hR.le
    _ = _ := by rw [Real.rpow_sub hR, Real.rpow_one]; field_simp

/-- A genuine bound at radii R>=r becomes an all-positive-radius bound after actual smoothing. -/
theorem exists_smoothLaw_all_scale_ball_bound (κ : SmoothKernel) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ] (r B : ℝ), 0 < r → 0 ≤ B →
      (∀ (z R : ℝ), r ≤ R → μ (closedBall z R) ≤ ENNReal.ofReal (B*R^s)) →
      ∀ (z R : ℝ), 0 < R → smoothLaw κ.law r μ (closedBall z R) ≤ ENNReal.ofReal (C*B*R^s) := by
  obtain ⟨M,hMpos,hM⟩ := κ.exists_height
  let C := 2*M+(2:ℝ)^s
  have hCpos : 0 < C := add_pos (mul_pos (by norm_num) hMpos) (by positivity)
  have hMC : 2*M ≤ C := le_add_of_nonneg_right (by positivity)
  have htwoC : (2:ℝ)^s ≤ C := le_add_of_nonneg_left (by positivity)
  refine ⟨C,hCpos,?_⟩
  intro μ _ r B hr hB hball z R hR
  by_cases hRr : R ≤ r
  · have hf := smoothLaw_ball_le_density_bound κ μ hMpos.le hM hB hr
      (fun z ↦ hball z r le_rfl) z R hR
    apply hf.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = (2*M*B)*(r^(s-1)*R) := by ring
      _ ≤ (2*M*B)*R^s := mul_le_mul_of_nonneg_left
        (fine_radius_linear_le_power hs1 hr hR hRr) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMC hB) (by positivity)
  · have hrR : r ≤ R := (lt_of_not_ge hRr).le
    calc
      _ ≤ μ (closedBall z (R+r)) := smoothLaw_closedBall_le κ.law κ.law_unitSupported μ hr.le z R
      _ ≤ ENNReal.ofReal (B*(R+r)^s) := hball z (R+r) (by linarith)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hp := Real.rpow_le_rpow (by linarith : 0 ≤ R+r) (by linarith : R+r ≤ 2*R) hs
        calc
          _ ≤ B*(2*R)^s := mul_le_mul_of_nonneg_left hp hB
          _ = ((2:ℝ)^s*B)*R^s := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hR.le]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htwoC hB) (by positivity)

end Kakeya4.Hard.MultiplicativeConvolution
