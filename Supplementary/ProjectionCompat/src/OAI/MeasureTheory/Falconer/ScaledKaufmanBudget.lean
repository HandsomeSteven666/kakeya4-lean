import OAI.MeasureTheory.Falconer.UniformProductNormalizedProjection

/-! Controlled larger collision scales pay for actual vector lengths. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem kaufman_real_scaled_budget {R e σ p K κ : ℝ} (hR : 1 ≤ R) (he : 0 ≤ e)
    (hp : p = σ+16*e) (hκp : κ*p ≤ e) (hK : 0 ≤ K) (hKb : K ≤ R^e)
    (hc : 2*(6:ℝ)^p ≤ R^e) :
    (2*K*(2*(3*R^(κ-1)))^p*R^(2*e))/(R^(-(σ+2*e))) ≤ R^(-8*e) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hform : (2*K*(2*(3*R^(κ-1)))^p*R^(2*e))/(R^(-(σ+2*e))) =
      (2*(6:ℝ)^p)*K*(R^((κ-1)*p)*R^(2*e)*R^(σ+2*e)) := by
    rw [show 2*(3*R^(κ-1)) = 6*R^(κ-1) by ring,
      Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_mul hR0.le,
      Real.rpow_neg hR0.le (σ+2*e),div_eq_mul_inv,inv_inv]
    ring
  rw [hform]
  calc
    _ ≤ R^e*R^e*(R^((κ-1)*p)*R^(2*e)*R^(σ+2*e)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hc hKb hK (by positivity)) (by positivity)
    _ = R^(σ+6*e+(κ-1)*p) := by
      rw [← Real.rpow_add hR0,← Real.rpow_add hR0,← Real.rpow_add hR0,← Real.rpow_add hR0]
      congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by nlinarith [hp])

#print axioms kaufman_real_scaled_budget
end OAI.Falconer
