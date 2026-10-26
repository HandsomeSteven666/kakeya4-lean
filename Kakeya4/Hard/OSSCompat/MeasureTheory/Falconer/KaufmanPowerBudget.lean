






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.RieszCoefficientBudget

/-! The actual scalar budget used by the law-uniform Kaufman consumer. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem kaufman_real_dyadic_budget {R e σ p K : ℝ} (hR : 1 ≤ R) (he : 0 ≤ e)
    (hp : p = σ+16*e) (hK : 0 ≤ K) (hKb : K ≤ R^e)
    (hc : 2*(6:ℝ)^p ≤ R^e) :
    (2*K*(2*(3/R))^p*R^(2*e))/(R^(-(σ+2*e))) ≤ R^(-8*e) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hform : (2*K*(2*(3/R))^p*R^(2*e))/(R^(-(σ+2*e))) =
      (2*(6:ℝ)^p)*K*(R^(-p)*R^(2*e)*R^(σ+2*e)) := by
    rw [show 2*(3/R) = 6/R by ring,Real.div_rpow (by norm_num) hR0.le,
      Real.rpow_neg hR0.le (σ+2*e),div_eq_mul_inv,inv_inv,
      Real.rpow_neg hR0.le p]
    ring
  rw [hform]
  calc
    _ ≤ R^e*R^e*(R^(-p)*R^(2*e)*R^(σ+2*e)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hc hKb hK (by positivity)) (by positivity)
    _ = R^(σ+6*e-p) := by
      rw [← Real.rpow_add hR0,← Real.rpow_add hR0,← Real.rpow_add hR0,← Real.rpow_add hR0]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by rw [hp]; linarith)

theorem kaufman_cover_exponent_identity {R e σ : ℝ} (hR : 0 < R) :
    (R^(-e))^2/(R^(-(σ+2*e))) = R^σ := by
  rw [← Real.rpow_natCast (R^(-e)) 2,← Real.rpow_mul hR.le,← Real.rpow_sub hR]
  congr 1
  norm_num
  ring

#print axioms kaufman_real_dyadic_budget
#print axioms kaufman_cover_exponent_identity
end OAI.Falconer
