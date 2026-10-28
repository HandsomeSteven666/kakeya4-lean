import OAI.MeasureTheory.Falconer.DyadicOSSFrostmanProjection

/-! Actual coarser dyadic selection, mass thresholds and covering exponents. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem exists_coarser_dyadic_above_depth (M : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ ((2:ℝ)^M)⁻¹) :
    ∃ N ≥ M, δ ≤ ((2:ℝ)^N)⁻¹ ∧ ((2:ℝ)^N)⁻¹ < 2*δ := by
  obtain ⟨n,hlo,hhi⟩ := PlanarFalconer.exists_dyadic_scale
    (by positivity : 0 < ((2:ℝ)^M)⁻¹) hδ hsmall
  have he : ((2:ℝ)^M)⁻¹/(2:ℝ)^n = ((2:ℝ)^(M+n))⁻¹ := by
    rw [pow_add,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he] at hlo hhi
  exact ⟨M+n,Nat.le_add_right M n,hlo,hhi⟩

theorem coarser_dyadic_threshold_budget {R δ a : ℝ} (hR : 2 ≤ R)
    (hδ : 0 < δ) (hne : R⁻¹ < 2*δ) (ha : 0 ≤ a) :
    R^(-a) ≤ δ^(a/2) ∧ δ^(-(a/2)) ≤ R^a := by
  have hR0 : 0 < R := by linarith
  have hinv : 0 < R⁻¹ := inv_pos.mpr hR0
  have hhalf : R⁻¹ ≤ (1/2:ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hR0 (by norm_num : (0:ℝ) < 2)).mpr hR
  have hsquare : (R⁻¹)^2 ≤ δ := by nlinarith [mul_nonneg hinv.le (sub_nonneg.mpr hhalf)]
  have he : ((R⁻¹)^2)^(a/2) = R^(-a) := by
    rw [← Real.rpow_neg_one,← Real.rpow_natCast (R^(-1:ℝ)) 2,
      ← Real.rpow_mul hR0.le,← Real.rpow_mul hR0.le]
    congr 1; norm_num; ring
  have hm : R^(-a) ≤ δ^(a/2) := by
    rw [← he]
    exact Real.rpow_le_rpow (sq_nonneg _) hsquare (by positivity)
  refine ⟨hm,?_⟩
  rw [Real.rpow_neg hδ.le]
  have hh := (inv_le_inv₀ (Real.rpow_pos_of_pos hδ (a/2)) (Real.rpow_pos_of_pos hR0 (-a))).mpr hm
  simpa only [Real.rpow_neg hR0.le,inv_inv] using hh

theorem coarser_dyadic_cover_exponent {R δ σ σ' : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) (hne : R⁻¹ < 2*δ) (hσ : 0 ≤ σ)
    (habsorb : (2:ℝ)^σ ≤ R^(σ'-σ)) : δ^(-σ) ≤ R^σ' := by
  have hlow : 1/(2*R) ≤ δ := by
    apply (div_le_iff₀ (by positivity : 0 < 2*R)).mpr
    have hh := mul_lt_mul_of_pos_right hne hR
    rw [inv_mul_cancel₀ hR.ne'] at hh
    nlinarith
  calc
    _ ≤ (1/(2*R))^(-σ) := Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
    _ = (2*R)^σ := by
      rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
      congr 1; ring
    _ = (2:ℝ)^σ*R^σ := Real.mul_rpow (by norm_num) hR.le
    _ ≤ R^(σ'-σ)*R^σ := mul_le_mul_of_nonneg_right habsorb (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring

#print axioms exists_coarser_dyadic_above_depth
#print axioms coarser_dyadic_threshold_budget
#print axioms coarser_dyadic_cover_exponent
end OAI.Falconer
