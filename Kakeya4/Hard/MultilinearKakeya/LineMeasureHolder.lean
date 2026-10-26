import Kakeya4.Hard.MultilinearKakeya.IntegratedFactorMajorant
import Kakeya4.Hard.MultilinearKakeya.DiscreteKernelMajorant

/-! Actual line-law factor integration and finite spatial Holder. Total
measure masses replace finite sums of line weights, without normalization. -/

noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem actual_lineMeasure_kernel_holder_budget {n : ℕ} (hn : 2 ≤ n)
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    {κ : Type*} [Fintype κ] (b : κ → E n) (a : κ → ℝ) (ha : ∀ q, 1 ≤ a q)
    {C : ℕ} (hoverlap : ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.closedBall (b q) 1)).card ≤ C)
    (R : ℝ) :
    (∀ q, lineMeasureKernel μ R (b q) ≠ ⊤) ∧
      (∑ q, (directionalDeterminantConstant n*a q*(lineMeasureKernel μ R (b q)).toReal)^((n : ℝ)⁻¹)) ≤
        ballTubeBudgetCost n C R*weightedVisibilityDegreeBound n a*
          (∏ i, (μ i).real univ)^((n : ℝ)⁻¹) := by
  obtain ⟨S,hM,hS,hdet,hbudget⟩ := exists_measurable_geometric_ballTube_factors hn b a ha hoverlap R
  let B := ballTubeBudgetCost n C R*weightedVisibilityDegreeBound n a
  have hB : ∀ p, ∑ q, S p q ≤ B := hbudget
  have hI (i : Fin n) (q : κ) : Integrable (fun p => S p q) (μ i) :=
    integrable_factor_of_finite_sum_budget (μ i) S hM hS hB q
  have hiB (i : Fin n) : (∑ q, ∫ p, S p q ∂μ i) ≤ (μ i).real univ*B :=
    sum_integral_factor_le_of_finite_sum_budget (μ i) S hM hS hB
  have hlocal (q : κ) := real_lineMeasureKernel_le_integrated_product μ R (b q)
    (fun _ p => S p q) (fun i => hI i q) (fun _ p => hS p q)
    (mul_pos (directionalDeterminantConstant_pos (by omega : 0 < n))
      (lt_of_lt_of_le zero_lt_one (ha q))) (hdet q)
  refine ⟨fun q => (hlocal q).1,?_⟩
  have h := real_sum_local_product_majorant_le (ι := fun _ : Fin n => Unit) (by omega : 0 < n)
    (fun q => directionalDeterminantConstant n*a q*(lineMeasureKernel μ R (b q)).toReal)
    (fun q => mul_nonneg (mul_nonneg (directionalDeterminantConstant_pos (by omega : 0 < n)).le
      (le_trans zero_le_one (ha q))) ENNReal.toReal_nonneg)
    (fun _ _ => (1 : ℝ)) (fun _ _ => zero_le_one)
    (fun i q _ => ∫ p, S p q ∂μ i)
    (fun i q _ => integral_nonneg (fun p => hS p q))
    (fun i => (μ i).real univ*B) (fun i _ => hiB i)
    (fun q => by simpa using (hlocal q).2)
  simp only [Fintype.sum_unique,one_mul] at h
  have hBnonneg : 0 ≤ B := mul_nonneg (ballTubeBudgetCost_nonneg n C R)
    (weightedVisibilityDegreeBound_nonneg n a (fun q => le_trans zero_le_one (ha q)))
  rw [real_prod_uniform_budget_rpow (by omega : 0 < n) (fun i => (μ i).real univ)
    (fun _ => ENNReal.toReal_nonneg) hBnonneg] at h
  exact h

theorem lineMeasureKernel_ne_top {n : ℕ} (hn : 2 ≤ n)
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    (R : ℝ) (x : E n) : lineMeasureKernel μ R x ≠ ⊤ := by
  have hov : ∀ y, (Finset.univ.filter (fun _ : Unit => y ∈ Metric.closedBall x 1)).card ≤ 1 := by
    intro y
    exact (Finset.card_filter_le _ _).trans (by simp)
  exact (actual_lineMeasure_kernel_holder_budget hn μ (fun _ : Unit => x) (fun _ => 1)
    (fun _ => le_rfl) hov R).1 ()

end Kakeya4.Hard.MultilinearKakeya
