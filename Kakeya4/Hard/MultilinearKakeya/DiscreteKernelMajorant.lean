import Kakeya4.Hard.MultilinearKakeya.RealKernel
import Kakeya4.Hard.MultilinearKakeya.RealFiniteFactors

/-! The actual real determinant-incidence kernel is majorized by the products
of the constructed line factors. No distinctness or positive line-weight
assumption is introduced. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators NNReal

namespace Kakeya4.Hard.MultilinearKakeya

def ballTubeBudgetCost (n C : ℕ) (R : ℝ) : ℝ :=
  (C : ℝ)*((ENNReal.ofReal (R+1))^(n-1)*transverseUnitVolume n).toReal*Real.pi

theorem ballTubeBudgetCost_nonneg (n C : ℕ) (R : ℝ) : 0 ≤ ballTubeBudgetCost n C R := by
  unfold ballTubeBudgetCost
  positivity

theorem realKernel_le_product_of_line_factors {n : ℕ}
    {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (R : ℝ) (b : E n)
    (S : Line n → ℝ) (hS : ∀ l, 0 ≤ S l) {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hdet : ∀ l : Fin n → Line n, (∀ i, b ∈ (l i).tube R) →
      c*a*|Matrix.det (fun i j => (l j).direction i)| ≤ ∏ i, S (l i)) :
    c*a*realKernel L w R b ≤ ∏ i, ∑ t, (w i t : ℝ)*S (L i t) := by
  rw [Fintype.prod_sum]
  unfold realKernel
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : ∀ i, b ∈ (L i (t i)).tube R
  · rw [if_pos ht]
    have hpw : 0 ≤ ∏ i : Fin n, (w i (t i) : ℝ) :=
      Finset.prod_nonneg (fun i _ => (w i (t i)).coe_nonneg)
    have he := mul_le_mul_of_nonneg_right (hdet (fun i => L i (t i)) ht)
      hpw
    simp only [realTupleCoefficient]
    rw [Finset.prod_mul_distrib]
    nlinarith [he]
  · rw [if_neg ht,mul_zero]
    exact Finset.prod_nonneg (fun i _ => mul_nonneg (w i (t i)).coe_nonneg (hS _))

theorem actual_ballTube_kernel_holder_budget {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (a : κ → ℝ) (ha : ∀ q, 1 ≤ a q)
    {C : ℕ} (hoverlap : ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.closedBall (b q) 1)).card ≤ C)
    (R : ℝ) {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) :
    (∑ q, (directionalDeterminantConstant n*a q*realKernel L w R (b q))^((n : ℝ)⁻¹)) ≤
      ∏ i, ((∑ t, (w i t : ℝ)) *
        ((C : ℝ)*((ENNReal.ofReal (R+1))^(n-1)*transverseUnitVolume n).toReal*Real.pi*
          weightedVisibilityDegreeBound n a))^((n : ℝ)⁻¹) := by
  obtain ⟨S,hS,hdet,hB⟩ := exists_geometric_ballTube_factors hn b a ha hoverlap R
  apply real_sum_local_product_majorant_le (by omega : 0 < n)
    (fun q => directionalDeterminantConstant n*a q*realKernel L w R (b q))
    (fun q => mul_nonneg
      (mul_nonneg (directionalDeterminantConstant_pos (by omega : 0 < n)).le (le_trans zero_le_one (ha q)))
      (realKernel_nonneg L w R (b q)))
    (fun i t => (w i t : ℝ)) (fun i t => (w i t).coe_nonneg)
    (fun i q t => S (L i t) q) (fun i q t => hS _ _) _
    (fun i t => hB (L i t))
  intro q
  exact realKernel_le_product_of_line_factors L w R (b q) (fun l => S l q) (fun l => hS l q)
    (directionalDeterminantConstant_pos (by omega : 0 < n)).le (le_trans zero_le_one (ha q)) (hdet q)

theorem actual_ballTube_kernel_uniform_holder_budget {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (a : κ → ℝ) (ha : ∀ q, 1 ≤ a q)
    {C : ℕ} (hoverlap : ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.closedBall (b q) 1)).card ≤ C)
    (R : ℝ) {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) :
    (∑ q, (directionalDeterminantConstant n*a q*realKernel L w R (b q))^((n : ℝ)⁻¹)) ≤
      ballTubeBudgetCost n C R*weightedVisibilityDegreeBound n a*
        (∏ i, ∑ t, (w i t : ℝ))^((n : ℝ)⁻¹) := by
  have h := actual_ballTube_kernel_holder_budget hn b a ha hoverlap R L w
  have hnonneg : 0 ≤ ballTubeBudgetCost n C R*weightedVisibilityDegreeBound n a :=
    mul_nonneg (ballTubeBudgetCost_nonneg n C R)
      (weightedVisibilityDegreeBound_nonneg n a (fun q => le_trans zero_le_one (ha q)))
  change (∑ q, (directionalDeterminantConstant n*a q*realKernel L w R (b q))^((n : ℝ)⁻¹)) ≤
    ∏ i, ((∑ t, (w i t : ℝ))*(ballTubeBudgetCost n C R*weightedVisibilityDegreeBound n a))^((n : ℝ)⁻¹) at h
  rw [real_prod_uniform_budget_rpow (by omega : 0 < n) _
    (fun i => Finset.sum_nonneg (fun t _ => (w i t).coe_nonneg)) hnonneg] at h
  exact h

end Kakeya4.Hard.MultilinearKakeya
