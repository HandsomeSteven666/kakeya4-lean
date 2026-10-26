import Kakeya4.Hard.MultilinearKakeya.LineMeasureHolder
import Kakeya4.Hard.MultilinearKakeya.DiscreteEndpoint

/-! Finite spatial endpoint for arbitrary finite line laws. The exact positive
support rescaling/cancellation is the already verified finite-family algebra;
only the actual integrated factor budget replaces sums of line weights. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem real_discrete_lineMeasure_endpoint_of_positive_kernel {n : ℕ} (hn : 2 ≤ n)
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    {κ : Type*} [Fintype κ] (b : κ → E n) {C : ℕ}
    (hoverlap : ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.closedBall (b q) 1)).card ≤ C)
    (R : ℝ)
    (hpositive : ∀ q, 0 < (lineMeasureKernel μ R (b q)).toReal) :
    (∑ q, ((lineMeasureKernel μ R (b q)).toReal)^endpointExponent n) ≤
      discreteEndpointConstant n C R * (∏ i, (μ i).real univ)^endpointExponent n := by
  let F (q : κ) := (lineMeasureKernel μ R (b q)).toReal
  let H := ∑ q, (F q)^endpointExponent n
  let T := ∏ i, (μ i).real univ
  let c := directionalDeterminantConstant n
  let K := visibilityWeightCost n
  let G := ballTubeBudgetCost n C R*(n : ℝ)
  have hc : 0 < c := directionalDeterminantConstant_pos (by omega : 0 < n)
  have hK : 0 ≤ K := (visibilityWeightCost_pos n).le
  have hG : 0 ≤ G := mul_nonneg (ballTubeBudgetCost_nonneg n C R) (Nat.cast_nonneg n)
  have hT : 0 ≤ T := Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hHnonneg : 0 ≤ H := Finset.sum_nonneg (fun q _ => Real.rpow_nonneg (hpositive q).le _)
  by_cases hH : 0 < H
  · obtain ⟨α,hα,ha⟩ := exists_positive_finite_rescaling (fun q => (F q)^endpointExponent n)
      (fun q => Real.rpow_pos_of_pos (hpositive q) _)
    let a (q : κ) := α*(F q)^endpointExponent n
    have hasum : ∑ q, a q = α*H := by simp only [a,H,Finset.mul_sum]
    have hleft : (∑ q, (c*a q*F q)^((n : ℝ)⁻¹)) = (c*α)^((n : ℝ)⁻¹)*H := by
      calc
        _ = ∑ q, (c*α)^((n : ℝ)⁻¹)*(F q)^endpointExponent n := by
          apply Finset.sum_congr rfl
          intro q _
          exact weighted_endpoint_dual_power_identity hn hc.le hα.le (show 0 < F q from hpositive q)
        _ = _ := by rw [← Finset.mul_sum]
    have hdegree : weightedVisibilityDegreeBound n a = (n : ℝ)*(K*α*H)^((n : ℝ)⁻¹) := by
      unfold weightedVisibilityDegreeBound
      rw [hasum]
      congr 2
      ring
    have h := (actual_lineMeasure_kernel_holder_budget hn μ b a ha hoverlap R).2
    change (∑ q, (c*a q*F q)^((n : ℝ)⁻¹)) ≤
      ballTubeBudgetCost n C R*weightedVisibilityDegreeBound n a*T^((n : ℝ)⁻¹) at h
    rw [hleft,hdegree] at h
    have hdual : (c*α)^((n : ℝ)⁻¹)*H ≤ G*(K*α*H)^((n : ℝ)⁻¹)*T^((n : ℝ)⁻¹) := by
      convert h using 1 <;> ring
    have hout := cancel_endpoint_duality hn hc hα hH hG hK hT hdual
    have hbase : 0 ≤ G^n*K/c := div_nonneg (mul_nonneg (pow_nonneg hG _) hK) hc.le
    rw [Real.mul_rpow hbase hT] at hout
    exact hout
  · have he : H = 0 := le_antisymm (le_of_not_gt hH) hHnonneg
    change H ≤ _
    rw [he]
    exact mul_nonneg (discreteEndpointConstant_nonneg hn C R) (Real.rpow_nonneg hT _)

/-- Zero kernel values are removed only for the auxiliary positive rescaling;
the conclusion keeps the original finite family and all zero weights. -/
theorem real_discrete_lineMeasure_endpoint {n : ℕ} (hn : 2 ≤ n)
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    {κ : Type*} [Fintype κ] (b : κ → E n) {C : ℕ}
    (hoverlap : ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.closedBall (b q) 1)).card ≤ C)
    (R : ℝ) :
    (∑ q, ((lineMeasureKernel μ R (b q)).toReal)^endpointExponent n) ≤
      discreteEndpointConstant n C R * (∏ i, (μ i).real univ)^endpointExponent n := by
  let F (q : κ) := (lineMeasureKernel μ R (b q)).toReal
  let I := {q : κ // 0 < F q}
  have hoverlap' : ∀ x, (Finset.univ.filter (fun q : I => x ∈ Metric.closedBall (b q.val) 1)).card ≤ C := by
    intro x
    refine le_trans (Finset.card_le_card_of_injOn (fun q : I => q.val) ?_ ?_) (hoverlap x)
    · intro q hq
      simpa only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] using hq
    · intro q _ q' _ h
      exact Subtype.ext h
  have h := real_discrete_lineMeasure_endpoint_of_positive_kernel hn μ (fun q : I => b q.val)
    hoverlap' R (fun q => q.property)
  have hexp : 0 < endpointExponent n := by
    unfold endpointExponent
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_pos.mpr (by linarith)
  have hzero : (∑ q : {q : κ // ¬ 0 < F q}, (F q.val)^endpointExponent n) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    have hz : F q.val = 0 := le_antisymm (le_of_not_gt q.property) ENNReal.toReal_nonneg
    rw [hz,Real.zero_rpow hexp.ne']
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun q : κ => 0 < F q)
    (fun q => (F q)^endpointExponent n)
  rw [hzero,add_zero] at hsum
  change (∑ q : I, (F q.val)^endpointExponent n) ≤ _ at h
  rw [hsum] at h
  exact h

end Kakeya4.Hard.MultilinearKakeya
