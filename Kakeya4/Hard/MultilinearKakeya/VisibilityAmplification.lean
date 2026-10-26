import Kakeya4.Hard.MultilinearKakeya.WeightedVisibility

/-! Exact n-th-power amplification of the weighted visibility construction.
Writing lambda=t^n makes the degree bound linear in t, while the small-body
bound decays as t^(-n); no asymptotic or exchanged epsilon quantifiers are used. -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace Kakeya4.Hard.MultilinearKakeya

def weightedVisibilityDegreeBound (n : ℕ) {κ : Type*} [Fintype κ] (w : κ → ℝ) : ℝ :=
  (n : ℝ)*(visibilityWeightCost n * ∑ q, w q)^((n : ℝ)⁻¹)

theorem weightedVisibilityDegreeBound_nonneg (n : ℕ) {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (hw : ∀ q, 0 ≤ w q) : 0 ≤ weightedVisibilityDegreeBound n w :=
  mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg
    (mul_nonneg (visibilityWeightCost_pos n).le (Finset.sum_nonneg (fun q _ => hw q))) _)

theorem weightedVisibilityDegreeBound_amplification {n : ℕ} (hn : 0 < n)
    {κ : Type*} [Fintype κ] (w : κ → ℝ) (hw : ∀ q, 0 ≤ w q) {t : ℝ} (ht : 0 ≤ t) :
    weightedVisibilityDegreeBound n (fun q => t^n*w q) = t*weightedVisibilityDegreeBound n w := by
  have hsum : visibilityWeightCost n * ∑ q, t^n*w q = t^n*(visibilityWeightCost n * ∑ q, w q) := by
    rw [← Finset.mul_sum]
    ring
  unfold weightedVisibilityDegreeBound
  rw [hsum,Real.mul_rpow (pow_nonneg ht n)
    (mul_nonneg (visibilityWeightCost_pos n).le (Finset.sum_nonneg (fun q _ => hw q)))]
  rw [Real.pow_rpow_inv_natCast ht hn.ne']
  ring

theorem exists_amplified_weighted_small_visibilityBody {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (w : κ → ℝ) (hw : ∀ q, 1 ≤ w q)
    {t : ℝ} (ht : 1 ≤ t) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      (P.totalDegree : ℝ) ≤ t*weightedVisibilityDegreeBound n w ∧
      ∀ q, (volume (visibilityBody (smoothDirectionalSeminorm P ε (Metric.closedBall (b q) 1)
        (isCompact_closedBall (b q) 1)))).toReal < (2*Real.sqrt n)^n / (t^n*w q) := by
  have htn : 1 ≤ t^n := one_le_pow₀ ht
  have hw' (q : κ) : 1 ≤ t^n*w q := by nlinarith [hw q]
  obtain ⟨ε,hε,P,hP,hD,hV⟩ := exists_polynomial_weighted_small_visibilityBody hn b (fun q => t^n*w q) hw'
  refine ⟨ε,hε,P,hP,?_,hV⟩
  have he := weightedVisibilityDegreeBound_amplification (by omega : 0 < n) w
    (fun q => le_trans zero_le_one (hw q)) (by linarith : 0 ≤ t)
  exact hD.trans_eq he

theorem div_pow_lt_inverse_power_of_payment {n : ℕ} (hn : 0 < n)
    {t A B C : ℝ} (ht : 0 < t) (hA : 0 < A)
    (hpay : B*(2*A)^(n-1) < C*t) :
    B/t^n < (2*(t*A))⁻¹^(n-1)*C := by
  have hp : t^n = t^(n-1)*t := by rw [← pow_succ,Nat.sub_add_cancel hn]
  have he : (2*(t*A))^(n-1) = t^(n-1)*(2*A)^(n-1) := by
    rw [← mul_pow]
    congr 1
    ring
  have hpos : 0 < (2*(t*A))^(n-1) := pow_pos (by positivity) _
  have h : B/t^n < C/(2*(t*A))^(n-1) := by
    apply (div_lt_div_iff₀ (pow_pos ht _) hpos).mpr
    rw [hp,he]
    have hm := mul_lt_mul_of_pos_left hpay (pow_pos ht (n-1))
    nlinarith
  simpa only [inv_pow,div_eq_mul_inv,mul_comm] using h

end Kakeya4.Hard.MultilinearKakeya
