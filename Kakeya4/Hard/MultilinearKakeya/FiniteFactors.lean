import Kakeya4.Hard.MultilinearKakeya.Basic

/-! Weighted finite Hölder aggregation for the local factors in CV Proposition 2.
This supplies the analytic budget step, not the geometric existence of the factors. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem sum_geometricMean_le {Q : Type*} [Fintype Q] (n : ℕ) (hn : 0 < n)
    (f : Fin n → Q → ℝ≥0∞) :
    (∑ q, ∏ i, (f i q)^((n : ℝ)⁻¹)) ≤
      ∏ i, (∑ q, f i q)^((n : ℝ)⁻¹) := by
  letI : MeasurableSpace Q := ⊤
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ∑ _i : Fin n, (n : ℝ)⁻¹ = 1 := by
    simp [hnR.ne']
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := Measure.count)
    (Finset.univ : Finset (Fin n))
    (f := f) (fun i _ => (measurable_of_countable (f i)).aemeasurable) hp
    (fun _ _ => inv_nonneg.mpr hnR.le)
  simpa only [lintegral_count, tsum_fintype] using h

/-- Per-tube budgets control arbitrary nonnegative weights, including repeated
indices and zero weights, before the geometric factors are constructed. -/
theorem weighted_factor_budget {Q : Type*} [Fintype Q] {n : ℕ} (hn : 0 < n)
    {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (w : ∀ i, ι i → ℝ≥0∞) (S : ∀ i, Q → ι i → ℝ≥0∞) (B : Fin n → ℝ≥0∞)
    (hB : ∀ i a, ∑ q, S i q a ≤ B i) :
    (∑ q, ∏ i, (∑ a, w i a * S i q a)^((n : ℝ)⁻¹)) ≤
      ∏ i, ((∑ a, w i a) * B i)^((n : ℝ)⁻¹) := by
  have hsum (i : Fin n) : (∑ q, ∑ a, w i a * S i q a) ≤ (∑ a, w i a) * B i := by
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    rw [← Finset.mul_sum]
    exact mul_le_mul_right (hB i a) _
  calc
    _ ≤ ∏ i, (∑ q, ∑ a, w i a * S i q a)^((n : ℝ)⁻¹) :=
      sum_geometricMean_le n hn _
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro i _
      exact ENNReal.rpow_le_rpow (hsum i) (by positivity)

/-- A local tuple-factor majorant feeds the weighted budget estimate. The
construction of such geometric factors is a separate, still required CV step. -/
theorem sum_local_majorant_le {Q : Type*} [Fintype Q] {n : ℕ} (hn : 0 < n)
    {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (F : Q → ℝ≥0∞) (w : ∀ i, ι i → ℝ≥0∞)
    (S : ∀ i, Q → ι i → ℝ≥0∞) (B : Fin n → ℝ≥0∞)
    (hF : ∀ q, F q ≤ ∑ a : ∀ i, ι i, ∏ i, w i (a i) * S i q (a i))
    (hB : ∀ i a, ∑ q, S i q a ≤ B i) :
    (∑ q, (F q)^((n : ℝ)⁻¹)) ≤
      ∏ i, ((∑ a, w i a) * B i)^((n : ℝ)⁻¹) := by
  have hp : 0 ≤ (n : ℝ)⁻¹ := by positivity
  calc
    _ ≤ ∑ q, ∏ i, (∑ a, w i a * S i q a)^((n : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro q _
      rw [ENNReal.prod_rpow_of_nonneg hp]
      apply ENNReal.rpow_le_rpow _ hp
      simpa only [Fintype.prod_sum] using hF q
    _ ≤ _ := weighted_factor_budget hn w S B hB

end Kakeya4.Hard.MultilinearKakeya
