import Kakeya4.Hard.MultilinearKakeya.FiniteFactors

/-! Finite nonnegative-real versions of the existing ENNReal Holder budgets.
Finiteness is proved before taking toReal, including zero inputs. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem real_sum_geometricMean_le {κ : Type*} [Fintype κ] {n : ℕ} (hn : 0 < n)
    (f : Fin n → κ → ℝ) (hf : ∀ i q, 0 ≤ f i q) :
    (∑ q, ∏ i, (f i q)^((n : ℝ)⁻¹)) ≤ ∏ i, (∑ q, f i q)^((n : ℝ)⁻¹) := by
  have hr : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have h := sum_geometricMean_le n hn (fun i q => ENNReal.ofReal (f i q))
  have hR : (∏ i : Fin n, (∑ q, ENNReal.ofReal (f i q))^((n : ℝ)⁻¹)) ≠ ⊤ :=
    ENNReal.prod_ne_top (fun i _ => ENNReal.rpow_ne_top_of_nonneg hr
      (ENNReal.sum_ne_top.mpr (fun q _ => ENNReal.ofReal_ne_top)))
  have hreal := ENNReal.toReal_mono hR h
  rw [ENNReal.toReal_sum (fun q _ => ENNReal.prod_ne_top
    (fun i _ => ENNReal.rpow_ne_top_of_nonneg hr ENNReal.ofReal_ne_top))] at hreal
  simp_rw [ENNReal.toReal_prod,← ENNReal.toReal_rpow,
    ENNReal.toReal_sum (fun q _ => ENNReal.ofReal_ne_top)] at hreal
  simpa only [ENNReal.toReal_ofReal (hf _ _)] using hreal

theorem real_sum_local_product_majorant_le {κ : Type*} [Fintype κ] {n : ℕ} (hn : 0 < n)
    {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (F : κ → ℝ) (hF : ∀ q, 0 ≤ F q)
    (w : ∀ i, ι i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (S : ∀ i, κ → ι i → ℝ) (hS : ∀ i q a, 0 ≤ S i q a)
    (B : Fin n → ℝ) (hB : ∀ i a, ∑ q, S i q a ≤ B i)
    (hlocal : ∀ q, F q ≤ ∏ i, ∑ a, w i a*S i q a) :
    (∑ q, (F q)^((n : ℝ)⁻¹)) ≤
      ∏ i, ((∑ a, w i a)*B i)^((n : ℝ)⁻¹) := by
  have hr : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hsum (i : Fin n) : (∑ q, ∑ a, w i a*S i q a) ≤ (∑ a, w i a)*B i := by
    rw [Finset.sum_comm,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hB i a) (hw i a)
  calc
    _ ≤ ∑ q, ∏ i, (∑ a, w i a*S i q a)^((n : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro q _
      rw [Real.finsetProd_rpow Finset.univ _ (fun i _ =>
        Finset.sum_nonneg (fun a _ => mul_nonneg (hw i a) (hS i q a)))]
      exact Real.rpow_le_rpow (hF q) (hlocal q) hr
    _ ≤ ∏ i, (∑ q, ∑ a, w i a*S i q a)^((n : ℝ)⁻¹) :=
      real_sum_geometricMean_le hn _ (fun i q =>
        Finset.sum_nonneg (fun a _ => mul_nonneg (hw i a) (hS i q a)))
    _ ≤ _ := Finset.prod_le_prod₀
      (fun i _ => Real.rpow_nonneg
        (Finset.sum_nonneg (fun q _ => Finset.sum_nonneg (fun a _ => mul_nonneg (hw i a) (hS i q a)))) _)
      (fun i _ => Real.rpow_le_rpow
        (Finset.sum_nonneg (fun q _ => Finset.sum_nonneg (fun a _ => mul_nonneg (hw i a) (hS i q a))))
        (hsum i) hr)

theorem real_prod_uniform_budget_rpow {n : ℕ} (hn : 0 < n)
    (W : Fin n → ℝ) (hW : ∀ i, 0 ≤ W i) {B : ℝ} (hB : 0 ≤ B) :
    (∏ i, (W i*B)^((n : ℝ)⁻¹)) = B*(∏ i, W i)^((n : ℝ)⁻¹) := by
  rw [Real.finsetProd_rpow Finset.univ _ (fun i _ => mul_nonneg (hW i) hB),
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Real.mul_rpow (Finset.prod_nonneg (fun i _ => hW i)) (pow_nonneg hB _),
    Real.pow_rpow_inv_natCast hB hn.ne']
  exact mul_comm _ _

end Kakeya4.Hard.MultilinearKakeya
