import OAI.MeasureTheory.Falconer.FlatteningIndicatorEstimate
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Finite squared-integral selection with explicit cardinality loss. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open scoped ENNReal BigOperators

theorem fin_sum_sq_le_card_mul_sum_sq {n : ℕ} (a : Fin n → ℝ≥0∞) :
    (∑ i, a i)^2 ≤ (n : ℝ≥0∞) * ∑ i, a i ^ 2 := by
  let : MeasurableSpace (Fin n) := ⊤
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure (Fin n))
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    (measurable_of_countable a).aemeasurable
    (show AEMeasurable (fun _ : Fin n ↦ (1 : ℝ≥0∞)) Measure.count from aemeasurable_const)
  simp only [Pi.mul_apply,mul_one,ENNReal.rpow_two,
    lintegral_count,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at h
  have h2 := pow_le_pow_left' h 2
  have he (b : ℝ≥0∞) : (b ^ (1/(2:ℝ)))^(2:ℕ) = b := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    norm_num
  rw [mul_pow,he,he] at h2
  simpa only [one_pow,mul_one,mul_comm] using h2

theorem lintegral_fin_sum_sq_le {n : ℕ} (F : Fin n → ℝ → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) :
    (∫⁻ x, (∑ i, F i x)^2) ≤ (n : ℝ≥0∞) * ∑ i, ∫⁻ x, F i x ^ 2 := by
  calc
    _ ≤ ∫⁻ x, (n : ℝ≥0∞) * ∑ i, F i x ^ 2 :=
      lintegral_mono (fun x ↦ fin_sum_sq_le_card_mul_sum_sq (fun i ↦ F i x))
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_finsetSum _ (fun i _ ↦ (hF i).pow_const 2)]

theorem exists_fin_large_sq_integral {n : ℕ} (hn : 0 < n) (h : ℝ → ℝ≥0∞)
    (F : Fin n → ℝ → ℝ≥0∞) (hF : ∀ i, Measurable (F i))
    (hbound : ∀ x, h x ≤ ∑ i, F i x) :
    ∃ i : Fin n, (∫⁻ x, h x ^ 2) ≤ (n : ℝ≥0∞)^2 * ∫⁻ x, F i x ^ 2 := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n ↦ ∫⁻ x, F i x ^ 2) Finset.univ_nonempty
  refine ⟨i,?_⟩
  calc
    _ ≤ ∫⁻ x, (∑ i, F i x)^2 := lintegral_mono (fun x ↦ pow_le_pow_left' (hbound x) 2)
    _ ≤ (n : ℝ≥0∞) * ∑ j, ∫⁻ x, F j x ^ 2 := lintegral_fin_sum_sq_le F hF
    _ ≤ (n : ℝ≥0∞) * ∑ _ : Fin n, ∫⁻ x, F i x ^ 2 := by
      exact mul_le_mul_right (Finset.sum_le_sum (fun j _ ↦ hmax j (Finset.mem_univ j))) _
    _ = _ := by simp [pow_two,mul_assoc]

#print axioms fin_sum_sq_le_card_mul_sum_sq
#print axioms lintegral_fin_sum_sq_le
#print axioms exists_fin_large_sq_integral
end OAI.Falconer
