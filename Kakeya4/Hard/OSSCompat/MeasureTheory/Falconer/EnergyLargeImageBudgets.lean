






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.EightValueMassTransport

/-! Uniform real-power budgets and actual target-cover transport for energy input. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem exists_small_scaled_rpow_budget {a b : ℝ} (hba : b < a)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → (A*r)^a ≤ B*r^b := by
  let q := B/A^a
  have hq : 0 < q := div_pos hB (Real.rpow_pos_of_pos hA _)
  let r₀ := min 1 (q^(1/(a-b)))
  refine ⟨r₀,lt_min zero_lt_one (Real.rpow_pos_of_pos hq _),min_le_left _ _,?_⟩
  intro r hr hrr
  have hp := Real.rpow_le_rpow hr.le (hrr.trans (min_le_right _ _)) (sub_pos.mpr hba).le
  have heq : (q^(1/(a-b)))^(a-b) = q := by
    rw [← Real.rpow_mul hq.le,div_mul_cancel₀ _ (sub_pos.mpr hba).ne',Real.rpow_one]
  rw [heq] at hp
  calc
    _ = A^a*r^(a-b)*r^b := by rw [Real.mul_rpow hA.le hr.le,mul_assoc,← Real.rpow_add hr]; congr 1; congr 1; ring
    _ ≤ A^a*q*r^b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = _ := by dsimp [q]; field_simp [ne_of_gt (Real.rpow_pos_of_pos hA a)]

theorem eight_noisy_cover_transfer {ι : Type*} (c : ι → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (w u : Fin 8 → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hu : ∀ i, |u i| ≤ 1)
    (hV : eightBilinearValue w ∈ ⋃ i, closedBall (c i) r) :
    eightBilinearValue (fun i ↦ noisyHalf r (w i) (u i)) ∈ ⋃ i, closedBall (c i/4) (9*r) := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp hV
  apply mem_iUnion.mpr
  refine ⟨i,?_⟩
  rw [mem_closedBall,Real.dist_eq] at hi ⊢
  have hn := eight_bilinear_noisyHalf_error w u hr hr1 hw hu
  have he : eightBilinearValue (fun i ↦ noisyHalf r (w i) (u i))-c i/4 =
      (eightBilinearValue (fun i ↦ noisyHalf r (w i) (u i))-eightBilinearValue w/4)+
        (eightBilinearValue w-c i)/4 := by ring
  rw [he]
  have hq : |(eightBilinearValue w-c i)/4| ≤ r/4 := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 4)]
    exact div_le_div_of_nonneg_right hi (by norm_num)
  exact (abs_add_le _ _).trans (by linarith)

#print axioms exists_small_scaled_rpow_budget
#print axioms eight_noisy_cover_transfer
end OAI.Falconer
