import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Absorbing fixed constants into a strictly smaller positive power -/

noncomputable section

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- A fixed nonnegative coefficient is absorbed uniformly before all input laws. -/
theorem exists_small_scale_power_bound {C a τ : ℝ} (hC : 0 ≤ C) (hgap : τ < a) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      C*r^a ≤ (2:ℝ)^(-τ)*r^τ := by
  let q := (2:ℝ)^(-τ)/(C+1)
  have hq : 0 < q := div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)
  let r₀ := min 1 (q^(1/(a-τ)))
  have hr₀ : 0 < r₀ := lt_min (by norm_num) (Real.rpow_pos_of_pos hq _)
  refine ⟨r₀,hr₀,min_le_left _ _,?_⟩
  intro r hr hrr
  have hp : r^(a-τ) ≤ q := by
    have hb : r ≤ q^(1/(a-τ)) := hrr.trans (min_le_right _ _)
    have h := Real.rpow_le_rpow hr.le hb (by linarith : 0 ≤ a-τ)
    have he : (q^(1/(a-τ)))^(a-τ) = q := by
      rw [← Real.rpow_mul hq.le, div_mul_cancel₀ _ (by linarith : a-τ ≠ 0), Real.rpow_one]
    exact h.trans_eq he
  have hc : C*q ≤ (2:ℝ)^(-τ) := by
    dsimp [q]
    have hd : C/(C+1) ≤ 1 := (div_le_one (by linarith : 0 < C+1)).mpr (by linarith)
    have h := mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-τ))
    convert h using 1 <;> ring
  have hcoef : C*r^(a-τ) ≤ (2:ℝ)^(-τ) := (mul_le_mul_of_nonneg_left hp hC).trans hc
  rw [show a = (a-τ)+τ by ring, Real.rpow_add hr]
  nlinarith [Real.rpow_pos_of_pos hr τ]

end Kakeya4.Hard.MultiplicativeConvolution
