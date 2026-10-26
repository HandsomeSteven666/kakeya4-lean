import Kakeya4.Hard.MultilinearKakeya.SimultaneousVisibility

/-! Dimension-only payment for reciprocal visibility targets. Weights at least
one absorb the rounding cost, giving degree O_n((sum weights)^(1/n)) on
arbitrary finite families of unit balls, with one actual polynomial and epsilon. -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace Kakeya4.Hard.MultilinearKakeya

def visibilityWeightCost (n : ℕ) : ℝ :=
  ((volume (Metric.closedBall (0 : E n) 1)).toReal / spatialTestVolumeFactor n + 1) * shapeColourCount n

theorem visibilityWeightCost_pos (n : ℕ) : 0 < visibilityWeightCost n := by
  have hcol : 0 < shapeColourCount n := by dsimp [shapeColourCount,operatorColourCount]; omega
  apply mul_pos _ (by exact_mod_cast hcol)
  exact add_pos_of_nonneg_of_pos (div_nonneg ENNReal.toReal_nonneg (spatialTestVolumeFactor_pos n).le) zero_lt_one

theorem visibilityIndexBudget_inv_weights_le {n : ℕ} {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (hw : ∀ q, 1 ≤ w q) :
    (visibilityIndexBudget n (fun q => (w q)⁻¹) : ℝ) ≤ visibilityWeightCost n * ∑ q, w q := by
  classical
  let V := (volume (Metric.closedBall (0 : E n) 1)).toReal
  let F := spatialTestVolumeFactor n
  have hF : 0 < F := spatialTestVolumeFactor_pos n
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hq (q : κ) : V/(F*(w q)⁻¹) = (V/F)*w q := by
    have hwpos : 0 < w q := lt_of_lt_of_le zero_lt_one (hw q)
    field_simp [hF.ne',hwpos.ne']
  simp only [visibilityIndexBudget,Nat.cast_sum,Nat.cast_mul]
  change (∑ q, (⌈V/(F*(w q)⁻¹)⌉₊ : ℝ)*(shapeColourCount n : ℝ)) ≤
    ((V/F+1)*(shapeColourCount n : ℝ))*∑ q, w q
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  have hwpos : 0 < w q := lt_of_lt_of_le zero_lt_one (hw q)
  have hceil := (Nat.ceil_lt_add_one (div_nonneg hV (mul_pos hF (inv_pos.mpr hwpos)).le)).le
  rw [hq q] at hceil
  have hc : (⌈V/(F*(w q)⁻¹)⌉₊ : ℝ) ≤ (V/F+1)*w q := by
    rw [hq q]
    nlinarith [hw q]
  calc
    _ ≤ ((V/F+1)*w q)*(shapeColourCount n : ℝ) := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
    _ = _ := by ring

theorem exists_polynomial_weighted_small_visibilityBody {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (w : κ → ℝ) (hw : ∀ q, 1 ≤ w q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      (P.totalDegree : ℝ) ≤ (n : ℝ)*(visibilityWeightCost n * ∑ q, w q)^((n : ℝ)⁻¹) ∧
      ∀ q, (volume (visibilityBody (smoothDirectionalSeminorm P ε (Metric.closedBall (b q) 1)
        (isCompact_closedBall (b q) 1)))).toReal < (2*Real.sqrt n)^n / w q := by
  obtain ⟨ε,hε,P,hP,hD,hV⟩ := exists_polynomial_simultaneous_small_visibilityBody_quantitative hn b
    (fun q => (w q)⁻¹) (fun q => inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hw q)))
  refine ⟨ε,hε,P,hP,?_,?_⟩
  · apply hD.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (visibilityIndexBudget_inv_weights_le w hw)
      (inv_nonneg.mpr (Nat.cast_nonneg n))
  · intro q
    simpa only [div_eq_mul_inv] using hV q

end Kakeya4.Hard.MultilinearKakeya
