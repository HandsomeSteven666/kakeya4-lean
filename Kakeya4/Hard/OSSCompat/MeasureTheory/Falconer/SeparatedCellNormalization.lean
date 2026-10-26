






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.ScaleSeparationBudgets
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Uniform geometry for the fixed-grid separation route: a common positive
similarity puts each far pair of small cells in the same canonical unit root,
with a fixed separation. The similarity scale has a uniform lower bound.
This does not assert the still-needed global product-cell decomposition. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem separated_cell_pair_normalization (u v : Space 2)
    (hd : 0 < dist u v) (hdiam : dist u v ≤ 4) :
    ∃ (a : ℝ) (ha : 0 < a), 1/16 ≤ a ∧ ∃ center : Space 2,
      (∀ z ∈ closedBall u (dist u v/8),
        radialZoom a ha.ne' center z ∈ (centeredUnitCube 2).carrier) ∧
      (∀ x ∈ closedBall v (dist u v/8),
        radialZoom a ha.ne' center x ∈ (centeredUnitCube 2).carrier) ∧
      (∀ z ∈ closedBall u (dist u v/8), ∀ x ∈ closedBall v (dist u v/8),
        1/8 ≤ dist (radialZoom a ha.ne' center z)
          (radialZoom a ha.ne' center x)) := by
  let d := dist u v
  let a := 1/(4*d)
  let center := midpoint ℝ u v
  have ha : 0 < a := by dsimp [a,d]; positivity
  have haLower : 1/16 ≤ a := by
    dsimp [a]
    apply (le_div_iff₀ (by dsimp [d]; positivity : 0 < 4*d)).mpr
    dsimp [d]
    linarith
  have huc : dist u center = d/2 := by
    dsimp [center,d]
    rw [dist_left_midpoint]
    norm_num
    ring
  have hvc : dist v center = d/2 := by
    dsimp [center,d]
    rw [dist_right_midpoint]
    norm_num
    ring
  have hroot (w z : Space 2) (hw : dist w center = d/2) (hz : dist z w ≤ d/8) :
      radialZoom a ha.ne' center z ∈ (centeredUnitCube 2).carrier := by
    apply mem_centeredUnitCube_of_norm
    rw [radialZoom_norm ha,← dist_eq_norm]
    have hzc : dist z center ≤ d/8+d/2 := (dist_triangle z w center).trans
      (by rw [hw]; linarith)
    calc
      a*dist z center ≤ a*(d/8+d/2) := mul_le_mul_of_nonneg_left hzc ha.le
      _ = 5/32 := by dsimp [a,d]; field_simp [ne_of_gt hd]; ring
      _ ≤ _ := by norm_num
  refine ⟨a,ha,haLower,center,fun z hz => hroot u z huc hz,
    fun x hx => hroot v x hvc hx,?_⟩
  intro z hz x hx
  have hchain : d ≤ dist z u+dist z x+dist x v := by
    calc
      d ≤ dist u z+dist z v := dist_triangle u z v
      _ ≤ dist u z+(dist z x+dist x v) := by have := dist_triangle z x v; linarith
      _ = _ := by rw [dist_comm u z]; ring
  have hdz : dist z u ≤ d/8 := hz
  have hdx : dist x v ≤ d/8 := hx
  rw [dist_eq_norm,norm_radialZoom_sub ha,← dist_eq_norm]
  change 1/8 ≤ (1/(4*d))*dist z x
  rw [show (1/(4*d))*dist z x = dist z x/(4*d) by ring]
  apply (le_div_iff₀ (by dsimp [d]; positivity : 0 < 4*d)).mpr
  linarith

#print axioms separated_cell_pair_normalization
end OAI.Falconer
