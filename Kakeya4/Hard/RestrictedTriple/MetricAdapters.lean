import Kakeya4.Hard.RestrictedTriple.ExpansionTransport

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem planeCoordinates_dist_le (x y : Plane) :
    dist (planeCoordinates x) (planeCoordinates y) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact PiLp.dist_apply_le x y i

theorem plane_dist_le_two_coordinates (x y : Plane) :
    dist x y ≤ 2*dist (planeCoordinates x) (planeCoordinates y) := by
  have hex : x-y = EuclideanSpace.single 0 (x 0-y 0) + EuclideanSpace.single 1 (x 1-y 1) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  have h0 := dist_le_pi_dist (planeCoordinates x) (planeCoordinates y) (0 : Fin 2)
  have h1 := dist_le_pi_dist (planeCoordinates x) (planeCoordinates y) (1 : Fin 2)
  simp only [planeCoordinates, Real.dist_eq] at h0 h1
  rw [dist_eq_norm, hex]
  have hh := norm_add_le (EuclideanSpace.single (0 : Fin 2) (x 0-y 0))
    (EuclideanSpace.single (1 : Fin 2) (x 1-y 1))
  simp only [EuclideanSpace.norm_single, Real.norm_eq_abs] at hh
  linarith

theorem separated_coordinates_implies_Euclidean {P : Set Plane} {p : ℝ} (hp : 0 ≤ p)
    (hsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' P)) :
    ∀ x ∈ P, ∀ y ∈ P, x ≠ y → p < dist x y := by
  intro x hx y hy hne
  have hh := hsep (show planeCoordinates x ∈ planeCoordinates '' P from ⟨x,hx,rfl⟩)
    (show planeCoordinates y ∈ planeCoordinates '' P from ⟨y,hy,rfl⟩)
    (fun heq ↦ hne (planeCoordinates_injective heq))
  have hreal : p < dist (planeCoordinates x) (planeCoordinates y) := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp).mp
    simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hp, edist_dist] using hh
  exact hreal.trans_le (planeCoordinates_dist_le x y)

theorem closedBall_local_count_of_ADUpperBound {A P : Set Plane} {p C : ℝ}
    (hp : 0 < p) (hAD : ADUpperBound p C A) (hPA : P ⊆ A)
    (hsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' P))
    (z : Plane) {w : ℝ} (hw : p ≤ w) :
    ((P ∩ closedBall z w).encard : ℝ≥0∞) ≤ ENNReal.ofReal (2*C*w/p) := by
  have hwpos : 0 < w := hp.trans_le hw
  have hsub : P ∩ closedBall z w ⊆ P ∩ ball z (2*w) := by
    intro x hx
    exact ⟨hx.1, by rw [mem_ball]; have hh := mem_closedBall.mp hx.2; linarith⟩
  have hh := (ENat.toENNReal_mono (encard_le_encard hsub)).trans
    (separated_local_count_of_ADUpperBound hp hAD hPA hsep z (show p ≤ 2*w by linarith))
  have heq : C*(2*w)/p = 2*C*w/p := by ring
  rwa [heq] at hh

theorem unitSquare_norm_le_two {x : Plane} (hx : x ∈ unitSquare) : ‖x‖ ≤ 2 := by
  have hh := plane_dist_le_two_coordinates x 0
  have hc : dist (planeCoordinates x) (planeCoordinates 0) ≤ 1 := by
    apply (dist_pi_le_iff (by norm_num)).mpr
    intro i
    simpa [planeCoordinates, Real.dist_eq, abs_of_nonneg (hx i).1] using (hx i).2
  simpa only [dist_zero_right] using hh.trans (by linarith)

def halfPlane (x : Plane) : Plane := (1/2 : ℝ) • x
def halfTriple (t : Triple) : Triple := (halfPlane t.1, halfPlane t.2.1, halfPlane t.2.2)

theorem halfPlane_norm_le_one {x : Plane} (hx : x ∈ unitSquare) : ‖halfPlane x‖ ≤ 1 := by
  have hh := unitSquare_norm_le_two hx
  simp only [halfPlane, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  linarith

theorem dotDifference_halfTriple (t : Triple) : dotDifference (halfTriple t) = dotDifference t/4 := by
  simp only [dotDifference, halfTriple, halfPlane, ← smul_sub, inner_smul_left, inner_smul_right]
  simp
  ring

theorem halfPlane_dist (x y : Plane) : dist (halfPlane x) (halfPlane y) = dist x y/2 := by
  simp only [halfPlane, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
  norm_num
  ring

theorem halfPlane_injective : Function.Injective halfPlane := by
  intro x y h
  have hh := congrArg (fun v : Plane ↦ (2:ℝ) • v) h
  simpa [halfPlane, smul_smul] using hh

theorem halfPlane_separated {P : Set Plane} {p : ℝ} (hp : 0 ≤ p)
    (hsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' P)) :
    ∀ x ∈ halfPlane '' P, ∀ y ∈ halfPlane '' P, x ≠ y → p/2 < dist x y := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hne
  have hh := separated_coordinates_implies_Euclidean hp hsep x hx y hy (fun h ↦ hne (congrArg halfPlane h))
  rw [halfPlane_dist]
  linarith

/-- The normalized finite set satisfies a closed-ball Katz--Tao bound at p/2,
with exactly twice the original AD coefficient; no lower regularity is used. -/
theorem halfPlane_closedBall_local_count {A P : Set Plane} {p C : ℝ}
    (hp : 0 < p) (hAD : ADUpperBound p C A) (hPA : P ⊆ A)
    (hsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' P))
    (z : Plane) {w : ℝ} (hw : p/2 ≤ w) :
    (((halfPlane '' P) ∩ closedBall z w).encard : ℝ≥0∞) ≤
      ENNReal.ofReal (2*C*w/(p/2)) := by
  have hhalf : halfPlane ((2:ℝ) • z) = z := by simp [halfPlane, smul_smul]
  have hd (x : Plane) : dist (halfPlane x) z = dist x ((2:ℝ) • z)/2 := by
    calc
      _ = dist (halfPlane x) (halfPlane ((2:ℝ) • z)) := by rw [hhalf]
      _ = _ := halfPlane_dist x ((2:ℝ) • z)
  have himg : halfPlane '' (P ∩ closedBall ((2:ℝ) • z) (2*w)) =
      (halfPlane '' P) ∩ closedBall z w := by
    ext y
    constructor
    · rintro ⟨x,⟨hx,hxb⟩,rfl⟩
      refine ⟨⟨x,hx,rfl⟩, ?_⟩
      rw [mem_closedBall, hd]
      have hh := mem_closedBall.mp hxb
      linarith
    · rintro ⟨⟨x,hx,rfl⟩,hxb⟩
      refine ⟨x,⟨hx, ?_⟩,rfl⟩
      rw [mem_closedBall] at hxb ⊢
      rw [hd] at hxb
      linarith
  rw [← himg, halfPlane_injective.encard_image]
  have hh := closedBall_local_count_of_ADUpperBound hp hAD hPA hsep ((2:ℝ) • z)
    (show p ≤ 2*w by linarith)
  have heq : 2*C*(2*w)/p = 2*C*w/(p/2) := by ring
  rwa [heq] at hh

end Kakeya4.Hard.RestrictedTriple
