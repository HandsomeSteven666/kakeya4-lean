import Kakeya4.Hard.MultilinearKakeya.Basic

/-! Euclidean normal-coordinate control for actual full-line tubes in the plane. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace InnerProductSpace

namespace Kakeya4.Hard.MultilinearKakeya

def perpendicular (v : E 2) : E 2 := WithLp.toLp 2 ![-v 1, v 0]

theorem norm_perpendicular (v : E 2) : ‖perpendicular v‖ = ‖v‖ := by
  simp [EuclideanSpace.norm_eq, perpendicular, Fin.sum_univ_two, add_comm]

theorem inner_perpendicular_self (v : E 2) : ⟪perpendicular v, v⟫_ℝ = 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, perpendicular,
    Fin.sum_univ_two]
  ring

/-- The signed normal displacement is constant along the entire affine line. -/
theorem inner_perpendicular_line_displacement (L : Line 2) (x : E 2) (t : ℝ) :
    ⟪perpendicular L.direction, x - (L.anchor + t • L.direction)⟫_ℝ =
      ⟪perpendicular L.direction, x - L.anchor⟫_ℝ := by
  simp only [inner_sub_right, inner_add_right, inner_smul_right,
    inner_perpendicular_self, mul_zero, add_zero]

theorem abs_normal_le_infDist (L : Line 2) (x : E 2) :
    |⟪perpendicular L.direction, x - L.anchor⟫_ℝ| ≤ Metric.infDist x L.carrier := by
  apply (Metric.le_infDist L.carrier_nonempty).mpr
  rintro y ⟨t, rfl⟩
  calc
    _ = |⟪perpendicular L.direction, x - (L.anchor + t • L.direction)⟫_ℝ| :=
      congrArg abs (inner_perpendicular_line_displacement L x t).symm
    _ ≤ ‖perpendicular L.direction‖ * ‖x - (L.anchor + t • L.direction)‖ :=
      abs_real_inner_le_norm _ _
    _ = _ := by rw [norm_perpendicular, L.norm_direction, one_mul, dist_eq_norm]

/-- A true Euclidean tube lies in its normal-coordinate strip. -/
theorem tube_subset_normalStrip (L : Line 2) (r : ℝ) :
    L.tube r ⊆ {x | |⟪perpendicular L.direction, x - L.anchor⟫_ℝ| ≤ r} := by
  intro x hx
  exact (abs_normal_le_infDist L x).trans hx

/-- A linear map taking a set into two strips pays exactly its determinant.
The singular case needs no inverse and remains valid for infinite source volume. -/
theorem determinant_mul_volume_le_rectangle (A : Matrix (Fin 2) (Fin 2) ℝ)
    (S : Set (Fin 2 → ℝ)) (c : Fin 2 → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hS : ∀ x ∈ S, ∀ i, |A.mulVec x i - c i| ≤ r) :
    ENNReal.ofReal |A.det| * volume S ≤ ENNReal.ofReal (4*r^2) := by
  let B : Set (Fin 2 → ℝ) := Icc (fun i => c i - r) (fun i => c i + r)
  have hsub : (Matrix.toLin' A) '' S ⊆ B := by
    rintro y ⟨x,hx,rfl⟩
    constructor <;> intro i
    · have h := (abs_le.mp (hS x hx i)).1
      change c i - r ≤ A.mulVec x i
      linarith
    · have h := (abs_le.mp (hS x hx i)).2
      change A.mulVec x i ≤ c i + r
      linarith
  calc
    _ = volume ((Matrix.toLin' A) '' S) := by
      rw [volume.addHaar_image_linearMap, LinearMap.det_toLin']
    _ ≤ volume B := measure_mono hsub
    _ = _ := by
      change volume (Icc (fun i : Fin 2 => c i-r) (fun i => c i+r)) = _
      rw [Real.volume_Icc_pi, Fin.prod_univ_two]
      have hd (i : Fin 2) : (c i+r)-(c i-r) = 2*r := by ring
      simp only [hd]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)]
      congr 1
      ring

end Kakeya4.Hard.MultilinearKakeya
