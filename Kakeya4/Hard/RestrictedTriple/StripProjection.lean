import Kakeya4.Hard.RestrictedTriple.UniformSequentialTwoEnds

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem plane_inner_coordinates (x y : Plane) : inner ℝ x y = x 0*y 0+x 1*y 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
  ring

theorem unit_direction_inner_decomposition (a v e : Plane) (he : ‖e‖ = 1) :
    inner ℝ a v = inner ℝ a e*inner ℝ v e+
      inner ℝ a (quarterTurn e)*inner ℝ v (quarterTurn e) := by
  have hu : (e 0)^2+(e 1)^2 = 1 := by rw [← plane_norm_sq_coordinates,he]; norm_num
  rw [plane_inner_coordinates a v,plane_inner_coordinates a e,plane_inner_coordinates v e,
    inner_quarterTurn_eq_cross2,inner_quarterTurn_eq_cross2]
  unfold cross2
  calc
    _ = (a 0*v 0+a 1*v 1)*((e 0)^2+(e 1)^2) := by rw [hu]; ring
    _ = _ := by ring

theorem norm_le_unit_inner_pair (v e : Plane) (he : ‖e‖ = 1) :
    ‖v‖ ≤ |inner ℝ v e|+|inner ℝ v (quarterTurn e)| := by
  have hh := planar_lagrange_identity v e
  rw [he] at hh
  have hd : inner ℝ v e = v 0*e 0+v 1*e 1 := plane_inner_coordinates v e
  have hn : inner ℝ v (quarterTurn e) = -cross2 v e := inner_quarterTurn_eq_cross2 v e
  have hprod := mul_nonneg (abs_nonneg (inner ℝ v e)) (abs_nonneg (inner ℝ v (quarterTurn e)))
  have hs1 := sq_abs (inner ℝ v e)
  have hs2 := sq_abs (inner ℝ v (quarterTurn e))
  rw [← hd] at hh
  have hnormalSq : (inner ℝ v (quarterTurn e))^2 = (cross2 v e)^2 := by rw [hn]; ring
  nlinarith [norm_nonneg v,abs_nonneg (inner ℝ v e),abs_nonneg (inner ℝ v (quarterTurn e))]

theorem strip_normal_difference_le {t : ℝ} (ht : 0 ≤ t) (L : AffineLine) (x y : Plane)
    (hx : x ∈ lineNeighborhood t L) (hy : y ∈ lineNeighborhood t L) :
    |inner ℝ (x-y) (quarterTurn L.direction)| ≤ 2*t := by
  rw [← innerStrip_eq_lineNeighborhood ht] at hx hy
  change |inner ℝ (x-L.anchor) (quarterTurn L.direction)| ≤ t at hx
  change |inner ℝ (y-L.anchor) (quarterTurn L.direction)| ≤ t at hy
  have heq : x-y = (x-L.anchor)-(y-L.anchor) := by module
  rw [heq,inner_sub_left]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2,(abs_le.mp hy).1,(abs_le.mp hy).2]

/-- Quantitative projection lower bound on one actual strip, before any separated-point choice. -/
theorem strip_projection_lower {t : ℝ} (ht : 0 ≤ t) (L : AffineLine) (a x y : Plane)
    (hx : x ∈ lineNeighborhood t L) (hy : y ∈ lineNeighborhood t L) :
    |inner ℝ a L.direction| * dist x y ≤ |inner ℝ a (x-y)|+4*t*‖a‖ := by
  let v := x-y
  let e := L.direction
  let n := quarterTurn e
  have hN : |inner ℝ v n| ≤ 2*t := strip_normal_difference_le ht L x y hx hy
  have hA : |inner ℝ a e| ≤ ‖a‖ := by
    simpa only [L.direction_unit,mul_one] using abs_real_inner_le_norm a L.direction
  have hC : |inner ℝ a n| ≤ ‖a‖ := by
    simpa only [quarterTurn_norm,L.direction_unit,mul_one] using abs_real_inner_le_norm a (quarterTurn L.direction)
  have hdec : inner ℝ a v = inner ℝ a e*inner ℝ v e+inner ℝ a n*inner ℝ v n :=
    unit_direction_inner_decomposition a v e L.direction_unit
  have htri : |inner ℝ a e| * |inner ℝ v e| ≤ |inner ℝ a v|+|inner ℝ a n| * |inner ℝ v n| := by
    have hu := abs_le.mp (show |inner ℝ a v| ≤ |inner ℝ a v| from le_rfl)
    have hn := abs_le.mp (show |inner ℝ a n*inner ℝ v n| ≤ |inner ℝ a n*inner ℝ v n| from le_rfl)
    have hh : |inner ℝ a e*inner ℝ v e| ≤ |inner ℝ a v|+|inner ℝ a n*inner ℝ v n| := by
      apply abs_le.mpr
      constructor <;> linarith
    simpa only [abs_mul] using hh
  have herror : |inner ℝ a n| * |inner ℝ v n| ≤ ‖a‖*(2*t) := by gcongr
  have hnorm := norm_le_unit_inner_pair v e L.direction_unit
  have hT := mul_le_mul_of_nonneg_left hnorm (abs_nonneg (inner ℝ a e))
  have hNN := mul_le_mul_of_nonneg_left hN (abs_nonneg (inner ℝ a e))
  have hAA := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2*t by positivity)
  change |inner ℝ a e| * ‖v‖ ≤ |inner ℝ a v|+4*t*‖a‖
  nlinarith

/-- On a separated subset, projection is co-Lipschitz once the tangential component
dominates the strip error. This is the elementary growth mechanism of Lemma8.13 Step1. -/
theorem strip_projection_colipschitz {t : ℝ} (ht : 0 ≤ t) (L : AffineLine) (a x y : Plane)
    (ha : ‖a‖ ≤ 1) (hA : 0 < |inner ℝ a L.direction|)
    (hx : x ∈ lineNeighborhood t L) (hy : y ∈ lineNeighborhood t L)
    (hsep : 8*t/|inner ℝ a L.direction| ≤ dist x y) :
    (|inner ℝ a L.direction|/2)*dist x y ≤ |inner ℝ a (x-y)| := by
  have hh := strip_projection_lower ht L a x y hx hy
  have hwide : 8*t ≤ |inner ℝ a L.direction| * dist x y := by
    have hh := (div_le_iff₀ hA).mp hsep
    nlinarith
  have herr := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4*t by positivity)
  nlinarith

end Kakeya4.Hard.RestrictedTriple
