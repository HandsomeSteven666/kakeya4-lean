import Kakeya4.Hard.RestrictedTriple.RadialReadyInput

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem normalize_distance_weighted (v u : Plane) (hu : u ≠ 0) :
    ‖v‖*dist (NormedSpace.normalize v) (NormedSpace.normalize u) ≤ 2*dist v u := by
  have hid : ‖v‖ • (NormedSpace.normalize v-NormedSpace.normalize u) =
      (v-u)+(‖u‖-‖v‖) • NormedSpace.normalize u := by
    rw [smul_sub,sub_smul,NormedSpace.norm_smul_normalize,NormedSpace.norm_smul_normalize]
    module
  have hh := norm_add_le (v-u) ((‖u‖-‖v‖) • NormedSpace.normalize u)
  rw [← hid,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,NormedSpace.norm_normalize hu,
    abs_of_nonneg (norm_nonneg v),mul_one] at hh
  have hnorm : |‖u‖-‖v‖| ≤ ‖v-u‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le u v
  rw [← dist_eq_norm,← dist_eq_norm] at hh
  rw [← dist_eq_norm] at hnorm
  linarith

theorem normalize_distance_le_four {v u : Plane} (hv : 1/2 ≤ ‖v‖) (hu : u ≠ 0) :
    dist (NormedSpace.normalize v) (NormedSpace.normalize u) ≤ 4*dist v u := by
  have hh := normalize_distance_weighted v u hu
  have hlo := mul_le_mul_of_nonneg_right hv
    (dist_nonneg : 0 ≤ dist (NormedSpace.normalize v) (NormedSpace.normalize u))
  linarith

/-- The actual normalized endpoint directions lie in one fixed cap. -/
theorem occupied_radial_cap (Q : Finset Triple) (q : Triple) (hq : q ∈ Q)
    (hgeom : standardTripleGeometry Q) :
    ‖radialProjection q.2.2 q.2.1‖ = 1 ∧
      ∀ x ∈ activeTripleClasses Q 1, ‖radialProjection q.2.2 x‖ = 1 ∧
        1/2 ≤ inner ℝ (radialProjection q.2.2 x) (radialProjection q.2.2 q.2.1) := by
  have hqdist : 1/2 ≤ ‖q.2.1-q.2.2‖ := by
    simpa only [dist_eq_norm] using (hgeom.2 q hq q hq).2.2.2
  have hqne : q.2.1-q.2.2 ≠ 0 := by intro hz; rw [hz,norm_zero] at hqdist; norm_num at hqdist
  have he : ‖radialProjection q.2.2 q.2.1‖ = 1 := NormedSpace.norm_normalize hqne
  refine ⟨he,?_⟩
  intro x hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  have hvdist : 1/2 ≤ ‖v.2.1-q.2.2‖ := by
    simpa only [dist_eq_norm] using (hgeom.2 v hv q hq).2.2.2
  have hvne : v.2.1-q.2.2 ≠ 0 := by intro hz; rw [hz,norm_zero] at hvdist; norm_num at hvdist
  have hunit : ‖radialProjection q.2.2 v.2.1‖ = 1 := NormedSpace.norm_normalize hvne
  refine ⟨hunit,?_⟩
  have hds := normalize_distance_le_four hvdist hqne
  have hdiff : dist (v.2.1-q.2.2) (q.2.1-q.2.2) = dist v.2.1 q.2.1 := by simp
  rw [hdiff] at hds
  have hclose : dist (radialProjection q.2.2 v.2.1) (radialProjection q.2.2 q.2.1) ≤ 1 := by
    change dist (NormedSpace.normalize _) (NormedSpace.normalize _) ≤ 1
    linarith [(hgeom.2 v hv q hq).2.1]
  have hs := norm_sub_sq_real (radialProjection q.2.2 v.2.1) (radialProjection q.2.2 q.2.1)
  rw [hunit,he,← dist_eq_norm] at hs
  nlinarith [dist_nonneg (x := radialProjection q.2.2 v.2.1) (y := radialProjection q.2.2 q.2.1)]

/-- A one-dimensional chart controls distances on this unit cap. -/
theorem unit_cap_chart_distance (x y e : Plane) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (he : ‖e‖ = 1) (hxe : 1/2 ≤ inner ℝ x e) (hye : 1/2 ≤ inner ℝ y e) :
    dist x y ≤ 3*|inner ℝ (x-y) (quarterTurn e)| := by
  let A := inner ℝ x e
  let B := inner ℝ y e
  let C := inner ℝ x (quarterTurn e)
  let D := inner ℝ y (quarterTurn e)
  have hsum : 1 ≤ A+B := by dsimp [A,B]; linarith
  have hC : |C| ≤ 1 := by
    simpa only [C,hx,quarterTurn_norm,he,mul_one] using abs_real_inner_le_norm x (quarterTurn e)
  have hD : |D| ≤ 1 := by
    simpa only [D,hy,quarterTurn_norm,he,mul_one] using abs_real_inner_le_norm y (quarterTurn e)
  have hCs : |C+D| ≤ 2 := (abs_add_le C D).trans (by linarith)
  have hxx := unit_direction_inner_decomposition x x e he
  have hyy := unit_direction_inner_decomposition y y e he
  rw [real_inner_self_eq_norm_sq,hx] at hxx
  rw [real_inner_self_eq_norm_sq,hy] at hyy
  have hid : (A-B)*(A+B) = -(C-D)*(C+D) := by dsimp [A,B,C,D]; nlinarith
  have habs : |A-B| * (A+B) = |C-D| * |C+D| := by
    have hh := congrArg abs hid
    simpa only [abs_mul,abs_neg,abs_of_nonneg (show 0 ≤ A+B by linarith)] using hh
  have hsmall : |A-B| ≤ 2*|C-D| := by
    have hlo := mul_le_mul_of_nonneg_left hsum (abs_nonneg (A-B))
    have hhi := mul_le_mul_of_nonneg_left hCs (abs_nonneg (C-D))
    nlinarith
  have hnorm := norm_le_unit_inner_pair (x-y) e he
  rw [inner_sub_left,inner_sub_left] at hnorm
  change ‖x-y‖ ≤ |A-B|+|C-D| at hnorm
  rw [dist_eq_norm,inner_sub_left]
  change ‖x-y‖ ≤ 3*|C-D|
  linarith

end Kakeya4.Hard.RestrictedTriple
