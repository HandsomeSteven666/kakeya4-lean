import Kakeya4.Hard.RestrictedTriple.BranchReadyInput

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

def cross2 (x y : Plane) : ℝ := x 0*y 1-x 1*y 0

def determinantStrip (δ : ℝ) (L : AffineLine) : Set Plane :=
  {x | |cross2 (x-L.anchor) L.direction| ≤ δ}

def determinantStripCount (δ : ℝ) (L : AffineLine) (P : Finset Plane) : ℝ≥0∞ := by
  classical
  exact ((P.filter (fun x ↦ x ∈ determinantStrip δ L)).card : ℝ≥0∞)

theorem plane_norm_sq_coordinates (x : Plane) : ‖x‖^2 = (x 0)^2+(x 1)^2 := by
  simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x

theorem planar_lagrange_identity (x d : Plane) :
    ‖x‖^2*‖d‖^2 = (cross2 x d)^2+(x 0*d 0+x 1*d 1)^2 := by
  rw [plane_norm_sq_coordinates,plane_norm_sq_coordinates]
  unfold cross2
  ring

theorem cross2_le_norm_of_unit (v d : Plane) (hd : ‖d‖ = 1) : |cross2 v d| ≤ ‖v‖ := by
  have hh := planar_lagrange_identity v d
  rw [hd] at hh
  have habs : |cross2 v d|^2 = (cross2 v d)^2 := sq_abs _
  nlinarith [sq_nonneg (v 0*d 0+v 1*d 1),abs_nonneg (cross2 v d),norm_nonneg v]

theorem norm_projection_residual (v d : Plane) (hd : ‖d‖ = 1) :
    ‖v-(v 0*d 0+v 1*d 1) • d‖ = |cross2 v d| := by
  let t : ℝ := v 0*d 0+v 1*d 1
  have hunit : (d 0)^2+(d 1)^2 = 1 := by rw [← plane_norm_sq_coordinates,hd]; norm_num
  have hcoord : ‖v-t • d‖^2 = (v 0-t*d 0)^2+(v 1-t*d 1)^2 := by
    rw [plane_norm_sq_coordinates]
    simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  have hmult : t^2*((d 0)^2+(d 1)^2) = t^2 := by rw [hunit]; ring
  have hlag := planar_lagrange_identity v d
  rw [hd,plane_norm_sq_coordinates] at hlag
  have hdot : t = v 0*d 0+v 1*d 1 := rfl
  have hsq : ‖v-t • d‖^2 = (cross2 v d)^2 := by
    nlinarith
  change ‖v-t • d‖ = _
  nlinarith [sq_abs (cross2 v d),abs_nonneg (cross2 v d),norm_nonneg (v-t • d)]

theorem cross2_sub_line_point (x : Plane) (L : AffineLine) (t : ℝ) :
    cross2 (x-(L.anchor+t • L.direction)) L.direction = cross2 (x-L.anchor) L.direction := by
  simp only [cross2,PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

/-- Exact distance, including the infimum over every point of the entire affine line. -/
theorem infEDist_lineCarrier_eq_cross2 (x : Plane) (L : AffineLine) :
    infEDist x (lineCarrier L) = ENNReal.ofReal |cross2 (x-L.anchor) L.direction| := by
  apply le_antisymm
  · let v := x-L.anchor
    let t : ℝ := v 0*L.direction 0+v 1*L.direction 1
    have hy : L.anchor+t • L.direction ∈ lineCarrier L := ⟨t,rfl⟩
    have heq : x-(L.anchor+t • L.direction) = v-t • L.direction := by dsimp [v]; module
    have hd : dist x (L.anchor+t • L.direction) = |cross2 (x-L.anchor) L.direction| := by
      rw [dist_eq_norm,heq]
      exact norm_projection_residual v L.direction L.direction_unit
    exact (infEDist_le_edist_of_mem hy).trans_eq (by rw [edist_dist,hd])
  · apply le_infEDist.mpr
    intro y hy
    obtain ⟨t,rfl⟩ := hy
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm,← cross2_sub_line_point x L t]
    exact cross2_le_norm_of_unit _ _ L.direction_unit

theorem determinantStrip_eq_lineNeighborhood {δ : ℝ} (hδ : 0 ≤ δ) (L : AffineLine) :
    determinantStrip δ L = lineNeighborhood δ L := by
  ext x
  simp only [determinantStrip,mem_ofPred_eq,lineNeighborhood,mem_cthickening_iff,
    infEDist_lineCarrier_eq_cross2,ENNReal.ofReal_le_ofReal_iff hδ]

theorem determinantStrip_count_eq (δ : ℝ) (hδ : 0 ≤ δ) (L : AffineLine) (P : Finset Plane) :
    determinantStripCount δ L P =
      (((P : Set Plane) ∩ lineNeighborhood δ L).encard : ℝ≥0∞) := by
  classical
  unfold determinantStripCount
  rw [← determinantStrip_eq_lineNeighborhood hδ]
  have hset : (P : Set Plane) ∩ determinantStrip δ L =
      (P.filter (fun x ↦ x ∈ determinantStrip δ L) : Set Plane) := by ext x; simp
  rw [hset,Set.encard_coe_eq_coe_finsetCard,ENat.toENNReal_coe]

end Kakeya4.Hard.RestrictedTriple
