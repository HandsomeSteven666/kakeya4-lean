import Kakeya4.Hard.RestrictedTriple.SequentialOrthogonalInput
import Mathlib.Analysis.Normed.Module.Normalize

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

def radialProjection (b x : Plane) : Plane := NormedSpace.normalize (x-b)

theorem cross2_smul_smul (a b : ℝ) (x y : Plane) :
    cross2 (a • x) (b • y) = a*b*cross2 x y := by
  simp only [cross2,PiLp.smul_apply,smul_eq_mul]
  ring

theorem strip_vantage_height {w h : ℝ} (hw : 0 ≤ w) (L : AffineLine) (b y : Plane)
    (hy : y ∈ lineNeighborhood w L)
    (hfar : h+w ≤ |cross2 (b-L.anchor) L.direction|) :
    h ≤ |cross2 (y-b) L.direction| := by
  rw [← determinantStrip_eq_lineNeighborhood hw] at hy
  change |cross2 (y-L.anchor) L.direction| ≤ w at hy
  have heq : cross2 (b-L.anchor) L.direction =
      cross2 (y-L.anchor) L.direction-cross2 (y-b) L.direction := by
    simp only [cross2,PiLp.sub_apply]
    ring
  have hh : |cross2 (y-L.anchor) L.direction-cross2 (y-b) L.direction| ≤
      |cross2 (y-L.anchor) L.direction|+|cross2 (y-b) L.direction| := by
    simpa only [sub_eq_add_neg,abs_neg] using
      abs_add_le (cross2 (y-L.anchor) L.direction) (-cross2 (y-b) L.direction)
  rw [← heq] at hh
  linarith

/-- Rotate the already proved strip projection bound to obtain a determinant bound. -/
theorem strip_vantage_determinant_lower {w h : ℝ} (hw : 0 ≤ w) (L : AffineLine)
    (b x y : Plane) (hx : x ∈ lineNeighborhood w L) (hy : y ∈ lineNeighborhood w L)
    (hfar : h+w ≤ |cross2 (b-L.anchor) L.direction|) (hyb : dist y b ≤ 2) :
    h*dist x y ≤ |cross2 (x-b) (y-b)|+8*w := by
  have hheight := strip_vantage_height hw L b y hy hfar
  have hh := strip_projection_lower hw L (quarterTurn (y-b)) x y hx hy
  have hleft : inner ℝ (quarterTurn (y-b)) L.direction = cross2 (y-b) L.direction := by
    rw [real_inner_comm,inner_quarterTurn_eq_cross2]
    unfold cross2
    ring
  have hright : inner ℝ (quarterTurn (y-b)) (x-y) = -cross2 (x-b) (y-b) := by
    rw [real_inner_comm,inner_quarterTurn_eq_cross2]
    simp only [cross2,PiLp.sub_apply]
    ring
  rw [hleft,hright,abs_neg,quarterTurn_norm,← dist_eq_norm] at hh
  have hmult := mul_le_mul_of_nonneg_right hheight (dist_nonneg : 0 ≤ dist x y)
  have herr := mul_le_mul_of_nonneg_left hyb (show 0 ≤ 4*w by positivity)
  nlinarith

theorem cross2_le_normalized_distance (v u : Plane) (hu : u ≠ 0) :
    |cross2 v u| ≤ ‖v‖*‖u‖*dist (NormedSpace.normalize v) (NormedSpace.normalize u) := by
  have hscale : cross2 v u = ‖v‖*‖u‖*cross2 (NormedSpace.normalize v) (NormedSpace.normalize u) := by
    calc
      _ = cross2 (‖v‖ • NormedSpace.normalize v) (‖u‖ • NormedSpace.normalize u) := by
        rw [NormedSpace.norm_smul_normalize,NormedSpace.norm_smul_normalize]
      _ = _ := cross2_smul_smul _ _ _ _
  have hh := cross2_le_norm_of_unit (NormedSpace.normalize v-NormedSpace.normalize u)
    (NormedSpace.normalize u) (NormedSpace.norm_normalize hu)
  have heq : cross2 (NormedSpace.normalize v-NormedSpace.normalize u) (NormedSpace.normalize u) =
      cross2 (NormedSpace.normalize v) (NormedSpace.normalize u) := by
    simp only [cross2,PiLp.sub_apply]
    ring
  rw [heq,← dist_eq_norm] at hh
  rw [hscale,abs_mul,abs_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg u))]
  exact mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg v) (norm_nonneg u))

/-- Co-Lipschitz radial geometry above the atomic strip-error cutoff. -/
theorem strip_radial_colipschitz {w h : ℝ} (hw : 0 ≤ w) (hh : 0 < h) (L : AffineLine)
    (b x y : Plane) (hx : x ∈ lineNeighborhood w L) (hy : y ∈ lineNeighborhood w L)
    (hfar : h+w ≤ |cross2 (b-L.anchor) L.direction|)
    (hxb : dist x b ≤ 2) (hyb : dist y b ≤ 2) (hsep : 16*w/h ≤ dist x y) :
    (h/8)*dist x y ≤ dist (radialProjection b x) (radialProjection b y) := by
  have hdet := strip_vantage_determinant_lower hw L b x y hx hy hfar hyb
  have hcut : 16*w ≤ h*dist x y := by
    have hc := (div_le_iff₀ hh).mp hsep
    nlinarith
  have hu : y-b ≠ 0 := by
    intro heq
    have hheight := strip_vantage_height hw L b y hy hfar
    rw [heq] at hheight
    simp only [cross2,PiLp.zero_apply,zero_mul,sub_self,abs_zero] at hheight
    linarith
  have hcross := cross2_le_normalized_distance (x-b) (y-b) hu
  have hnorms : ‖x-b‖*‖y-b‖ ≤ 4 := by
    rw [← dist_eq_norm,← dist_eq_norm]
    calc
      _ ≤ 2*2 := mul_le_mul hxb hyb dist_nonneg (by norm_num)
      _ = _ := by norm_num
  have hupper := mul_le_mul_of_nonneg_right hnorms
    (dist_nonneg : 0 ≤ dist (NormedSpace.normalize (x-b)) (NormedSpace.normalize (y-b)))
  change (h/8)*dist x y ≤ dist (NormedSpace.normalize (x-b)) (NormedSpace.normalize (y-b))
  nlinarith

end Kakeya4.Hard.RestrictedTriple
