import Kakeya4.Hard.RestrictedTriple.AxialRescaling

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

def axialDirection (e : Plane) (d : ℝ) (θ : Plane) : Plane :=
  NormedSpace.normalize (axialScale e d θ)

theorem axialScale_norm_le (e x : Plane) (he : ‖e‖ = 1) {d : ℝ} (hd : 0 < d) :
    ‖axialScale e d x‖ ≤ |inner ℝ x e|+|inner ℝ x (quarterTurn e)|/d := by
  have hh := norm_add_le (inner ℝ x e • e) ((d⁻¹*inner ℝ x (quarterTurn e)) • quarterTurn e)
  simpa only [axialScale,norm_smul,Real.norm_eq_abs,he,quarterTurn_norm,mul_one,
    abs_mul,abs_inv,abs_of_pos hd,div_eq_mul_inv,mul_comm,one_mul] using hh

theorem axialScale_fine_cap_norm (e θ : Plane) (he : ‖e‖ = 1) (hθ : ‖θ‖ = 1)
    {d : ℝ} (hd : 0 < d) (hclose : dist θ e ≤ d/2) : ‖axialScale e d θ‖ ≤ 3/2 := by
  have hpar : |inner ℝ θ e| ≤ 1 := by simpa only [hθ,he,mul_one] using abs_real_inner_le_norm θ e
  have hen : inner ℝ e (quarterTurn e) = 0 := by rw [real_inner_comm]; exact quarterTurn_perpendicular e
  have hn := abs_real_inner_le_norm (θ-e) (quarterTurn e)
  rw [quarterTurn_norm,he,mul_one,← dist_eq_norm,inner_sub_left,hen,sub_zero] at hn
  have hnormal : |inner ℝ θ (quarterTurn e)|/d ≤ 1/2 :=
    (div_le_iff₀ hd).mpr (by linarith)
  exact (axialScale_norm_le e θ he hd).trans (by linarith)

theorem axialDirection_fine_cap (e θ : Plane) (he : ‖e‖ = 1) (hθ : ‖θ‖ = 1)
    {d : ℝ} (hd : 0 < d) (hclose : dist θ e ≤ d/2) (hcap : 3/4 ≤ inner ℝ θ e) :
    ‖axialDirection e d θ‖ = 1 ∧ 1/2 ≤ inner ℝ (axialDirection e d θ) e := by
  have hupper := axialScale_fine_cap_norm e θ he hθ hd hclose
  have hinner := abs_real_inner_le_norm (axialScale e d θ) e
  rw [he,mul_one,(axialScale_coordinates e θ he d).1] at hinner
  have hlower : 3/4 ≤ ‖axialScale e d θ‖ := hcap.trans ((le_abs_self _).trans hinner)
  have hpos : 0 < ‖axialScale e d θ‖ := (by norm_num : (0:ℝ)<3/4).trans_le hlower
  refine ⟨NormedSpace.norm_normalize (norm_pos_iff.mp hpos),?_⟩
  change 1/2 ≤ inner ℝ (‖axialScale e d θ‖⁻¹ • axialScale e d θ) e
  rw [real_inner_smul_left,(axialScale_coordinates e θ he d).1,mul_comm,← div_eq_mul_inv]
  exact (le_div_iff₀ hpos).mpr (by linarith)

/-- The normalized direction is the radial direction of the genuinely transformed points. -/
theorem axialDirection_radialProjection (e b x : Plane) (d : ℝ) (hxb : x-b ≠ 0) :
    axialDirection e d (radialProjection b x) =
      radialProjection (axialScale e d b) (axialScale e d x) := by
  change NormedSpace.normalize (axialScale e d (‖x-b‖⁻¹ • (x-b))) =
    NormedSpace.normalize (axialScale e d x-axialScale e d b)
  rw [← axialScale_sub,axialScale_smul]
  exact NormedSpace.normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr hxb)) _

/-- Separation gain under the actual height-scale linear stretch and normalization. -/
theorem axialDirection_distance_lower (e θ φ : Plane) (he : ‖e‖ = 1)
    (hθ : ‖θ‖ = 1) (hφ : ‖φ‖ = 1) (hpair : 1/2 ≤ inner ℝ θ φ)
    {d : ℝ} (hd : 0 < d) (hθup : ‖axialScale e d θ‖ ≤ 3/2)
    (hφup : ‖axialScale e d φ‖ ≤ 3/2) :
    dist θ φ ≤ 8*d*dist (axialDirection e d θ) (axialDirection e d φ) := by
  have hφne : axialScale e d φ ≠ 0 := by
    intro hz
    have hzero : axialScale e d (0:Plane) = 0 := by simp [axialScale]
    have hφzero := axialScale_injective e he hd.ne' (hz.trans hzero.symm)
    rw [hφzero,norm_zero] at hφ
    norm_num at hφ
  have hold := unit_cap_distance_le_cross θ φ hθ hφ hpair
  have hcross := cross2_le_normalized_distance (axialScale e d θ) (axialScale e d φ) hφne
  have hprod : ‖axialScale e d θ‖*‖axialScale e d φ‖ ≤ 9/4 := by
    have hh := mul_le_mul hθup hφup (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
    nlinarith
  have hupper : |cross2 (axialScale e d θ) (axialScale e d φ)| ≤
      (9/4)*dist (axialDirection e d θ) (axialDirection e d φ) := by
    exact hcross.trans (mul_le_mul_of_nonneg_right hprod dist_nonneg)
  have hdet : |cross2 (axialScale e d θ) (axialScale e d φ)| = |cross2 θ φ|/d := by
    rw [cross2_axialScale _ _ e he,abs_mul,abs_inv,abs_of_pos hd]
    ring
  rw [hdet] at hupper
  have hpaid := (div_le_iff₀ hd).mp hupper
  have hmult := mul_le_mul_of_nonneg_left hpaid (by norm_num : (0:ℝ)≤3)
  have hnonneg := mul_nonneg hd.le
    (dist_nonneg : 0 ≤ dist (axialDirection e d θ) (axialDirection e d φ))
  nlinarith

end Kakeya4.Hard.RestrictedTriple
