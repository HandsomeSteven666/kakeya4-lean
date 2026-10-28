import Kakeya4.Hard.RestrictedTriple.StripReadyInput

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Kakeya4.Hard.RestrictedTriple

def positivePartPlane (x : Plane) : Plane := WithLp.toLp 2 (fun i ↦ max 0 (x i))

def squarePadding : Plane := WithLp.toLp 2 (fun _ : Fin 2 ↦ (1/40:ℝ))

def endpointSquareShift (w : Plane) : Plane := positivePartPlane (-w)+squarePadding

theorem positivePartPlane_norm_le (x : Plane) : ‖positivePartPlane x‖ ≤ ‖x‖ := by
  have hs (i : Fin 2) : (max 0 (x i))^2 ≤ (x i)^2 := by
    by_cases h : 0 ≤ x i
    · rw [max_eq_right h]
    · rw [max_eq_left (le_of_not_ge h)]
      simpa using sq_nonneg (x i)
  have hnorm := plane_norm_sq_coordinates x
  have hp := plane_norm_sq_coordinates (positivePartPlane x)
  change ‖positivePartPlane x‖^2 = (max 0 (x 0))^2+(max 0 (x 1))^2 at hp
  nlinarith [hs 0,hs 1,norm_nonneg x,norm_nonneg (positivePartPlane x)]

theorem squarePadding_norm_le : ‖squarePadding‖ ≤ 1/20 := by
  have hh := plane_norm_sq_coordinates squarePadding
  change ‖squarePadding‖^2 = (1/40:ℝ)^2+(1/40:ℝ)^2 at hh
  nlinarith [norm_nonneg squarePadding]

theorem endpointSquareShift_add_center (w : Plane) :
    w+endpointSquareShift w = positivePartPlane w+squarePadding := by
  apply PiLp.ext
  intro i
  simp only [endpointSquareShift,positivePartPlane,squarePadding,PiLp.add_apply,PiLp.neg_apply,PiLp.toLp_apply]
  by_cases h : 0 ≤ w i
  · rw [max_eq_right h,max_eq_left (by linarith : -w i ≤ 0)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_right (by linarith : 0 ≤ -w i)]
    ring

theorem coordinate_abs_le_plane_norm (x : Plane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  simpa [Real.dist_eq] using PiLp.dist_apply_le x (0:Plane) i

/-- Both small endpoint balls fit in the positive unit square and the closed unit ball
after the same translation, without changing their distance or dot differences. -/
theorem two_ball_endpoint_square_shift (w : Plane) (hw : ‖w‖ ≤ 3/4) (x : Plane)
    (hx : dist x 0 ≤ 1/40 ∨ dist x w ≤ 1/40) :
    x+endpointSquareShift w ∈ unitSquare ∧ ‖x+endpointSquareShift w‖ ≤ 1 := by
  have hshift : ‖endpointSquareShift w‖ ≤ 4/5 := by
    have h1 := norm_add_le (positivePartPlane (-w)) squarePadding
    have h2 := positivePartPlane_norm_le (-w)
    rw [norm_neg] at h2
    dsimp [endpointSquareShift]
    linarith [squarePadding_norm_le]
  have hcenter : ‖w+endpointSquareShift w‖ ≤ 4/5 := by
    rw [endpointSquareShift_add_center]
    have h1 := norm_add_le (positivePartPlane w) squarePadding
    linarith [positivePartPlane_norm_le w,squarePadding_norm_le]
  have hnonneg : ∀ i, 0 ≤ (x+endpointSquareShift w) i := by
    intro i
    simp only [endpointSquareShift,positivePartPlane,squarePadding,PiLp.add_apply,PiLp.neg_apply,PiLp.toLp_apply]
    rcases hx with hx | hx
    · have hcoord := PiLp.dist_apply_le x (0:Plane) i
      have hh : |x i| ≤ 1/40 := by simpa [Real.dist_eq] using hcoord.trans hx
      have hm : 0 ≤ max 0 (-w i) := le_max_left _ _
      linarith [(abs_le.mp hh).1]
    · have hcoord := PiLp.dist_apply_le x w i
      have hh : |x i-w i| ≤ 1/40 := by simpa only [Real.dist_eq] using hcoord.trans hx
      have hm : -w i ≤ max 0 (-w i) := le_max_right _ _
      linarith [(abs_le.mp hh).1]
  have hnorm : ‖x+endpointSquareShift w‖ ≤ 1 := by
    rcases hx with hx | hx
    · have hh := norm_add_le x (endpointSquareShift w)
      simp only [dist_zero_right] at hx
      linarith
    · have heq : x+endpointSquareShift w = (x-w)+(w+endpointSquareShift w) := by module
      rw [heq]
      have hh := norm_add_le (x-w) (w+endpointSquareShift w)
      rw [dist_eq_norm] at hx
      linarith
  refine ⟨?_,hnorm⟩
  intro i
  exact ⟨hnonneg i,(le_abs_self _).trans ((coordinate_abs_le_plane_norm _ i).trans hnorm)⟩

theorem endpoint_cell_square_support (b c : Plane) {δ : ℝ} (hbc : 0 < dist b c)
    (hδ : δ ≤ dist b c/50) :
    ∃ z : Plane, ∀ x : Plane, dist x b ≤ δ ∨ dist x c ≤ δ →
      z+cellScale (dist b c) • x ∈ unitSquare ∧ ‖z+cellScale (dist b c) • x‖ ≤ 1 := by
  let v := cellScale (dist b c)
  let w := v • (c-b)
  have hv : 0 < v := cellScale_pos hbc
  have hmul : v*dist b c = 3/4 := cellScale_mul hbc
  have hrad : v*δ ≤ 1/40 := cellScale_radius hbc hδ
  have hw : ‖w‖ = 3/4 := by
    dsimp [w]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hv,← dist_eq_norm,dist_comm]
    exact hmul
  refine ⟨endpointSquareShift w-v • b,?_⟩
  intro x hx
  have hnear : dist (v • (x-b)) 0 ≤ 1/40 ∨ dist (v • (x-b)) w ≤ 1/40 := by
    rcases hx with hx | hx
    · left
      have hh := scaled_translated_dist hv b x b
      simp only [sub_self,smul_zero] at hh
      rw [hh]
      exact (mul_le_mul_of_nonneg_left hx hv.le).trans hrad
    · right
      rw [scaled_translated_dist hv b x c]
      exact (mul_le_mul_of_nonneg_left hx hv.le).trans hrad
  have hh := two_ball_endpoint_square_shift w hw.le (v • (x-b)) hnear
  have heq : endpointSquareShift w-v • b+v • x = v • (x-b)+endpointSquareShift w := by module
  change endpointSquareShift w-v • b+v • x ∈ unitSquare ∧
    ‖endpointSquareShift w-v • b+v • x‖ ≤ 1
  rwa [heq]

end Kakeya4.Hard.RestrictedTriple
