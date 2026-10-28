import Kakeya4.Hard.RestrictedTriple.FineArcInput

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

def axialScale (e : Plane) (d : ℝ) (x : Plane) : Plane :=
  inner ℝ x e • e+(d⁻¹*inner ℝ x (quarterTurn e)) • quarterTurn e

def axialDual (e : Plane) (d : ℝ) (x : Plane) : Plane :=
  (d⁻¹*inner ℝ x e) • e+inner ℝ x (quarterTurn e) • quarterTurn e

def axialTripleNormalization (e : Plane) (d : ℝ) (z : Plane) (t : Triple) : Triple :=
  (axialDual e d t.1,z+axialScale e d t.2.1,z+axialScale e d t.2.2)

theorem axialScale_coordinates (e x : Plane) (he : ‖e‖ = 1) (d : ℝ) :
    inner ℝ (axialScale e d x) e = inner ℝ x e ∧
      inner ℝ (axialScale e d x) (quarterTurn e) = d⁻¹*inner ℝ x (quarterTurn e) := by
  have hne := quarterTurn_perpendicular e
  have hen : inner ℝ e (quarterTurn e) = 0 := by rw [real_inner_comm]; exact hne
  simp [axialScale,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    he,quarterTurn_norm,hne,hen]

theorem axialDual_coordinates (e x : Plane) (he : ‖e‖ = 1) (d : ℝ) :
    inner ℝ (axialDual e d x) e = d⁻¹*inner ℝ x e ∧
      inner ℝ (axialDual e d x) (quarterTurn e) = inner ℝ x (quarterTurn e) := by
  have hne := quarterTurn_perpendicular e
  have hen : inner ℝ e (quarterTurn e) = 0 := by rw [real_inner_comm]; exact hne
  simp [axialDual,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    he,quarterTurn_norm,hne,hen]

theorem axialScale_sub (e x y : Plane) (d : ℝ) :
    axialScale e d (x-y) = axialScale e d x-axialScale e d y := by
  simp only [axialScale,inner_sub_left,mul_sub,sub_smul]
  module

theorem axialScale_smul (e x : Plane) (d a : ℝ) :
    axialScale e d (a • x) = a • axialScale e d x := by
  simp only [axialScale,real_inner_smul_left,smul_add,smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem unit_frame_ext (x y e : Plane) (he : ‖e‖ = 1)
    (h₀ : inner ℝ x e = inner ℝ y e)
    (h₁ : inner ℝ x (quarterTurn e) = inner ℝ y (quarterTurn e)) : x = y := by
  have hh := norm_le_unit_inner_pair (x-y) e he
  rw [inner_sub_left,inner_sub_left,h₀,h₁,sub_self,sub_self,abs_zero,zero_add] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

theorem axialScale_injective (e : Plane) (he : ‖e‖ = 1) {d : ℝ} (hd : d ≠ 0) :
    Function.Injective (axialScale e d) := by
  intro x y hxy
  have h₀ := congrArg (fun z ↦ inner ℝ z e) hxy
  have h₁ := congrArg (fun z ↦ inner ℝ z (quarterTurn e)) hxy
  rw [(axialScale_coordinates e x he d).1,(axialScale_coordinates e y he d).1] at h₀
  rw [(axialScale_coordinates e x he d).2,(axialScale_coordinates e y he d).2] at h₁
  exact unit_frame_ext x y e he h₀ (mul_left_cancel₀ (inv_ne_zero hd) h₁)

theorem axialDual_injective (e : Plane) (he : ‖e‖ = 1) {d : ℝ} (hd : d ≠ 0) :
    Function.Injective (axialDual e d) := by
  intro x y hxy
  have h₀ := congrArg (fun z ↦ inner ℝ z e) hxy
  have h₁ := congrArg (fun z ↦ inner ℝ z (quarterTurn e)) hxy
  rw [(axialDual_coordinates e x he d).1,(axialDual_coordinates e y he d).1] at h₀
  rw [(axialDual_coordinates e x he d).2,(axialDual_coordinates e y he d).2] at h₁
  exact unit_frame_ext x y e he (mul_left_cancel₀ (inv_ne_zero hd) h₀) h₁

theorem cross2_unit_frame (x y e : Plane) (he : ‖e‖ = 1) :
    cross2 x y = inner ℝ x e*inner ℝ y (quarterTurn e)-inner ℝ x (quarterTurn e)*inner ℝ y e := by
  have hunit : (e 0)^2+(e 1)^2 = 1 := by rw [← plane_norm_sq_coordinates,he]; norm_num
  rw [plane_inner_coordinates,plane_inner_coordinates,plane_inner_coordinates,plane_inner_coordinates,
    quarterTurn_zero,quarterTurn_one]
  calc
    _ = cross2 x y*((e 0)^2+(e 1)^2) := by rw [hunit]; ring
    _ = _ := by unfold cross2; ring

theorem cross2_axialScale (x y e : Plane) (he : ‖e‖ = 1) (d : ℝ) :
    cross2 (axialScale e d x) (axialScale e d y) = d⁻¹*cross2 x y := by
  rw [cross2_unit_frame _ _ e he,(axialScale_coordinates e x he d).1,
    (axialScale_coordinates e y he d).1,(axialScale_coordinates e x he d).2,
    (axialScale_coordinates e y he d).2,cross2_unit_frame x y e he]
  ring

theorem axialDual_inner_axialScale (x y e : Plane) (he : ‖e‖ = 1) (d : ℝ) :
    inner ℝ (axialDual e d x) (axialScale e d y) = d⁻¹*inner ℝ x y := by
  rw [unit_direction_inner_decomposition _ _ e he,(axialDual_coordinates e x he d).1,
    (axialDual_coordinates e x he d).2,(axialScale_coordinates e y he d).1,
    (axialScale_coordinates e y he d).2,unit_direction_inner_decomposition x y e he]
  ring

theorem dotDifference_axialTripleNormalization (e : Plane) (he : ‖e‖ = 1) (d : ℝ)
    (z : Plane) (t : Triple) :
    dotDifference (axialTripleNormalization e d z t) = d⁻¹*dotDifference t := by
  change inner ℝ (axialDual e d t.1) ((z+axialScale e d t.2.1)-(z+axialScale e d t.2.2)) = _
  have hid : (z+axialScale e d t.2.1)-(z+axialScale e d t.2.2) = axialScale e d (t.2.1-t.2.2) := by
    rw [axialScale_sub]
    module
  rw [hid,axialDual_inner_axialScale _ _ e he d]
  rfl

theorem axialTripleNormalization_injective (e : Plane) (he : ‖e‖ = 1) {d : ℝ}
    (hd : d ≠ 0) (z : Plane) : Function.Injective (axialTripleNormalization e d z) := by
  intro t u htu
  have h₀ := congrArg (fun v : Triple ↦ v.1) htu
  have h₁ := congrArg (fun v : Triple ↦ v.2.1) htu
  have h₂ := congrArg (fun v : Triple ↦ v.2.2) htu
  change axialDual e d t.1 = axialDual e d u.1 at h₀
  change z+axialScale e d t.2.1 = z+axialScale e d u.2.1 at h₁
  change z+axialScale e d t.2.2 = z+axialScale e d u.2.2 at h₂
  exact Prod.ext (axialDual_injective e he hd h₀)
    (Prod.ext (axialScale_injective e he hd (add_left_cancel h₁))
      (axialScale_injective e he hd (add_left_cancel h₂)))

theorem dotDifferenceImage_axialTripleNormalization (e : Plane) (he : ‖e‖ = 1)
    (d : ℝ) (z : Plane) (Q : Set Triple) :
    dotDifferenceImage (axialTripleNormalization e d z '' Q) =
      (fun x : ℝ ↦ d⁻¹*x) '' dotDifferenceImage Q := by
  simp only [dotDifferenceImage,Set.image_image]
  congr 1
  funext t
  exact dotDifference_axialTripleNormalization e he d z t

end Kakeya4.Hard.RestrictedTriple
