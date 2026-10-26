import Kakeya4.Hard.MultiplicativeConvolution.GaussianBilinear

/-!
# Actual overlap integral for two translated Gaussian profiles

Completing the square reduces the overlap to Mathlib's Gaussian integral.
These identities provide the spatial kernel for the bilinear envelope L2 bound.
-/

noncomputable section
open MeasureTheory

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The standard positive Gaussian is bounded by one. -/
theorem gaussianWeight_le_one (x : ℝ) : gaussianWeight x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg x)

/-- Exact completion of the square for two translated profiles. -/
theorem gaussianWeight_mul_complete (a b u : ℝ) :
    gaussianWeight (a-u) * gaussianWeight (b-u) =
      Real.exp (-(Real.pi/2)*(a-b)^2) *
        Real.exp (-(2*Real.pi)*(u-(a+b)/2)^2) := by
  unfold gaussianWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The actual product of two translated Gaussian profiles is integrable. -/
theorem integrable_gaussianWeight_overlap (a b : ℝ) :
    Integrable (fun u ↦ gaussianWeight (a-u) * gaussianWeight (b-u)) := by
  simp_rw [gaussianWeight_mul_complete]
  exact ((integrable_exp_neg_mul_sq (by positivity : 0 < 2*Real.pi)).comp_sub_right
    ((a+b)/2)).const_mul _

/-- Exact real overlap integral, with its fixed normalization. -/
theorem integral_gaussianWeight_overlap (a b : ℝ) :
    (∫ u, gaussianWeight (a-u) * gaussianWeight (b-u)) =
      Real.sqrt (1/2) * Real.exp (-(Real.pi/2)*(a-b)^2) := by
  simp_rw [gaussianWeight_mul_complete]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun u : ℝ ↦ Real.exp (-(2*Real.pi)*u^2)) ((a+b)/2),
    integral_gaussian]
  have h : Real.pi / (2*Real.pi) = (1/2 : ℝ) := by field_simp
  rw [h]
  ring

end Kakeya4.Hard.MultiplicativeConvolution
