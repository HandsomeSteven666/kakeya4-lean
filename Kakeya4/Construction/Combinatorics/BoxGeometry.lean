import Kakeya4.Construction.Combinatorics.BoxParameterNet

/-!
# Geometric constraints on orthogonal boxes

This file isolates consequences of a body containing a Euclidean ball when that body is already
known to lie in a certified orthogonal box. It does not construct the box certificate.
-/

set_option autoImplicit false

open Metric
open scoped InnerProductSpace

namespace Kakeya4.Construction

/-- If a set contains the closed ball of radius `δ` about zero and lies in an orthogonal box,
then every half-width of that box is at least `δ`. The argument compares the two opposite points
`z ± δ bᵢ` in each frame direction, so neither the box center nor the ball center must lie in the
other set. -/
theorem orthogonalBox_halfWidth_ge_of_closedBall_subset
    {n : ℕ} (d : OrthogonalBoxData n) {W : Set (BoxAmbient n)} {z : BoxAmbient n}
    {δ : ℝ} (hδ : 0 ≤ δ) (hball : closedBall z δ ⊆ W)
    (hbox : W ⊆ orthogonalBox d.frame d.center d.halfWidth) :
    ∀ i, δ ≤ d.halfWidth i := by
  intro i
  have hplusBall : z + δ • d.frame i ∈ closedBall z δ := by
    rw [mem_closedBall, dist_eq_norm, show z + δ • d.frame i - z = δ • d.frame i by abel,
      norm_smul, d.frame.norm_eq_one]
    simp [abs_of_nonneg hδ]
  have hminusBall : z + (-δ) • d.frame i ∈ closedBall z δ := by
    rw [mem_closedBall, dist_eq_norm, show z + (-δ) • d.frame i - z = (-δ) • d.frame i by abel,
      norm_smul, d.frame.norm_eq_one]
    simp [abs_of_nonneg hδ]
  have hplus := hbox (hball hplusBall) i
  have hminus := hbox (hball hminusBall) i
  have hcoord :
      d.frame.repr ((z + δ • d.frame i) - d.center) i -
        d.frame.repr ((z + (-δ) • d.frame i) - d.center) i = 2 * δ := by
    rw [d.frame.repr_apply_apply, d.frame.repr_apply_apply]
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    have hunit : ⟪d.frame i, d.frame i⟫_ℝ = 1 := by
      simp
    rw [hunit]
    ring
  have hdiff :
      |d.frame.repr ((z + δ • d.frame i) - d.center) i -
        d.frame.repr ((z + (-δ) • d.frame i) - d.center) i| ≤
          |d.frame.repr ((z + δ • d.frame i) - d.center) i| +
            |d.frame.repr ((z + (-δ) • d.frame i) - d.center) i| := abs_sub _ _
  rw [hcoord, abs_of_nonneg (mul_nonneg (by norm_num) hδ)] at hdiff
  nlinarith

end Kakeya4.Construction
