import Kakeya4.Hard.MultiplicativeConvolution.GaussianEnergyKernel

/-! # Gaussian domination of the capped power with a general positive coefficient -/

noncomputable section
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Pointwise bound at the original radius, allowing the overlap coefficient pi/2. -/
theorem scaledGaussian_le_capped_real {a s r R : ℝ} (ha : 1 ≤ a)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : 0 < r) (hRr : 1 ≤ |R| * r) (x y : ℝ) :
    Real.exp (-a*R^2*(x-y)^2) ≤ r^s * (max r |x-y|)^(-s) := by
  have hsq : 1 ≤ (R*r)^2 := by
    have h : (|R| * r)^2 = (R*r)^2 := by rw [mul_pow, sq_abs, mul_pow]
    nlinarith [sq_nonneg (|R| * r-1)]
  have ha' : 1 ≤ a*(R*r)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hsq)]
  have hb := exp_neg_sq_le_capped_power ha' hs hs1 ((x-y)/r)
  have hex : -a*R^2*(x-y)^2 = -(a*(R*r)^2)*((x-y)/r)^2 := by field_simp
  rw [hex]
  have hmax : 0 < max 1 |(x-y)/r| := zero_lt_one.trans_le (le_max_left _ _)
  rw [max_distance_normalize hr, Real.mul_rpow hr.le hmax.le]
  have hc : r^s*r^(-s) = 1 := by rw [← Real.rpow_add hr]; simp
  simpa only [← mul_assoc, hc, one_mul] using hb

/-- Extended-valued bound retains the actual capped kernel at the original scale. -/
theorem ofReal_scaledGaussian_le_capped {a s r R : ℝ} (ha : 1 ≤ a)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : 0 < r) (hRr : 1 ≤ |R| * r) (x y : ℝ) :
    ENNReal.ofReal (Real.exp (-a*R^2*(x-y)^2)) ≤
      ENNReal.ofReal (r^s) * cappedKernel s r x y := by
  rw [cappedKernel_eq_ofReal hr, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  exact ENNReal.ofReal_le_ofReal (scaledGaussian_le_capped_real ha hs hs1 hr hRr x y)

end Kakeya4.Hard.MultiplicativeConvolution
