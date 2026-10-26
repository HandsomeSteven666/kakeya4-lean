import Kakeya4.Hard.MultiplicativeConvolution.GaussianFourierMoment
import Kakeya4.Hard.MultiplicativeConvolution.CappedEnergy
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Positive Gaussian kernels dominated by physical capped energy

This route uses Mathlib's Gaussian characteristic function directly. The
frequency width R and original physical scale r need only satisfy R*r>=1;
the energy is kept at the original scale, not replaced by a finer-scale input.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

set_option backward.isDefEq.respectTransparency.types false

/-- The positive kernel obtained from a frequency Gaussian of variance R^2. -/
def gaussianPair (R x y : ℝ) : ℝ := Real.exp (-2 * Real.pi ^ 2 * R ^ 2 * (x-y) ^ 2)

/-- Gaussian-weighted true squared Fourier amplitude. -/
def frequencyVariance (R : ℝ) : ℝ≥0 := ⟨R*R, mul_self_nonneg R⟩

/-- Gaussian-weighted true squared Fourier amplitude. -/
def gaussianFourierMass (R : ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ t, ‖fourier μ t‖ ^ 2 ∂ProbabilityTheory.gaussianReal 0 (frequencyVariance R)

/-- The positive kernel never exceeds one. -/
theorem gaussianPair_le_one (R x y : ℝ) : gaussianPair R x y ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  change -2 * Real.pi ^ 2 * R ^ 2 * (x-y) ^ 2 ≤ 0
  have hn : 0 ≤ 2 * Real.pi ^ 2 * R ^ 2 * (x-y) ^ 2 := by positivity
  calc
    _ = -(2 * Real.pi ^ 2 * R ^ 2 * (x-y) ^ 2) := by ring
    _ ≤ 0 := neg_nonpos.mpr hn

/-- A Gaussian majorizes every capped power with exponent between zero and one. -/
theorem exp_neg_sq_le_capped_power {a s : ℝ} (ha : 1 ≤ a) (hs : 0 ≤ s)
    (hs1 : s ≤ 1) (u : ℝ) :
    Real.exp (-a*u^2) ≤ (max 1 |u|) ^ (-s) := by
  by_cases hu : |u| ≤ 1
  · rw [max_eq_left hu, Real.one_rpow]
    apply Real.exp_le_one_iff.mpr
    have hn : 0 ≤ a*u^2 := mul_nonneg (by linarith) (sq_nonneg u)
    nlinarith
  · have hu1 : 1 ≤ |u| := (lt_of_not_ge hu).le
    have hup : 0 < |u| := zero_lt_one.trans_le hu1
    rw [max_eq_right hu1, Real.rpow_neg (abs_nonneg u),
      show -a*u^2 = -(a*u^2) by ring, Real.exp_neg]
    apply (inv_le_inv₀ (Real.exp_pos _) (Real.rpow_pos_of_pos hup _)).mpr
    have hp : |u| ^ s ≤ |u| := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu1 hs1
    have he : |u| ≤ Real.exp (a*u^2) := by
      have hsq : u^2 ≤ a*u^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg u)]
      have hex := Real.add_one_le_exp (a*u^2)
      nlinarith [sq_abs u, sq_nonneg (|u|-1)]
    exact hp.trans he

/-- Exact normalization of a capped distance by a positive physical radius. -/
theorem max_distance_normalize {r : ℝ} (hr : 0 < r) (d : ℝ) :
    max r |d| = r * max 1 |d/r| := by
  rw [abs_div, abs_of_pos hr, mul_max_of_nonneg _ _ hr.le, mul_one, mul_div_cancel₀ _ hr.ne']

/-- Pointwise Gaussian bound at the original smoothing scale. -/
theorem gaussianPair_le_capped_real {s r R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hr : 0 < r) (hRr : 1 ≤ R*r) (x y : ℝ) :
    gaussianPair R x y ≤ r ^ s * (max r |x-y|) ^ (-s) := by
  have ha : 1 ≤ 2 * Real.pi^2 * (R*r)^2 := by
    have hp := Real.pi_gt_three
    have hsq : 1 ≤ (R*r)^2 := by nlinarith
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ 2*Real.pi^2-1) (sub_nonneg.mpr hsq)]
  have hb := exp_neg_sq_le_capped_power ha hs hs1 ((x-y)/r)
  have hex : gaussianPair R x y = Real.exp (-(2 * Real.pi^2 * (R*r)^2) * ((x-y)/r)^2) := by
    unfold gaussianPair
    congr 1
    field_simp
  rw [hex]
  have hmax : 0 < max 1 |(x-y)/r| := zero_lt_one.trans_le (le_max_left _ _)
  rw [max_distance_normalize hr, Real.mul_rpow hr.le hmax.le]
  have hc : r^s * r^(-s) = 1 := by rw [← Real.rpow_add hr]; simp
  simpa only [← mul_assoc, hc, one_mul] using hb

/-- Extended-valued pointwise comparison with the true capped distance kernel. -/
theorem ofReal_gaussianPair_le_capped {s r R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hr : 0 < r) (hRr : 1 ≤ R*r) (x y : ℝ) :
    ENNReal.ofReal (gaussianPair R x y) ≤ ENNReal.ofReal (r^s) * cappedKernel s r x y := by
  rw [cappedKernel_eq_ofReal hr,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  exact ENNReal.ofReal_le_ofReal (gaussianPair_le_capped_real hs hs1 hr hRr x y)

/-- The Gaussian moment is exactly the ordinary double positive-kernel integral. -/
theorem gaussianFourierMass_eq_pair (R : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    gaussianFourierMass R μ = ∫ x, ∫ y, gaussianPair R x y ∂μ ∂μ := by
  have h := gaussian_fourier_sq_moment μ (frequencyVariance R)
  have hv : ((frequencyVariance R) : ℝ) = R*R := rfl
  rw [hv] at h
  simpa only [integral_complex_ofReal, Complex.ofReal_inj,
    gaussianFourierMass, gaussianPair, ← pow_two] using h

/-- The kernel is bounded and hence integrable against the finite pair law. -/
theorem integrable_gaussianPair (R : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun p : ℝ × ℝ ↦ gaussianPair R p.1 p.2) (μ.prod μ) := by
  apply Integrable.of_bound (by unfold gaussianPair; fun_prop) 1
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_pos (show 0 < gaussianPair R p.1 p.2 from Real.exp_pos _)]
  exact gaussianPair_le_one _ _ _

/-- No infinite values are lost when expressing the positive Gaussian moment. -/
theorem ofReal_gaussianFourierMass_eq_pair (R : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ENNReal.ofReal (gaussianFourierMass R μ) =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (gaussianPair R x y) ∂μ ∂μ := by
  rw [gaussianFourierMass_eq_pair,
    ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPair R μ).integral_prod_left
      (Filter.Eventually.of_forall (fun x ↦ integral_nonneg (fun y ↦ (Real.exp_pos _).le)))]
  apply lintegral_congr
  intro x
  have hi : Integrable (gaussianPair R x) μ := by
    apply Integrable.of_bound (by unfold gaussianPair; fun_prop) 1
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_pos (show 0 < gaussianPair R x y from Real.exp_pos _)]
    exact gaussianPair_le_one _ _ _
  exact ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun y ↦ (Real.exp_pos _).le))

/-- Gaussian frequency mass is controlled by the original physical capped energy. -/
theorem gaussianFourierMass_le_cappedEnergy {s r R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hr : 0 < r) (hRr : 1 ≤ R*r) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ENNReal.ofReal (gaussianFourierMass R μ) ≤ ENNReal.ofReal (r^s) * cappedEnergy s r μ := by
  rw [ofReal_gaussianFourierMass_eq_pair]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (r^s) * cappedKernel s r x y ∂μ ∂μ :=
      lintegral_mono (fun x ↦ lintegral_mono (fun y ↦ ofReal_gaussianPair_le_capped hs hs1 hr hRr x y))
    _ = _ := by simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; rfl

end Kakeya4.Hard.MultiplicativeConvolution
