import Kakeya4.Hard.MultiplicativeConvolution.GaussianCentral
import Kakeya4.Hard.MultiplicativeConvolution.GaussianTail

/-! # Central and tail decomposition of the actual bilinear Gaussian integral -/

noncomputable section
open MeasureTheory Set

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Fixed first moment used in the tail payment; it is an actual finite Bochner integral. -/
def gaussianTailMoment : ℝ := ∫ u : ℝ, |u| * Real.exp (-(Real.pi/4)*u^2)

/-- The fixed tail constant is nonnegative. -/
theorem gaussianTailMoment_nonneg : 0 ≤ gaussianTailMoment := by
  apply integral_nonneg
  intro u
  positivity

/-- The actual full Gaussian bilinear profile is integrable. -/
theorem integrable_fourier_gaussianAverage (η ν : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ν] (ξ : ℝ) :
    Integrable (fun u ↦ ‖fourier η u‖ * gaussianAverage ν ξ u) := by
  have h := (integrable_gaussian_fourierProfile η ν ξ).integral_prod_right
  have he : (fun u ↦ ∫ y, gaussianWeight (ξ*y-u) * ‖fourier η u‖ ∂ν) =
      (fun u ↦ ‖fourier η u‖ * gaussianAverage ν ξ u) := by
    funext u
    rw [integral_mul_const]
    exact mul_comm _ _
  rw [he] at h
  exact h

/-- The actual tail of the bilinear integral is paid by a fixed first moment. -/
theorem integral_fourier_gaussian_tail_le (η ν : Measure ℝ)
    [IsFiniteMeasure η] [IsProbabilityMeasure ν] (hν : UnitSupported ν)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    (∫ u in {u : ℝ | 2*|ξ| < |u|}, ‖fourier η u‖ * gaussianAverage ν ξ u) ≤
      η.real univ * gaussianTailMoment / (2*|ξ|) := by
  have hb : 0 < Real.pi/4 := by positivity
  have hT : 0 < 2*|ξ| := mul_pos (by norm_num) (abs_pos.mpr hξ)
  have hset : MeasurableSet {u : ℝ | 2*|ξ| < |u|} :=
    measurableSet_lt measurable_const (by fun_prop : Measurable (fun u : ℝ ↦ |u|))
  calc
    _ ≤ ∫ u in {u : ℝ | 2*|ξ| < |u|}, η.real univ * Real.exp (-(Real.pi/4)*u^2) := by
      apply integral_mono_ae (integrable_fourier_gaussianAverage η ν ξ).integrableOn
        ((integrable_exp_neg_mul_sq hb).const_mul (η.real univ)).integrableOn
      filter_upwards [ae_restrict_mem hset] with u hu
      exact mul_le_mul (show ‖fourier η u‖ ≤ η.real univ from norm_charFun_le _)
        (gaussianAverage_le_tail ν hν hu) (gaussianAverage_nonneg ν ξ u)
        (measureReal_nonneg)
    _ = η.real univ * (∫ u in {u : ℝ | 2*|ξ| < |u|}, Real.exp (-(Real.pi/4)*u^2)) :=
      integral_const_mul _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (integral_gaussian_tail_le hb hT)
        (show 0 ≤ η.real univ from measureReal_nonneg)
      simpa only [gaussianTailMoment, mul_div_assoc] using h

/-- The full two-factor Fourier amplitude has a proved central-plus-tail estimate. -/
theorem norm_fourier_mconv_le_central_tail (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hμ : UnitSupported μ) (hν : UnitSupported ν)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖fourier (μ ∗ₘ ν) ξ‖ ≤
      Real.sqrt (∫ u in Icc (-(2*|ξ|)) (2*|ξ|), ‖fourier (gaussianTiltLaw μ) u‖^2) *
        Real.sqrt (∫ u, gaussianAverage ν ξ u ^ 2) +
      (gaussianTiltLaw μ).real univ * gaussianTailMoment / (2*|ξ|) := by
  have hi := integrable_fourier_gaussianAverage (gaussianTiltLaw μ) ν ξ
  have hcompl : (Icc (-(2*|ξ|)) (2*|ξ|))ᶜ = {u : ℝ | 2*|ξ| < |u|} := by
    ext u
    simp only [mem_compl_iff, mem_Icc, mem_setOf_eq, ← abs_le, not_le]
  calc
    _ ≤ ∫ u, ‖fourier (gaussianTiltLaw μ) u‖ * gaussianAverage ν ξ u :=
      norm_fourier_mconv_le_gaussian μ ν hμ ξ
    _ = (∫ u in Icc (-(2*|ξ|)) (2*|ξ|), ‖fourier (gaussianTiltLaw μ) u‖ * gaussianAverage ν ξ u) +
        (∫ u in {u : ℝ | 2*|ξ| < |u|}, ‖fourier (gaussianTiltLaw μ) u‖ * gaussianAverage ν ξ u) := by
      rw [← integral_add_compl measurableSet_Icc hi, hcompl]
    _ ≤ _ := add_le_add (integral_gaussian_central_le (gaussianTiltLaw μ) ν ξ (2*|ξ|))
      (integral_fourier_gaussian_tail_le (gaussianTiltLaw μ) ν hν hξ)

end Kakeya4.Hard.MultiplicativeConvolution
