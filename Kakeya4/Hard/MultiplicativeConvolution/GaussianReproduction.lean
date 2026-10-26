import Kakeya4.Hard.MultiplicativeConvolution.GaussianTilt
import Kakeya4.Hard.MultiplicativeConvolution.GaussianFourierMoment

/-!
# Positive Gaussian reproduction for the two-factor estimate

The fixed Gaussian is used instead of assuming an auxiliary flat-top cutoff
has a positive Fourier transform. Its transform is reused from Mathlib.
-/

noncomputable section
open MeasureTheory
open FourierTransform

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Standard self-dual Gaussian in the manuscript Fourier convention. -/
def gaussianWeight (x : ℝ) : ℝ := Real.exp (-Real.pi*x^2)

/-- The actual paper Fourier phase, named to share integral identities. -/
def fourierPhase (ξ x : ℝ) : ℂ :=
  Complex.exp (((-(2*Real.pi)*ξ*x : ℝ) : ℂ) * Complex.I)

/-- The phase has unit norm at all real points. -/
theorem norm_fourierPhase (ξ x : ℝ) : ‖fourierPhase ξ x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Integral representation in the named phase. -/
theorem fourier_eq_integral_phase (μ : Measure ℝ) (ξ : ℝ) :
    fourier μ ξ = ∫ x, fourierPhase ξ x ∂μ := fourier_eq_integral μ ξ

/-- Exact normalized Gaussian Fourier transform, from the existing Mathlib theorem. -/
theorem gaussianWeight_fourier (x : ℝ) :
    (∫ u, (gaussianWeight u : ℂ) * fourierPhase x u) = (gaussianWeight x : ℂ) := by
  have h := congrFun (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)) x
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  simp only [mul_one, Complex.one_cpow, div_one, one_div, one_mul, smul_eq_mul] at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with u
    unfold gaussianWeight fourierPhase
    rw [Complex.ofReal_exp]
    simp_rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · unfold gaussianWeight
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring

/-- The fixed Gaussian is integrable. -/
theorem integrable_gaussianWeight : Integrable gaussianWeight :=
  integrable_exp_neg_mul_sq Real.pi_pos

/-- Reflection preserves the standard Gaussian. -/
theorem gaussianWeight_neg (x : ℝ) : gaussianWeight (-x) = gaussianWeight x := by
  simp only [gaussianWeight, neg_sq]

/-- Symmetry of the actual real bilinear Fourier phase. -/
theorem fourierPhase_comm (x y : ℝ) : fourierPhase x y = fourierPhase y x := by
  unfold fourierPhase
  congr 2
  push_cast
  ring

/-- Exact phase multiplication under subtraction. -/
theorem fourierPhase_sub (x ξ u : ℝ) :
    fourierPhase x (ξ-u) = fourierPhase x ξ * fourierPhase (-x) u := by
  unfold fourierPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Shifted Gaussian Fourier integral, with no cutoff or sign assumption. -/
theorem gaussianWeight_shift_fourier (ξ x : ℝ) :
    (∫ u, (gaussianWeight (ξ-u) : ℂ) * fourierPhase x u) =
      fourierPhase ξ x * (gaussianWeight x : ℂ) := by
  have h := integral_sub_left_eq_self
    (fun u : ℝ ↦ (gaussianWeight (ξ-u) : ℂ) * fourierPhase x u) volume ξ
  calc
    _ = ∫ u, (gaussianWeight (ξ-(ξ-u)) : ℂ) * fourierPhase x (ξ-u) := h.symm
    _ = ∫ u, fourierPhase x ξ * ((gaussianWeight u : ℂ) * fourierPhase (-x) u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [show ξ-(ξ-u) = u by ring, fourierPhase_sub]
      ring
    _ = _ := by
      rw [integral_const_mul, gaussianWeight_fourier, gaussianWeight_neg, fourierPhase_comm]

/-- Fourier transform of the actual Gaussian-weighted law. -/
theorem fourier_withDensity_gaussian (μ : Measure ℝ) (ξ : ℝ) :
    fourier (μ.withDensity (fun x ↦ ENNReal.ofReal (gaussianWeight x))) ξ =
      ∫ x, (gaussianWeight x : ℂ) * fourierPhase ξ x ∂μ := by
  have hg : Measurable (fun x ↦ ENNReal.ofReal (gaussianWeight x)) := by
    unfold gaussianWeight
    fun_prop
  rw [fourier_eq_integral_phase,
    integral_withDensity_eq_integral_toReal_smul hg
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (show 0 ≤ gaussianWeight x from (Real.exp_pos _).le)]
  exact Complex.real_smul

/-- Actual Gaussian weighting becomes a positive Gaussian convolution on Fourier side. -/
theorem gaussianWeight_fourier_convolution (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    fourier (μ.withDensity (fun x ↦ ENNReal.ofReal (gaussianWeight x))) ξ =
      ∫ u, (gaussianWeight (ξ-u) : ℂ) * fourier μ u := by
  have hg : Integrable (fun u : ℝ ↦ gaussianWeight (ξ-u)) :=
    integrable_gaussianWeight.comp_sub_left ξ
  have hp : Integrable (fun p : ℝ × ℝ ↦
      (gaussianWeight (ξ-p.1) : ℂ) * fourierPhase p.1 p.2) (volume.prod μ) := by
    apply (hg.comp_fst μ).mono' (by unfold gaussianWeight fourierPhase; fun_prop)
    filter_upwards [] with p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < gaussianWeight (ξ-p.1) from Real.exp_pos _), norm_fourierPhase, mul_one]
  symm
  calc
    _ = ∫ u, ∫ x, (gaussianWeight (ξ-u) : ℂ) * fourierPhase u x ∂μ := by
      simp_rw [fourier_eq_integral_phase, integral_const_mul]
    _ = ∫ x, ∫ u, (gaussianWeight (ξ-u) : ℂ) * fourierPhase u x ∂volume ∂μ :=
      integral_integral_swap hp
    _ = ∫ x, (gaussianWeight x : ℂ) * fourierPhase ξ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hc : (fun u : ℝ ↦ (gaussianWeight (ξ-u) : ℂ) * fourierPhase u x) =
          (fun u : ℝ ↦ (gaussianWeight (ξ-u) : ℂ) * fourierPhase x u) := by
        funext u
        rw [fourierPhase_comm u x]
      rw [hc, gaussianWeight_shift_fourier, mul_comm]
    _ = _ := (fourier_withDensity_gaussian μ ξ).symm

/-- Exact positive-window reproduction of every original unit-supported finite law. -/
theorem fourier_gaussian_reproduction (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : UnitSupported μ) (ξ : ℝ) :
    fourier μ ξ = ∫ u, (gaussianWeight (ξ-u) : ℂ) * fourier (gaussianTiltLaw μ) u := by
  calc
    _ = fourier ((gaussianTiltLaw μ).withDensity
        (fun x ↦ ENNReal.ofReal (gaussianWeight x))) ξ :=
      congrArg (fun ν : Measure ℝ ↦ fourier ν ξ) (gaussianTiltLaw_recover μ hμ).symm
    _ = _ := gaussianWeight_fourier_convolution _ ξ

end Kakeya4.Hard.MultiplicativeConvolution
