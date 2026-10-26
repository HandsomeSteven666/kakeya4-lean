import Kakeya4.Hard.MultiplicativeConvolution.DifferenceLaw
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exact Gaussian-weighted Fourier squared moments

The Gaussian characteristic function is reused from fixed Mathlib. Fubini is
applied to actual finite measures with a unit-modulus oscillatory kernel; no
Plancherel or unproved Fourier-energy identity is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Fourier transforms of finite laws are integrable against every finite law. -/
theorem integrable_fourier_against (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fourier μ) ν := by
  apply Integrable.of_bound ((measurable_charFun.comp (by fun_prop)).aestronglyMeasurable)
      (μ.real univ)
  filter_upwards [] with t
  exact norm_charFun_le _

/-- Exact symmetric interchange of the two finite laws in the Fourier kernel. -/
theorem integral_fourier_swap (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ t, fourier μ t ∂ν) = ∫ x, fourier ν x ∂μ := by
  have hi : Integrable (fun p : ℝ × ℝ ↦
      Complex.exp (((-(2 * Real.pi) * p.1 * p.2 : ℝ) : ℂ) * Complex.I)) (ν.prod μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with p
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  simp_rw [fourier_eq_integral]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with t
  congr 2
  push_cast
  ring

/-- Exact difference-law integral for a bounded measurable test function. -/
theorem integral_differenceLaw (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℂ) (hf : Measurable f) (B : ℝ) (hb : ∀ z, ‖f z‖ ≤ B) :
    (∫ z, f z ∂differenceLaw μ) = ∫ x, ∫ y, f (x-y) ∂μ ∂μ := by
  haveI : IsFiniteMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have hfi : Integrable f (differenceLaw μ) :=
    Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hb)
  rw [differenceLaw, integral_conv hfi]
  apply integral_congr_ae
  filter_upwards [] with x
  have hfx : Measurable (fun z : ℝ ↦ f (x+z)) := hf.comp (by fun_prop)
  rw [integral_map (by fun_prop) hfx.aestronglyMeasurable]
  rfl

/-- Mathlib's Gaussian law has the paper's exact negative-2π Fourier transform. -/
theorem fourier_gaussianReal (v : ℝ≥0) (t : ℝ) :
    fourier (ProbabilityTheory.gaussianReal 0 v) t =
      ((Real.exp (-2 * Real.pi ^ 2 * (v : ℝ) * t ^ 2) : ℝ) : ℂ) := by
  rw [fourier, ProbabilityTheory.charFun_gaussianReal]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- A squared Fourier amplitude is the Fourier transform of the genuine difference law. -/
theorem gaussian_fourier_sq_moment (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℝ≥0) :
    (∫ t, ((‖fourier μ t‖ ^ 2 : ℝ) : ℂ) ∂ProbabilityTheory.gaussianReal 0 v) =
      ∫ x, ∫ y, ((Real.exp (-2 * Real.pi ^ 2 * (v : ℝ) * (x-y) ^ 2) : ℝ) : ℂ) ∂μ ∂μ := by
  haveI : IsFiniteMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  simp_rw [← fourier_differenceLaw]
  rw [integral_fourier_swap]
  simp_rw [fourier_gaussianReal]
  apply integral_differenceLaw μ _ (by fun_prop) 1
  intro z
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have hv := v.property
  have hnonneg : 0 ≤ 2 * Real.pi ^ 2 * (v : ℝ) * z ^ 2 := by positivity
  calc
    _ = -(2 * Real.pi ^ 2 * (v : ℝ) * z ^ 2) := by ring
    _ ≤ 0 := neg_nonpos.mpr hnonneg

end Kakeya4.Hard.MultiplicativeConvolution
