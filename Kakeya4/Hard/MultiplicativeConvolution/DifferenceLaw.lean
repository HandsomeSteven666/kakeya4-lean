import Kakeya4.Hard.MultiplicativeConvolution.FourierJensen

/-!
# Difference laws and OSS Lemma 4.1

The Fourier transform on the right side of the source inequality is real and
nonnegative. We express its real part explicitly in Lean and prove the exact
identity with the average squared Fourier amplitude before using Jensen.
-/

noncomputable section
open MeasureTheory

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The law of X-X' for independent copies of the same input law. -/
def differenceLaw (μ : Measure ℝ) : Measure ℝ := μ ∗ μ.map (fun x ↦ -x)

/-- Reflection conjugates the Fourier transform in the chosen convention. -/
theorem fourier_reflect (μ : Measure ℝ) (ξ : ℝ) :
    fourier (μ.map (fun x ↦ -x)) ξ = star (fourier μ ξ) := by
  have h : μ.map (fun x ↦ -x) = μ.map (fun x ↦ (-1 : ℝ) * x) := by
    congr 1
    funext x
    ring
  rw [h]
  unfold fourier
  rw [charFun_map_mul]
  convert charFun_neg (μ := μ) (-(2 * Real.pi) * ξ) using 1 <;> congr 1 <;> ring

/-- The transform of the genuine difference law is the squared amplitude. -/
theorem fourier_differenceLaw (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    fourier (differenceLaw μ) ξ = ((‖fourier μ ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [differenceLaw, fourier_additiveConvolution, fourier_reflect]
  simpa only [Complex.ofReal_pow, starRingEnd_apply] using Complex.mul_conj' (fourier μ ξ)

/-- The source right-hand Fourier value is exactly a real nonnegative average. -/
theorem fourier_difference_mconv (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ξ : ℝ) :
    fourier (differenceLaw μ ∗ₘ ν) ξ =
      ((∫ x, ‖fourier μ (ξ * x)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
  haveI : IsProbabilityMeasure (differenceLaw μ) := by
    unfold differenceLaw
    infer_instance
  rw [Measure.mconv_comm, fourier_multiplicativeConvolution]
  simp_rw [fourier_differenceLaw]
  exact integral_ofReal

/-- OSS Lemma 4.1 for arbitrary Borel probability laws, including mass at zero. -/
theorem norm_fourier_mconv_sq_le_difference (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ξ : ℝ) :
    ‖fourier (μ ∗ₘ ν) ξ‖ ^ 2 ≤ (fourier (differenceLaw μ ∗ₘ ν) ξ).re := by
  rw [fourier_difference_mconv, Complex.ofReal_re]
  simpa only [Measure.mconv_comm μ ν] using norm_fourier_mconv_sq_le ν μ ξ

end Kakeya4.Hard.MultiplicativeConvolution
