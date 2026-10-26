import Kakeya4.Hard.MultiplicativeConvolution.GaussianEnvelopeEnergy
import Kakeya4.Hard.MultiplicativeConvolution.LowFrequencyEndpoint
import Mathlib.MeasureTheory.Function.L2Space

/-! # Cauchy--Schwarz on the actual central frequency window -/

noncomputable section
open MeasureTheory Set

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Central part of the actual Gaussian bilinear integral, with no assumed L2 certificate. -/
theorem integral_gaussian_central_le (η ν : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ν] (ξ R : ℝ) :
    (∫ u in Icc (-R) R, ‖fourier η u‖ * gaussianAverage ν ξ u) ≤
      Real.sqrt (∫ u in Icc (-R) R, ‖fourier η u‖^2) *
        Real.sqrt (∫ u, gaussianAverage ν ξ u ^ 2) := by
  have hm : Measurable (fun u ↦ ‖fourier η u‖) := by
    unfold fourier
    fun_prop
  have hf : MemLp (fun u ↦ ‖fourier η u‖) 2 (volume.restrict (Icc (-R) R)) :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr (integrableOn_fourier_sq η R)
  have hg : MemLp (gaussianAverage ν ξ) 2 (volume.restrict (Icc (-R) R)) :=
    (memLp_two_iff_integrable_sq
      (stronglyMeasurable_gaussianAverage ν ξ).aestronglyMeasurable).mpr
        (integrable_gaussianAverage_sq ν ξ).integrableOn
  have hp : (2:ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Filter.Eventually.of_forall (fun u ↦ norm_nonneg (fourier η u)))
    (Filter.Eventually.of_forall (fun u ↦ gaussianAverage_nonneg ν ξ u))
    (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have hsq : (∫ u in Icc (-R) R, gaussianAverage ν ξ u ^ 2) ≤
      ∫ u, gaussianAverage ν ξ u ^ 2 :=
    setIntegral_le_integral (integrable_gaussianAverage_sq ν ξ)
      (Filter.Eventually.of_forall (fun u ↦ sq_nonneg _))
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _))

end Kakeya4.Hard.MultiplicativeConvolution
