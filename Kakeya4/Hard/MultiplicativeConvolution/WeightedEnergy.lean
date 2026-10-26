import Kakeya4.Hard.MultiplicativeConvolution.NoiseEnergy
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Actual bounded changes of input law, preserving the original smoothing scale. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Positive Riesz energy is monotone in its actual input law. -/
theorem rieszEnergy_mono {μ ν : Measure ℝ} (h : μ ≤ ν) (s : ℝ) :
    rieszEnergy s μ ≤ rieszEnergy s ν := by
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, rieszKernel s x y ∂ν ∂μ :=
      lintegral_mono (fun x ↦ lintegral_mono' h le_rfl)
    _ ≤ _ := lintegral_mono' h le_rfl

/-- The actual smoothed energy is monotone, using its proved independent-noise formula. -/
theorem smoothEnergy_mono (κ : Measure ℝ) [SFinite κ] {μ ν : Measure ℝ}
    [SFinite μ] [SFinite ν] (h : μ ≤ ν) (s r : ℝ) :
    smoothEnergy κ s r μ ≤ smoothEnergy κ s r ν := by
  rw [smoothEnergy_eq_noiseKernel, smoothEnergy_eq_noiseKernel]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, noiseKernel κ s r x y ∂ν ∂μ :=
      lintegral_mono (fun x ↦ lintegral_mono' h le_rfl)
    _ ≤ _ := lintegral_mono' h le_rfl

/-- Original unnormalized mass enters the smooth energy quadratically. -/
theorem smoothEnergy_smul (κ : Measure ℝ) [SFinite κ] (μ : Measure ℝ) [SFinite μ]
    (s r : ℝ) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    smoothEnergy κ s r (c • μ) = (c*c) * smoothEnergy κ s r μ := by
  rw [smoothEnergy_eq_noiseKernel, smoothEnergy_eq_noiseKernel]
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hc]
  rw [mul_assoc]

/-- A bounded actual change of law costs the square of its density upper bound. -/
theorem smoothEnergy_le_of_law_le_smul (κ : Measure ℝ) [SFinite κ]
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (s r : ℝ)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (h : ν ≤ c • μ) :
    smoothEnergy κ s r ν ≤ (c*c) * smoothEnergy κ s r μ := by
  exact (smoothEnergy_mono κ h s r).trans_eq (smoothEnergy_smul κ μ s r c hc)

/-- Bounded nonnegative weights produce genuinely dominated measures. -/
theorem withDensity_le_smul (μ : Measure ℝ) (w : ℝ → ℝ≥0∞)
    (c : ℝ≥0∞) (hw : ∀ z, w z ≤ c) : μ.withDensity w ≤ c • μ := by
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall hw)

end Kakeya4.Hard.MultiplicativeConvolution
