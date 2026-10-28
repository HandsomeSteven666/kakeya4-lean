import OAI.MeasureTheory.Falconer.EnergyDifferenceConvolutionPowers
import Kakeya4.Hard.MultiplicativeConvolution.DensityL2
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Actual density contraction for the convolution powers used in OSS Lemma 3.1.
No flattening or energy cap is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem probability_lintegral_sq_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂ν)^2 ≤ ∫⁻ x, f x ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    hf.aemeasurable (show AEMeasurable (fun _ : ℝ ↦ (1 : ℝ≥0∞)) ν from aemeasurable_const)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    measure_univ, mul_one] at h
  have h2 := pow_le_pow_left' h 2
  have he (a : ℝ≥0∞) : (a ^ (1 / (2 : ℝ))) ^ (2 : ℕ) = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simpa only [he, ENNReal.rpow_two] using h2

theorem additiveDensity_conv (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (p : ℝ → ℝ≥0∞) (hp : Measurable p) (z : ℝ) :
    additiveDensity (μ ∗ ν) p z =
      ∫⁻ y, additiveDensity μ p (z-y) ∂ν := by
  have hm : Measurable (fun x : ℝ ↦ p (z-x)) := hp.comp (by fun_prop)
  rw [additiveDensity, Measure.lintegral_conv hm]
  rw [lintegral_lintegral_swap (by apply Measurable.aemeasurable; fun_prop)]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro x
  congr 1
  ring

theorem densityL2_conv_probability_le (μ ν : Measure ℝ)
    [SFinite μ] [IsProbabilityMeasure ν] (p : ℝ → ℝ≥0∞) (hp : Measurable p) :
    densityL2 (μ ∗ ν) p ≤ densityL2 μ p := by
  have hd := measurable_additiveDensity μ p hp
  calc
    _ ≤ ∫⁻ z, ∫⁻ y, additiveDensity μ p (z-y)^2 ∂ν := by
      apply lintegral_mono
      intro z
      dsimp only
      rw [additiveDensity_conv μ ν p hp]
      exact probability_lintegral_sq_le ν _ (hd.comp (by fun_prop))
    _ = ∫⁻ y, ∫⁻ z, additiveDensity μ p (z-y)^2 ∂volume ∂ν :=
      lintegral_lintegral_swap (by apply Measurable.aemeasurable; fun_prop)
    _ = densityL2 μ p := by
      have hshift (y : ℝ) : (∫⁻ z, additiveDensity μ p (z-y)^2) = densityL2 μ p :=
        lintegral_sub_right_eq_self (fun z ↦ additiveDensity μ p z ^ 2) y
      simp_rw [hshift]
      simp

theorem densityL2_additiveLawPower_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ → ℝ≥0∞) (hp : Measurable p) :
    Antitone (fun k ↦ densityL2 (additiveLawPower μ k) p) := by
  apply antitone_nat_of_succ_le
  intro k
  exact densityL2_conv_probability_le (additiveLawPower μ k) μ p hp

/-- Squared physical L2 mass; the exponent counts dyadic doublings, not summands. -/
def flatteningL2Seq (kernel : SmoothKernel) (μ : Measure ℝ) (r : ℝ) (k : ℕ) : ℝ≥0∞ :=
  densityL2 (additiveLawPower μ (2^k)) (kernelProfile kernel r)

theorem flatteningL2Seq_antitone (kernel : SmoothKernel) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (r : ℝ) : Antitone (flatteningL2Seq kernel μ r) := by
  intro a b hab
  apply densityL2_additiveLawPower_antitone μ _ (measurable_kernelProfile kernel r)
  exact Nat.pow_le_pow_right (by norm_num) hab

#print axioms flatteningL2Seq
#print axioms flatteningL2Seq_antitone
#print axioms probability_lintegral_sq_le
#print axioms additiveDensity_conv
#print axioms densityL2_conv_probability_le
#print axioms densityL2_additiveLawPower_antitone
end OAI.Falconer
