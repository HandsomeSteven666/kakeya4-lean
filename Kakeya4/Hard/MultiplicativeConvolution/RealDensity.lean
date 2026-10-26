import Kakeya4.Hard.MultiplicativeConvolution.SmoothEnergyL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real-valued density and genuine L2 membership

The nonnegative density is proved finite pointwise before taking toReal. Thus
infinite values are never erased to establish a real-valued estimate.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Actual convolution density has the height bound with the original total mass. -/
theorem additiveDensity_le_height (μ : Measure ℝ) (p : ℝ → ℝ≥0∞)
    {A : ℝ≥0∞} (hpA : ∀ z, p z ≤ A) (z : ℝ) :
    additiveDensity μ p z ≤ A * μ Set.univ := by
  calc
    _ ≤ ∫⁻ _ : ℝ, A ∂μ := lintegral_mono (fun x ↦ hpA (z-x))
    _ = _ := lintegral_const _

/-- The actual density is finite at every point for finite original laws. -/
theorem kernel_additiveDensity_ne_top (κ : SmoothKernel) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (r z : ℝ) : additiveDensity μ (kernelProfile κ r) z ≠ ⊤ := by
  obtain ⟨M,_,hM⟩ := κ.exists_height
  apply ne_top_of_le_ne_top _ (additiveDensity_le_height μ _ (kernelProfile_le κ hM r) z)
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (measure_ne_top μ _)

/-- The finite actual density converted to an ordinary nonnegative real function. -/
def realSmoothDensity (κ : SmoothKernel) (r : ℝ) (μ : Measure ℝ) (z : ℝ) : ℝ :=
  (additiveDensity μ (kernelProfile κ r) z).toReal

/-- The real density is a measurable function, including for atomic input laws. -/
theorem measurable_realSmoothDensity (κ : SmoothKernel) (μ : Measure ℝ) [SFinite μ]
    (r : ℝ) : Measurable (realSmoothDensity κ r μ) :=
  (measurable_additiveDensity μ _ (measurable_kernelProfile κ r)).ennreal_toReal

/-- Its nonnegativity is pointwise. -/
theorem realSmoothDensity_nonneg (κ : SmoothKernel) (μ : Measure ℝ) (r z : ℝ) :
    0 ≤ realSmoothDensity κ r μ z := ENNReal.toReal_nonneg

/-- Recovering the original extended density loses no mass or infinite value. -/
theorem ofReal_realSmoothDensity (κ : SmoothKernel) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (r z : ℝ) :
    ENNReal.ofReal (realSmoothDensity κ r μ z) = additiveDensity μ (kernelProfile κ r) z :=
  ENNReal.ofReal_toReal (kernel_additiveDensity_ne_top κ μ r z)

/-- This real density represents exactly the original convolution smoothing law. -/
theorem smoothLaw_eq_realDensity (κ : SmoothKernel) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : r ≠ 0) :
    smoothLaw κ.law r μ = volume.withDensity (fun z ↦ ENNReal.ofReal (realSmoothDensity κ r μ z)) := by
  rw [smoothLaw_eq_withDensity κ μ hr]
  congr 1
  funext z
  exact (ofReal_realSmoothDensity κ μ r z).symm

/-- Genuine L2 membership follows from the original finite energy, with no extra hypothesis. -/
theorem realSmoothDensity_memLp_two (κ : SmoothKernel) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (hE : smoothEnergy κ.law s r μ ≠ ⊤) :
    MemLp (realSmoothDensity κ r μ) 2 volume := by
  have hm := measurable_realSmoothDensity κ μ r
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have heq : (∫⁻ z, ENNReal.ofReal ‖realSmoothDensity κ r μ z ^ 2‖) =
      densityL2 μ (kernelProfile κ r) := by
    apply lintegral_congr
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      ENNReal.ofReal_pow (realSmoothDensity_nonneg κ μ r z), ofReal_realSmoothDensity]
  rw [heq]
  exact lt_top_iff_ne_top.mpr (densityL2_ne_top_of_energy κ μ hs hr hE)

/-- The nonnegative extended integral is exactly the ordinary finite squared L2 integral. -/
theorem ofReal_integral_realSmoothDensity_sq (κ : SmoothKernel) (μ : Measure ℝ)
    [IsFiniteMeasure μ] {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (hE : smoothEnergy κ.law s r μ ≠ ⊤) :
    ENNReal.ofReal (∫ z, realSmoothDensity κ r μ z ^ 2) = densityL2 μ (kernelProfile κ r) := by
  have hf := (realSmoothDensity_memLp_two κ μ hs hr hE).integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))]
  apply lintegral_congr
  intro z
  rw [ENNReal.ofReal_pow (realSmoothDensity_nonneg κ μ r z), ofReal_realSmoothDensity]

/-- Ordinary real squared L2 estimate with a constant preceding every input measure. -/
theorem exists_realSmoothDensity_L2_bound (κ : SmoothKernel) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ), 0 < r →
      smoothEnergy κ.law s r μ ≠ ⊤ →
      (∫ z, realSmoothDensity κ r μ z ^ 2) ≤
        C * r ^ (s-1) * (smoothEnergy κ.law s r μ).toReal := by
  obtain ⟨C,hCpos,hC⟩ := exists_smooth_density_L2_bound κ hs
  refine ⟨C,hCpos,?_⟩
  intro μ _ r hr hE
  have heq := ofReal_integral_realSmoothDensity_sq κ μ hs hr hE
  have hb := hC μ r hr
  rw [← heq] at hb
  have hfin : ENNReal.ofReal (C * r ^ (s-1)) * smoothEnergy κ.law s r μ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE
  have h := ENNReal.toReal_mono hfin hb
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hCpos.le (Real.rpow_nonneg hr.le _)),
    ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ sq_nonneg _))] at h
  exact h

end Kakeya4.Hard.MultiplicativeConvolution
