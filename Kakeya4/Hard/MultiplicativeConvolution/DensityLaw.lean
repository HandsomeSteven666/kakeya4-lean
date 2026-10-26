import Kakeya4.Hard.MultiplicativeConvolution.NoiseEnergy
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Exact physical densities for the actual smoothing law

This file derives density formulas from the image/convolution definitions using
Mathlib's fixed Lebesgue scaling, withDensity and Tonelli APIs.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual Jacobian-weighted density of a dilated real law. -/
def scaleDensity (p : ℝ → ℝ≥0∞) (r z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |r⁻¹| * p (z / r)

/-- Dilation of a density law, with the full absolute Jacobian. -/
theorem map_withDensity_scale (p : ℝ → ℝ≥0∞) (hp : Measurable p)
    {r : ℝ} (hr : r ≠ 0) :
    (volume.withDensity p).map (fun x ↦ r*x) = volume.withDensity (scaleDensity p r) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun x : ℝ ↦ r*x) := by fun_prop
  have hs : Measurable (scaleDensity p r) := by unfold scaleDensity; fun_prop
  have hfm : Measurable (fun x : ℝ ↦ f (r*x)) := hf.comp hm
  rw [lintegral_map hf hm, lintegral_withDensity_eq_lintegral_mul volume hp hfm,
    lintegral_withDensity_eq_lintegral_mul volume hs hf]
  let g : ℝ → ℝ≥0∞ := fun z ↦ p (z/r) * f z
  have hg : Measurable g := (hp.comp (by fun_prop)).mul hf
  have hchange : (∫⁻ u, g (r*u)) = ENNReal.ofReal |r⁻¹| * ∫⁻ z, g z := by
    rw [← lintegral_map hg hm, Real.map_volume_mul_left hr, lintegral_smul_measure]
    rfl
  calc
    _ = ∫⁻ u, g (r*u) := by
      apply lintegral_congr
      intro u
      simp only [g, Pi.mul_apply, mul_div_cancel_left₀ u hr]
    _ = _ := hchange
    _ = _ := by
      rw [← lintegral_const_mul _ hg]
      apply lintegral_congr
      intro z
      exact (mul_assoc _ _ _).symm

/-- The density of the scaled fixed kernel is exactly the usual r^-1 profile. -/
theorem SmoothKernel.map_law_scale (κ : SmoothKernel) {r : ℝ} (hr : r ≠ 0) :
    κ.law.map (fun x ↦ r*x) = volume.withDensity
      (scaleDensity (fun z ↦ ENNReal.ofReal (κ.density z)) r) := by
  exact map_withDensity_scale _ (κ.smooth.continuous.measurable.ennreal_ofReal) hr

/-- Actual density obtained by adding an independent variable with density p. -/
def additiveDensity (μ : Measure ℝ) (p : ℝ → ℝ≥0∞) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, p (z-x) ∂μ

/-- Joint measurability supplies the density needed for Tonelli. -/
theorem measurable_additiveDensity (μ : Measure ℝ) [SFinite μ]
    (p : ℝ → ℝ≥0∞) (hp : Measurable p) : Measurable (additiveDensity μ p) := by
  unfold additiveDensity
  fun_prop

/-- One-sided density formula; the original law μ may be singular or atomic. -/
theorem conv_withDensity (μ : Measure ℝ) [SFinite μ] (p : ℝ → ℝ≥0∞)
    (hp : Measurable p) :
    μ ∗ volume.withDensity p = volume.withDensity (additiveDensity μ p) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_conv hf,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_additiveDensity μ p hp) hf]
  have hinner (x : ℝ) :
      (∫⁻ y, f (x+y) ∂volume.withDensity p) = ∫⁻ z, p (z-x) * f z := by
    have hfm : Measurable (fun y : ℝ ↦ f (x+y)) := hf.comp (by fun_prop)
    rw [lintegral_withDensity_eq_lintegral_mul volume hp hfm]
    simpa only [add_sub_cancel_left, Pi.mul_apply] using
      (lintegral_add_left_eq_self (fun z ↦ p (z-x) * f z) x)
  simp_rw [hinner]
  rw [lintegral_lintegral_swap (by apply Measurable.aemeasurable; fun_prop)]
  apply lintegral_congr
  intro z
  have hpx : Measurable (fun x : ℝ ↦ p (z-x)) := hp.comp (by fun_prop)
  exact lintegral_mul_const _ hpx

/-- The actual smoothing law has an explicit physical density, with its Jacobian. -/
theorem smoothLaw_eq_withDensity (κ : SmoothKernel) (μ : Measure ℝ) [SFinite μ]
    {r : ℝ} (hr : r ≠ 0) :
    smoothLaw κ.law r μ = volume.withDensity
      (additiveDensity μ (scaleDensity (fun z ↦ ENNReal.ofReal (κ.density z)) r)) := by
  have hκ : Measurable κ.density := κ.smooth.continuous.measurable
  rw [smoothLaw, κ.map_law_scale hr, conv_withDensity]
  unfold scaleDensity
  fun_prop

end Kakeya4.Hard.MultiplicativeConvolution
