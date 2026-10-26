import Kakeya4.Hard.MultiplicativeConvolution.WeightedEnergy
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Bounded Gaussian reweighting for the two-factor argument

On [-1,1], an original law is recovered exactly by multiplying its bounded
tilted law by exp(-pi*x^2). This allows a positive Gaussian Fourier window,
without assuming an auxiliary compact flat-top function has positive Fourier
transform. The tilt is not an extra endpoint input.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual bounded inverse-Gaussian weight on the original support. -/
def gaussianTiltWeight (x : ℝ) : ℝ := if |x| ≤ 1 then Real.exp (Real.pi*x^2) else 0

/-- Actual measure reweighting, without changing or normalizing the original law. -/
def gaussianTiltLaw (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (gaussianTiltWeight x))

/-- The chosen weight is measurable. -/
theorem measurable_gaussianTiltWeight : Measurable gaussianTiltWeight := by
  change Measurable ({x : ℝ | |x| ≤ 1}.piecewise (fun x ↦ Real.exp (Real.pi*x^2)) (fun _ ↦ 0))
  exact Measurable.piecewise (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) measurable_const

/-- Its finite height is universal, independent of the original law or scale. -/
theorem gaussianTiltWeight_le (x : ℝ) : gaussianTiltWeight x ≤ Real.exp Real.pi := by
  unfold gaussianTiltWeight
  split_ifs with hx
  · apply Real.exp_le_exp.mpr
    have hsq : x^2 ≤ 1 := by simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg x) hx 2
    nlinarith [Real.pi_pos]
  · exact (Real.exp_pos _).le

/-- Genuine measure domination for the bounded tilted law. -/
theorem gaussianTiltLaw_le (μ : Measure ℝ) :
    gaussianTiltLaw μ ≤ ENNReal.ofReal (Real.exp Real.pi) • μ := by
  exact withDensity_le_smul μ _ _ (fun x ↦ ENNReal.ofReal_le_ofReal (gaussianTiltWeight_le x))

/-- The tilted law of a finite input is finite, with no density assumption on that input. -/
instance gaussianTiltLaw_isFiniteMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (gaussianTiltLaw μ) := by
  haveI : IsFiniteMeasure (ENNReal.ofReal (Real.exp Real.pi) • μ) := by
    constructor
    simpa only [Measure.smul_apply, smul_eq_mul] using
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)
  exact isFiniteMeasure_of_le (ENNReal.ofReal (Real.exp Real.pi) • μ) (gaussianTiltLaw_le μ)

/-- The original law is recovered exactly by the positive Gaussian weight. -/
theorem gaussianTiltLaw_recover (μ : Measure ℝ) (hμ : UnitSupported μ) :
    (gaussianTiltLaw μ).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-Real.pi*x^2))) = μ := by
  have hw : Measurable (fun x ↦ ENNReal.ofReal (gaussianTiltWeight x)) :=
    measurable_gaussianTiltWeight.ennreal_ofReal
  rw [gaussianTiltLaw, ← withDensity_mul μ hw (by fun_prop)]
  calc
    _ = μ.withDensity (fun _ ↦ 1) := by
      apply withDensity_congr_ae
      filter_upwards [hμ] with x hx
      dsimp only [Pi.mul_apply]
      rw [gaussianTiltWeight, if_pos hx,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      have hz : Real.pi*x^2 + -Real.pi*x^2 = 0 := by ring
      rw [hz]
      simp
    _ = μ := by simp

/-- The actual tilt costs a fixed square-height factor in the original-scale energy. -/
theorem smoothEnergy_gaussianTilt_le (κ : Measure ℝ) [SFinite κ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (s r : ℝ) :
    smoothEnergy κ s r (gaussianTiltLaw μ) ≤
      ENNReal.ofReal (Real.exp (2 * Real.pi)) * smoothEnergy κ s r μ := by
  have h := smoothEnergy_le_of_law_le_smul κ μ (gaussianTiltLaw μ) s r
    (ENNReal.ofReal (Real.exp Real.pi)) ENNReal.ofReal_ne_top (gaussianTiltLaw_le μ)
  have hc : ENNReal.ofReal (Real.exp Real.pi) * ENNReal.ofReal (Real.exp Real.pi) =
      ENNReal.ofReal (Real.exp (2*Real.pi)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    congr 1
    ring
  simpa only [hc] using h

end Kakeya4.Hard.MultiplicativeConvolution
