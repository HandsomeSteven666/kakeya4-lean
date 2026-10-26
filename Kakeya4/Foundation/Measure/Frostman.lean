import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# The Frostman mass distribution principle

If a measure `μ` gives mass at most `C * (diam s) ^ d` to every set of diameter at most one,
and `μ E ≠ 0`, then the `d`-dimensional Hausdorff measure of `E` is nonzero, hence
`dimH E ≥ d`.

This is the "diameter form" of the mass distribution principle (Frostman 1935). It is the form
used in the Kakeya reduction: the weighted estimates produce diameter bounds directly. The
ball form follows by the usual covering argument; it is recorded as a TODO below.

The proof is a direct application of `MeasureTheory.Measure.le_hausdorffMeasure`: after
normalising `μ` by `C`, the hypothesis is exactly the hypothesis of that lemma.
-/

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal

namespace Kakeya4

/-- **Frostman mass distribution principle** (diameter form).

Let `E` be a set in an extended metric space, `μ` a measure with `μ E ≠ 0`, and `d ≥ 0`.
If every set `s` with `ediam s ≤ 1` satisfies `μ s ≤ C * (ediam s) ^ d`, then
`dimH E ≥ d`. -/
theorem frostman_mass_distribution
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {E : Set X} {μ : Measure X} {d : ℝ≥0} {C : ℝ}
    (hC : 0 < C) (hμE : μ E ≠ 0)
    (hμ : ∀ s : Set X, ediam s ≤ 1 → μ s ≤ ENNReal.ofReal C * ediam s ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimH E := by
  set C' : ℝ≥0∞ := ENNReal.ofReal C with hC'
  have hC0 : C' ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hC
  have hCtop : C' ≠ ∞ := ENNReal.ofReal_ne_top
  let ν : Measure X := C'⁻¹ • μ
  have hν : ν ≤ μH[(d : ℝ)] := by
    refine le_hausdorffMeasure (d : ℝ) ν 1 (by norm_num) ?_
    intro s hs
    have h := hμ s hs
    calc
      ν s = C'⁻¹ * μ s := rfl
      _ ≤ C'⁻¹ * (C' * ediam s ^ (d : ℝ)) := by gcongr
      _ = ediam s ^ (d : ℝ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCtop, one_mul]
  have hνE : ν E ≠ 0 := by
    dsimp [ν]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hCtop) hμE
  have hμH : μH[(d : ℝ)] E ≠ 0 := by
    intro h0
    have hle : ν E ≤ μH[(d : ℝ)] E := hν E
    rw [h0] at hle
    exact hνE (le_zero_iff.mp hle)
  exact le_dimH_of_hausdorffMeasure_ne_zero (d := d) (by simpa using hμH)

end Kakeya4
