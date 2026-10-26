import Kakeya4.Foundation.Lemmas.QuadraticSublevel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Volume of a quadratic strip with a derivative floor

At fixed time and base coordinate, the allowed hidden coordinate lies in a quadratic
sublevel set with nonvanishing derivative. Integrating the already proved one-dimensional
bound supplies the spatial-volume estimate used by the selector-volume argument.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard

variable {Y : Type*} [MeasurableSpace Y]

/-- A measurable base region and a quadratic strip in its hidden real coordinate. -/
def quadraticStrip (R : Set Y) (a b c : Y → ℝ) (ε B : ℝ) : Set (Y × ℝ) :=
  {p | p.1 ∈ R ∧ |a p.1 * p.2 ^ 2 + b p.1 * p.2 + c p.1| ≤ ε ∧
    B ≤ |2 * a p.1 * p.2 + b p.1|}

theorem measurableSet_quadraticStrip (R : Set Y) (hR : MeasurableSet R)
    (a b c : Y → ℝ) (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (ε B : ℝ) : MeasurableSet (quadraticStrip R a b c ε B) := by
  have hvalue : Measurable (fun p : Y × ℝ => |a p.1 * p.2 ^ 2 + b p.1 * p.2 + c p.1|) := by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] using
      ((((ha.comp measurable_fst).mul (measurable_snd.pow_const 2)).add
        ((hb.comp measurable_fst).mul measurable_snd)).add (hc.comp measurable_fst)).norm
  have hderiv : Measurable (fun p : Y × ℝ => |2 * a p.1 * p.2 + b p.1|) := by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.add_apply, Pi.mul_apply] using
      (((measurable_const.mul (ha.comp measurable_fst)).mul measurable_snd).add
        (hb.comp measurable_fst)).norm
  exact (hR.preimage measurable_fst).inter
    ((measurableSet_le hvalue measurable_const).inter (measurableSet_le measurable_const hderiv))

/-- The spatial volume loss is a derivative-floor factor, independent of all coefficients. -/
theorem measure_quadraticStrip_le (μ : Measure Y) (R : Set Y) (hR : MeasurableSet R)
    (a b c : Y → ℝ) (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    (μ.prod volume) (quadraticStrip R a b c ε B) ≤ ENNReal.ofReal (4 * ε / B) * μ R := by
  rw [Measure.prod_apply (measurableSet_quadraticStrip R hR a b c ha hb hc ε B)]
  calc
    (∫⁻ y, volume (Prod.mk y ⁻¹' quadraticStrip R a b c ε B) ∂μ) ≤
        ∫⁻ y, R.indicator (fun _ => ENNReal.ofReal (4 * ε / B)) y ∂μ := by
      apply lintegral_mono
      intro y
      change volume (Prod.mk y ⁻¹' quadraticStrip R a b c ε B) ≤
        R.indicator (fun _ => ENNReal.ofReal (4 * ε / B)) y
      by_cases hy : y ∈ R
      · rw [Set.indicator_of_mem hy]
        have heq : Prod.mk y ⁻¹' quadraticStrip R a b c ε B =
            {w : ℝ | |a y * w ^ 2 + b y * w + c y| ≤ ε ∧ B ≤ |2 * a y * w + b y|} := by
          ext w
          simp only [quadraticStrip, mem_preimage, mem_ofPred_eq, hy, true_and]
        rw [heq]
        exact Kakeya4.quadratic_sublevel_volume_explicit (a y) (b y) (c y) ε B hε hB
      · have heq : Prod.mk y ⁻¹' quadraticStrip R a b c ε B = ∅ := by
          ext w
          simp only [quadraticStrip, mem_preimage, mem_ofPred_eq, hy, false_and, mem_empty_iff_false]
        rw [heq, measure_empty, Set.indicator_of_notMem hy]
    _ = ENNReal.ofReal (4 * ε / B) * μ R := lintegral_indicator_const hR _

end Kakeya4.Hard
