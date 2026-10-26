import Kakeya4.Hard.MultiplicativeConvolution.FrostmanExtraction
import Kakeya4.Hard.MultiplicativeConvolution.ProjectionPerturbation
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Actual mass transport into closed neighborhoods, including nonmeasurable sets

The product-rectangle outer-measure identity avoids imposing measurability on
the original test set. Only the target closed thickening is measured by map.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual law is the pushforward of the independent original/noise pair. -/
theorem unitRescaledSmoothLaw_eq_pairMap (κ : SmoothKernel) (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    unitRescaledSmoothLaw κ r μ = (μ.prod κ.law).map (fun p ↦ noisyHalf r p.1 p.2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_unitRescaledSmoothLaw κ μ r hf,
    lintegral_map hf (by unfold noisyHalf; fun_prop), lintegral_prod _ (by unfold noisyHalf; fun_prop)]
  rfl

/-- Unit support is an actual full-mass Borel set of admissible noise samples. -/
theorem SmoothKernel.law_unitSet_mass (κ : SmoothKernel) : κ.law {u : ℝ | |u| ≤ 1} = 1 := by
  exact (mem_ae_iff_prob_eq_one (measurableSet_le (by fun_prop) measurable_const)).mp κ.law_unitSupported

/-- Every original set's outer mass reaches the closed r/2-neighborhood of its half image. -/
theorem unitRescaledSmoothLaw_thickening_mass (κ : SmoothKernel) (μ : Measure ℝ) [SFinite μ]
    {r : ℝ} (hr : 0 ≤ r) (E : Set ℝ) :
    μ E ≤ unitRescaledSmoothLaw κ r μ (cthickening (r/2) ((fun x : ℝ ↦ x/2) '' E)) := by
  rw [unitRescaledSmoothLaw_eq_pairMap,
    Measure.map_apply (by unfold noisyHalf; fun_prop) isClosed_cthickening.measurableSet]
  calc
    _ = μ.prod κ.law (E ×ˢ {u : ℝ | |u| ≤ 1}) := by rw [Measure.prod_prod, κ.law_unitSet_mass, mul_one]
    _ ≤ _ := by
      apply measure_mono
      intro p hp
      change noisyHalf r p.1 p.2 ∈ cthickening (r/2) ((fun x : ℝ ↦ x/2) '' E)
      apply mem_cthickening_of_dist_le _ (p.1/2) _ _ (show p.1/2 ∈ (fun x : ℝ ↦ x/2) '' E from ⟨p.1,hp.1,rfl⟩)
      simpa only [Real.dist_eq] using noisyHalf_error hr hp.2

end Kakeya4.Hard.MultiplicativeConvolution
