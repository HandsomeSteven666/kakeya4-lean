import Kakeya4.Hard.MultiplicativeConvolution.NoiseEnergy

/-!
# Pair small-ball mass controlled by true smoothed energy

The measure is not assumed to have a density or to satisfy a Frostman bound.
These are consequences of the original energy, not extra endpoint hypotheses.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Probability/mass of two independent draws being within distance R. -/
def pairMass (R : ℝ) (μ : Measure ℝ) : ℝ≥0∞ := ∫⁻ x, μ (closedBall x R) ∂μ

/-- Kernel lower bound on a physical ball. -/
theorem cappedKernel_ge_on_ball {s r R x y : ℝ} (hs : 0 ≤ s) (hrR : r ≤ R)
    (hy : y ∈ closedBall x R) :
    ENNReal.ofReal R ^ (-s) ≤ cappedKernel s r x y := by
  apply ennreal_neg_rpow_antitone hs
  apply ENNReal.ofReal_le_ofReal
  apply max_le hrR
  simpa only [mem_closedBall, Real.dist_eq, abs_sub_comm] using hy

/-- Integrating over a ball retains the actual mass of that ball. -/
theorem ballMass_le_cappedPotential {s r R : ℝ} (hs : 0 ≤ s) (hrR : r ≤ R)
    (μ : Measure ℝ) (x : ℝ) :
    ENNReal.ofReal R ^ (-s) * μ (closedBall x R) ≤
      ∫⁻ y, cappedKernel s r x y ∂μ := by
  rw [← setLIntegral_const (closedBall x R), ← lintegral_indicator measurableSet_closedBall]
  apply lintegral_mono
  intro y
  by_cases hy : y ∈ closedBall x R
  · rw [indicator_of_mem hy]
    exact cappedKernel_ge_on_ball hs hrR hy
  · rw [indicator_of_notMem hy]
    exact bot_le

/-- The genuine pair close-encounter mass is controlled by capped energy. -/
theorem pairMass_le_cappedEnergy {s r R : ℝ} (hs : 0 ≤ s) (hR : 0 < R)
    (hrR : r ≤ R) (μ : Measure ℝ) :
    ENNReal.ofReal R ^ (-s) * pairMass R μ ≤ cappedEnergy s r μ := by
  have hC : ENNReal.ofReal R ^ (-s) ≠ ⊤ := by
    rw [ENNReal.ofReal_rpow_of_pos hR]
    exact ENNReal.ofReal_ne_top
  rw [pairMass, ← lintegral_const_mul' _ _ hC]
  exact lintegral_mono (fun x ↦ ballMass_le_cappedPotential hs hrR μ x)

/-- Close encounters of the original law are bounded by the original smooth energy. -/
theorem pairMass_le_smoothEnergy (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : UnitSupported κ) (μ : Measure ℝ) [SFinite μ] {s r R : ℝ}
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hR : 0 < R) (hrR : r ≤ R) :
    ENNReal.ofReal (3*R) ^ (-s) * pairMass R μ ≤ smoothEnergy κ s r μ := by
  have hmul : ENNReal.ofReal (3*R) ^ (-s) =
      ENNReal.ofReal 3 ^ (-s) * ENNReal.ofReal R ^ (-s) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
    exact ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top _
  rw [hmul, mul_assoc]
  exact (mul_le_mul_right (pairMass_le_cappedEnergy hs hR hrR μ) _).trans
    (smoothEnergy_ge_capped κ hκ μ hs hr)

end Kakeya4.Hard.MultiplicativeConvolution
