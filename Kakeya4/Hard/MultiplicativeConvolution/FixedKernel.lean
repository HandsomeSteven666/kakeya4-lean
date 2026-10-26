import Kakeya4.Hard.MultiplicativeConvolution.EndpointStatement
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A fixed actual smooth probability kernel

Reuse Mathlib's normalized smooth bump, with inner radius 1/2 and outer radius 1.
This eliminates any kernel-existence assumption from the H-004 target. Equivalence
with a different chosen approximate identity in the source still requires a
quantitative energy comparison; it is not assumed here.
-/

noncomputable section
open MeasureTheory

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- A dimension-independent fixed bump profile on the real line. -/
def fixedBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The actual normalized smooth kernel used in this development. -/
def fixedKernel : SmoothKernel where
  density := fixedBump.normed volume
  smooth := fixedBump.contDiff_normed
  nonneg := fixedBump.nonneg_normed
  outside := by
    intro x hx
    rw [ContDiffBump.normed_def, fixedBump.zero_of_le_dist]
    · exact zero_div _
    · simpa [fixedBump, Real.dist_eq] using hx.le
  positive := by
    intro x hx
    apply div_pos _ (fixedBump.integral_pos (μ := volume))
    rw [fixedBump.one_of_mem_closedBall]
    · norm_num
    · simpa [fixedBump, Metric.mem_closedBall, Real.dist_eq] using hx
  integrable := fixedBump.integrable_normed
  integral_one := fixedBump.integral_normed

/-- This kernel exists outright; it is not an unproved witness parameter. -/
theorem smoothKernel_nonempty : Nonempty SmoothKernel := ⟨fixedKernel⟩

/-- The chosen kernel is symmetric, as in the source's real-line smoothing. -/
theorem fixedKernel_even (x : ℝ) : fixedKernel.density (-x) = fixedKernel.density x :=
  fixedBump.normed_neg x

/-- Fixed normalization of the explicit profile. -/
theorem fixedKernel_integral_one : ∫ x, fixedKernel.density x = 1 :=
  fixedKernel.integral_one

/-- The non-vacuous full H-004 target for this fixed smooth kernel; unproved. -/
def ManuscriptDecay : Prop := FiniteScaleDecay fixedKernel

end Kakeya4.Hard.MultiplicativeConvolution
