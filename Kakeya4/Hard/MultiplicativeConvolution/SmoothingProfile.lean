import Kakeya4.Hard.MultiplicativeConvolution.DensityLaw

/-! Quantitative support, mass and height of the actual scaled smooth kernel. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The physical-scale density appearing in the proved smoothing-law identity. -/
def kernelProfile (κ : SmoothKernel) (r : ℝ) : ℝ → ℝ≥0∞ :=
  scaleDensity (fun z ↦ ENNReal.ofReal (κ.density z)) r

/-- Compact support and continuity provide a fixed height before all scales/laws. -/
theorem SmoothKernel.exists_height (κ : SmoothKernel) :
    ∃ M : ℝ, 0 < M ∧ ∀ x, κ.density x ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image
    (κ.smooth.continuous.continuousOn : ContinuousOn κ.density (Icc (-1) 1))
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x ↦ ?_⟩
  by_cases hx : |x| ≤ 1
  · exact (hM (mem_image_of_mem _ (abs_le.mp hx))).trans (le_max_right _ _)
  · rw [κ.outside x (lt_of_not_ge hx)]
    exact (zero_le_one.trans (le_max_left _ _))

/-- Jointly measurable actual kernel at a fixed scale. -/
theorem measurable_kernelProfile (κ : SmoothKernel) (r : ℝ) : Measurable (kernelProfile κ r) := by
  have hκ : Measurable κ.density := κ.smooth.continuous.measurable
  unfold kernelProfile scaleDensity
  fun_prop

/-- The exact physical profile is normalized at every nonzero scale. -/
theorem kernelProfile_integral (κ : SmoothKernel) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ z, kernelProfile κ r z = 1 := by
  have h := congrArg (fun ν : Measure ℝ ↦ ν univ) (κ.map_law_scale hr)
  simpa only [Measure.map_apply (measurable_const_mul r) MeasurableSet.univ, preimage_univ,
    measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    kernelProfile] using h.symm

/-- A fixed density height M becomes the expected M/|r| height. -/
theorem kernelProfile_le (κ : SmoothKernel) {M : ℝ} (hM : ∀ x, κ.density x ≤ M)
    (r z : ℝ) : kernelProfile κ r z ≤ ENNReal.ofReal |r⁻¹| * ENNReal.ofReal M := by
  unfold kernelProfile scaleDensity
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hM _)) _

/-- No spurious tails: the physical kernel vanishes outside radius r. -/
theorem kernelProfile_zero_of_radius (κ : SmoothKernel) {r z : ℝ} (hr : 0 < r)
    (hz : r < |z|) : kernelProfile κ r z = 0 := by
  have h : 1 < |z/r| := by rw [abs_div, abs_of_pos hr, one_lt_div hr]; exact hz
  dsimp only [kernelProfile, scaleDensity]
  rw [κ.outside _ h]
  simp

end Kakeya4.Hard.MultiplicativeConvolution
