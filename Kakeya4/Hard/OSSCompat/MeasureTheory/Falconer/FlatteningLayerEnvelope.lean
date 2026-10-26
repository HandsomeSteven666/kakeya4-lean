






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningDensityLevels

/-! Exact finite layer envelopes and the mass budget of the actual density. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal BigOperators

def densityLayerSum (f : ℝ → ℝ≥0∞) (L : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range L, (densityDyadicLevel f j).indicator (fun _ ↦ (2 : ℝ≥0∞)^j) x

theorem densityLayerSum_eq_of_mem (f : ℝ → ℝ≥0∞) {L j : ℕ} (hj : j < L)
    {x : ℝ} (hx : x ∈ densityDyadicLevel f j) :
    densityLayerSum f L x = (2 : ℝ≥0∞)^j := by
  unfold densityLayerSum
  rw [Finset.sum_eq_single j]
  · exact indicator_of_mem hx _
  · intro i _ hij
    apply indicator_of_notMem
    intro hi
    exact (disjoint_left.mp (densityDyadicLevel_disjoint f hij)) hi hx
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hj)).elim

theorem densityLayerSum_le_density (f : ℝ → ℝ≥0∞) (L : ℕ) (x : ℝ) :
    densityLayerSum f L x ≤ f x := by
  classical
  by_cases h : ∃ j < L, x ∈ densityDyadicLevel f j
  · obtain ⟨j,hj,hx⟩ := h
    rw [densityLayerSum_eq_of_mem f hj hx]
    exact hx.1.le
  · have hz : densityLayerSum f L x = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      apply indicator_of_notMem
      intro hx
      exact h ⟨j,Finset.mem_range.mp hj,hx⟩
    rw [hz]
    exact bot_le

theorem density_le_low_add_two_layerSum (f : ℝ → ℝ≥0∞) (L : ℕ)
    (hheight : ∀ x, f x ≤ (2 : ℝ≥0∞)^L) (x : ℝ) :
    f x ≤ (densityLowLevel f).indicator f x + 2 * densityLayerSum f L x := by
  by_cases hx : f x ≤ 1
  · rw [indicator_of_mem (show x ∈ densityLowLevel f from hx)]
    exact le_add_right le_rfl
  · obtain ⟨j,hj,hlo,hhi⟩ := exists_dyadic_level_of_le_pow L (lt_of_not_ge hx) (hheight x)
    rw [indicator_of_notMem (show x ∉ densityLowLevel f from hx),
      densityLayerSum_eq_of_mem f hj ⟨hlo,hhi⟩,zero_add]
    simpa only [pow_succ'] using hhi

theorem lintegral_densityLayerSum (f : ℝ → ℝ≥0∞) (hf : Measurable f) (L : ℕ) :
    (∫⁻ x, densityLayerSum f L x) =
      ∑ j ∈ Finset.range L, (2 : ℝ≥0∞)^j * volume (densityDyadicLevel f j) := by
  unfold densityLayerSum
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [lintegral_indicator (measurableSet_densityDyadicLevel f hf j),setLIntegral_const]
  · intro j _
    exact ((show Measurable (fun _ : ℝ ↦ (2 : ℝ≥0∞)^j) from measurable_const).indicator
      (measurableSet_densityDyadicLevel f hf j))

theorem density_levels_weighted_mass_le (f : ℝ → ℝ≥0∞) (hf : Measurable f) (L : ℕ) :
    (∑ j ∈ Finset.range L, (2 : ℝ≥0∞)^j * volume (densityDyadicLevel f j)) ≤ ∫⁻ x, f x := by
  rw [← lintegral_densityLayerSum f hf L]
  exact lintegral_mono (densityLayerSum_le_density f L)

theorem lintegral_additiveDensity_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ → ℝ≥0∞) (hp : Measurable p) :
    (∫⁻ z, additiveDensity μ p z) = ∫⁻ z, p z := by
  unfold additiveDensity
  rw [lintegral_lintegral_swap (by apply Measurable.aemeasurable; fun_prop)]
  simp_rw [lintegral_sub_right_eq_self]
  simp

theorem actual_density_levels_weighted_mass_le_one (kernel : SmoothKernel)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {r : ℝ} (hr : r ≠ 0) (L : ℕ) :
    (∑ j ∈ Finset.range L, (2 : ℝ≥0∞)^j *
      volume (densityDyadicLevel (additiveDensity μ (kernelProfile kernel r)) j)) ≤ 1 := by
  have h := density_levels_weighted_mass_le _
    (measurable_additiveDensity μ _ (measurable_kernelProfile kernel r)) L
  rw [lintegral_additiveDensity_probability μ _ (measurable_kernelProfile kernel r),
    kernelProfile_integral kernel hr] at h
  exact h

#print axioms densityLayerSum
#print axioms densityLayerSum_eq_of_mem
#print axioms densityLayerSum_le_density
#print axioms density_le_low_add_two_layerSum
#print axioms lintegral_densityLayerSum
#print axioms density_levels_weighted_mass_le
#print axioms lintegral_additiveDensity_probability
#print axioms actual_density_levels_weighted_mass_le_one
end OAI.Falconer
