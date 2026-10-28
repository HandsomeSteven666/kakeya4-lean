import OAI.MeasureTheory.Falconer.FlatteningBoxComparison

/-! Coarse/fine squared L2 comparison for the same original smooth kernel. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem additiveDensity_nested_eq_conv (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (p : ℝ → ℝ≥0∞) (hp : Measurable p) (x : ℝ) :
    additiveDensity μ (additiveDensity ν p) x = additiveDensity (μ ∗ ν) p x := by
  change (∫⁻ y, ∫⁻ z, p ((x-y)-z) ∂ν ∂μ) = ∫⁻ w, p (x-w) ∂μ ∗ ν
  have hm : Measurable (fun w : ℝ ↦ p (x-w)) := hp.comp (by fun_prop)
  rw [Measure.lintegral_conv hm]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro z
  congr 1
  ring

theorem exists_coarse_density_box_domination (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ r : ℝ, 0 < r → ∀ x : ℝ,
      additiveDensity μ (kernelProfile kernel (4*r)) x ≤ ENNReal.ofReal C *
        additiveDensity (μ ∗ flatteningBoxLaw r) (kernelProfile kernel r) x := by
  obtain ⟨C,hC,hprofile⟩ := exists_coarse_profile_box_domination kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr x
  have := flatteningBoxLaw_probability hr
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal C *
        additiveDensity (flatteningBoxLaw r) (kernelProfile kernel r) (x-y) ∂μ :=
      lintegral_mono (fun y ↦ hprofile r hr (x-y))
    _ = ENNReal.ofReal C *
        additiveDensity μ (additiveDensity (flatteningBoxLaw r) (kernelProfile kernel r)) x :=
      lintegral_const_mul _ ((measurable_additiveDensity _ _
        (measurable_kernelProfile kernel r)).comp (by fun_prop))
    _ = _ := by rw [additiveDensity_nested_eq_conv μ _ _ (measurable_kernelProfile kernel r)]

theorem exists_coarse_densityL2_le_fine (kernel : SmoothKernel) :
    ∃ D : ℝ, 0 < D ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ r : ℝ, 0 < r →
      densityL2 μ (kernelProfile kernel (4*r)) ≤ ENNReal.ofReal D *
        densityL2 μ (kernelProfile kernel r) := by
  obtain ⟨C,hC,hcomp⟩ := exists_coarse_density_box_domination kernel
  refine ⟨C^2,by positivity,?_⟩
  intro μ _ r hr
  have := flatteningBoxLaw_probability hr
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal C *
        additiveDensity (μ ∗ flatteningBoxLaw r) (kernelProfile kernel r) x)^2 :=
      lintegral_mono (fun x ↦ pow_le_pow_left' (hcomp μ r hr x) 2)
    _ = ENNReal.ofReal (C^2) * densityL2 (μ ∗ flatteningBoxLaw r) (kernelProfile kernel r) := by
      simp_rw [mul_pow, ← ENNReal.ofReal_pow hC.le]
      exact lintegral_const_mul _ ((measurable_additiveDensity _ _
        (measurable_kernelProfile kernel r)).pow_const 2)
    _ ≤ _ := mul_le_mul_right (densityL2_conv_probability_le μ (flatteningBoxLaw r)
      _ (measurable_kernelProfile kernel r)) _

theorem exists_actual_cellEnvelope_L2_fine_bound (kernel : SmoothKernel) :
    ∃ D : ℝ, 0 < D ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ r : ℝ, 0 < r →
      (∫⁻ x, flatteningCellEnvelope (additiveDensity μ (kernelProfile kernel r)) r x ^ 2) ≤
        ENNReal.ofReal D * densityL2 μ (kernelProfile kernel r) := by
  obtain ⟨C,hC,hcell⟩ := exists_actual_cellEnvelope_L2_comparison kernel
  obtain ⟨D,hD,hcoarse⟩ := exists_coarse_densityL2_le_fine kernel
  refine ⟨C^2*D,by positivity,?_⟩
  intro μ _ r hr
  calc
    _ ≤ ENNReal.ofReal (C^2) * densityL2 μ (kernelProfile kernel (4*r)) := hcell μ r hr
    _ ≤ ENNReal.ofReal (C^2) * (ENNReal.ofReal D * densityL2 μ (kernelProfile kernel r)) :=
      mul_le_mul_right (hcoarse μ r hr) _
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg C)]

theorem density_dyadic_layer_sq_mass_le (f : ℝ → ℝ≥0∞) (hf : Measurable f) (j : ℕ) :
    ((2 : ℝ≥0∞)^j)^2 * volume (densityDyadicLevel f j) ≤ ∫⁻ x, f x ^ 2 := by
  rw [← lintegral_indicator_const (measurableSet_densityDyadicLevel f hf j)]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ densityDyadicLevel f j
  · rw [indicator_of_mem hx]
    exact pow_le_pow_left' hx.1.le 2
  · rw [indicator_of_notMem hx]
    exact bot_le

theorem exists_actual_cell_layer_sq_mass_bound (kernel : SmoothKernel) :
    ∃ D : ℝ, 0 < D ∧ ∀ (μ : Measure ℝ) [SFinite μ],
      ∀ r : ℝ, 0 < r → ∀ j : ℕ,
      ((2 : ℝ≥0∞)^j)^2 * volume
        (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j) ≤
        ENNReal.ofReal D * densityL2 μ (kernelProfile kernel r) := by
  obtain ⟨D,hD,hcomp⟩ := exists_actual_cellEnvelope_L2_fine_bound kernel
  refine ⟨D,hD,?_⟩
  intro μ _ r hr j
  rw [cellDyadicLevel_eq_envelope_level _ hr]
  exact (density_dyadic_layer_sq_mass_le _ (measurable_flatteningCellEnvelope _ r) j).trans
    (hcomp μ r hr)

#print axioms additiveDensity_nested_eq_conv
#print axioms exists_coarse_density_box_domination
#print axioms exists_coarse_densityL2_le_fine
#print axioms exists_actual_cellEnvelope_L2_fine_bound
#print axioms density_dyadic_layer_sq_mass_le
#print axioms exists_actual_cell_layer_sq_mass_bound
end OAI.Falconer
