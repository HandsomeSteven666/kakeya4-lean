import OAI.MeasureTheory.Falconer.FlatteningCorrelation

/-! Actual extra smoothing and the lower bound needed before inverse flattening. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

def flatteningNoiseLaw (kernel : SmoothKernel) (r : ℝ) : Measure ℝ :=
  kernel.law.map (fun x ↦ r*x)

instance flatteningNoiseLaw_probability (kernel : SmoothKernel) (r : ℝ) :
    IsProbabilityMeasure (flatteningNoiseLaw kernel r) := by
  unfold flatteningNoiseLaw
  infer_instance

theorem flatteningNoiseLaw_eq_withDensity (kernel : SmoothKernel) {r : ℝ} (hr : r ≠ 0) :
    flatteningNoiseLaw kernel r = volume.withDensity (kernelProfile kernel r) :=
  kernel.map_law_scale hr

theorem flatteningNoiseLaw_ae_radius (kernel : SmoothKernel) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂flatteningNoiseLaw kernel r, |y| ≤ r := by
  rw [flatteningNoiseLaw_eq_withDensity kernel hr.ne',
    ae_withDensity_iff (measurable_kernelProfile kernel r)]
  filter_upwards [] with y hy
  by_contra h
  exact hy (kernelProfile_zero_of_radius kernel hr (lt_of_not_ge h))

theorem exists_profile_single_le_double_smoothing (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ,
      kernelProfile kernel r x ≤ ENNReal.ofReal C *
        additiveDensity (flatteningNoiseLaw kernel r) (kernelProfile kernel (4*r)) x := by
  obtain ⟨C,hC,hcomp⟩ := exists_kernelProfile_crosspoint_comparison kernel
  refine ⟨C,hC,?_⟩
  intro r hr x
  calc
    _ = ∫⁻ _ : ℝ, kernelProfile kernel r x ∂flatteningNoiseLaw kernel r := by simp
    _ ≤ ∫⁻ y, ENNReal.ofReal C * kernelProfile kernel (4*r) (x-y)
        ∂flatteningNoiseLaw kernel r := by
      apply lintegral_mono_ae
      filter_upwards [flatteningNoiseLaw_ae_radius kernel hr] with y hy
      apply hcomp r hr x (x-y)
      simpa only [sub_sub_cancel] using hy
    _ = _ := lintegral_const_mul _ ((measurable_kernelProfile kernel (4*r)).comp (by fun_prop))

theorem exists_density_single_le_double_smoothing (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ r : ℝ, 0 < r → ∀ x : ℝ,
      additiveDensity μ (kernelProfile kernel r) x ≤ ENNReal.ofReal C *
        additiveDensity (μ ∗ flatteningNoiseLaw kernel r) (kernelProfile kernel (4*r)) x := by
  obtain ⟨C,hC,hprofile⟩ := exists_profile_single_le_double_smoothing kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr x
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal C *
        additiveDensity (flatteningNoiseLaw kernel r) (kernelProfile kernel (4*r)) (x-y) ∂μ :=
      lintegral_mono (fun y ↦ hprofile r hr (x-y))
    _ = ENNReal.ofReal C * additiveDensity μ
        (additiveDensity (flatteningNoiseLaw kernel r) (kernelProfile kernel (4*r))) x :=
      lintegral_const_mul _ ((measurable_additiveDensity _ _
        (measurable_kernelProfile kernel (4*r))).comp (by fun_prop))
    _ = _ := by rw [additiveDensity_nested_eq_conv μ _ _ (measurable_kernelProfile kernel (4*r))]

theorem additiveDensity_withDensity_eq_lconvolution (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (x : ℝ) :
    additiveDensity (volume.withDensity f) g x = (f ⋆ₗ g) x := by
  have hm : Measurable (fun y : ℝ ↦ g (x-y)) := hg.comp (by fun_prop)
  rw [additiveDensity,lintegral_withDensity_eq_lintegral_mul volume hf hm]
  apply lintegral_congr
  intro y
  change f y * g (x-y) = f y * g (-y+x)
  rw [show -y+x = x-y by ring]

theorem actual_smoothed_density_convolution_eq (kernel : SmoothKernel)
    (μ : Measure ℝ) [SFinite μ] {r s : ℝ} (hr : r ≠ 0) (x : ℝ) :
    ((additiveDensity μ (kernelProfile kernel r)) ⋆ₗ
      (additiveDensity μ (kernelProfile kernel s))) x =
    additiveDensity ((μ ∗ μ) ∗ flatteningNoiseLaw kernel r) (kernelProfile kernel s) x := by
  rw [← additiveDensity_withDensity_eq_lconvolution _ _
    (measurable_additiveDensity μ _ (measurable_kernelProfile kernel r))
    (measurable_additiveDensity μ _ (measurable_kernelProfile kernel s))]
  have hμ : volume.withDensity (additiveDensity μ (kernelProfile kernel r)) =
      μ ∗ flatteningNoiseLaw kernel r := by
    rw [flatteningNoiseLaw_eq_withDensity kernel hr,conv_withDensity μ _ (measurable_kernelProfile kernel r)]
  rw [hμ,additiveDensity_nested_eq_conv _ _ _ (measurable_kernelProfile kernel s)]
  congr 1
  rw [Measure.conv_assoc,Measure.conv_comm (flatteningNoiseLaw kernel r) μ,← Measure.conv_assoc]

theorem exists_actual_double_density_lower_bound (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ r : ℝ, 0 < r → ∀ x : ℝ,
      additiveDensity (μ ∗ μ) (kernelProfile kernel r) x ≤ ENNReal.ofReal C *
        ((additiveDensity μ (kernelProfile kernel r)) ⋆ₗ
          (additiveDensity μ (kernelProfile kernel (4*r)))) x := by
  obtain ⟨C,hC,hcomp⟩ := exists_density_single_le_double_smoothing kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr x
  rw [actual_smoothed_density_convolution_eq kernel μ hr.ne']
  exact hcomp (μ ∗ μ) r hr x

theorem exists_actual_smoothed_self_L2_bound (kernel : SmoothKernel) :
    ∃ D : ℝ, 0 < D ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ r : ℝ, 0 < r →
      (∫⁻ x, ((additiveDensity μ (kernelProfile kernel (4*r))) ⋆ₗ
        (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2) ≤
      ENNReal.ofReal D * densityL2 (μ ∗ μ) (kernelProfile kernel r) := by
  obtain ⟨D,hD,hcoarse⟩ := exists_coarse_densityL2_le_fine kernel
  refine ⟨D,hD,?_⟩
  intro μ _ r hr
  simp_rw [actual_smoothed_density_convolution_eq kernel μ (by positivity : 4*r ≠ 0)]
  exact (densityL2_conv_probability_le (μ ∗ μ) (flatteningNoiseLaw kernel (4*r))
    _ (measurable_kernelProfile kernel (4*r))).trans (hcoarse (μ ∗ μ) r hr)

#print axioms flatteningNoiseLaw
#print axioms flatteningNoiseLaw_probability
#print axioms flatteningNoiseLaw_eq_withDensity
#print axioms flatteningNoiseLaw_ae_radius
#print axioms exists_profile_single_le_double_smoothing
#print axioms exists_density_single_le_double_smoothing
#print axioms additiveDensity_withDensity_eq_lconvolution
#print axioms actual_smoothed_density_convolution_eq
#print axioms exists_actual_double_density_lower_bound
#print axioms exists_actual_smoothed_self_L2_bound
end OAI.Falconer
