import OAI.MeasureTheory.Falconer.FlatteningDoubleSmoothing

/-! The actual indicator-convolution estimate used by inverse flattening. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem lintegral_lconvolution_eq_mul (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (f ⋆ₗ g) x) = (∫⁻ x, f x) * (∫⁻ x, g x) := by
  unfold lconvolution
  rw [lintegral_lintegral_swap (by apply Measurable.aemeasurable; fun_prop)]
  have hi (y : ℝ) : (∫⁻ x, f y * g (-y+x)) = f y * (∫⁻ x, g x) := by
    have hm : Measurable (fun x : ℝ ↦ g (-y+x)) := hg.comp (by fun_prop)
    rw [lintegral_const_mul _ hm,lintegral_add_left_eq_self]
  simp_rw [hi]
  exact lintegral_mul_const _ hf

theorem indicator_correlation_le_volume (A : Set ℝ) (hA : MeasurableSet A) (x : ℝ) :
    ((A.indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ
      profileReflect (A.indicator (fun _ ↦ (1 : ℝ≥0∞)))) x ≤ volume A := by
  have hb (z : ℝ) : profileReflect (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) z ≤ 1 := by
    by_cases hz : -z ∈ A <;> simp [profileReflect,hz]
  calc
    _ ≤ ∫⁻ y, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
      apply lintegral_mono
      intro y
      dsimp only
      simpa only [mul_one] using mul_le_mul'
        (le_rfl : A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y)
        (hb (-y+x))
    _ = _ := by rw [lintegral_indicator_const hA,one_mul]

theorem indicator_correlation_integral (A : Set ℝ) (hA : MeasurableSet A) :
    (∫⁻ x, ((A.indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ
      profileReflect (A.indicator (fun _ ↦ (1 : ℝ≥0∞)))) x) = volume A ^ 2 := by
  have hf : Measurable (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) := measurable_const.indicator hA
  rw [lintegral_lconvolution_eq_mul _ _ hf (measurable_profileReflect _ hf)]
  have hr : (∫⁻ x, profileReflect (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) x) = volume A := by
    change (∫⁻ x, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) (-x)) = volume A
    rw [lintegral_neg_eq_self,lintegral_indicator_const hA,one_mul]
  rw [hr,lintegral_indicator_const hA,one_mul,pow_two]

theorem indicator_correlation_sq_integral_le (A : Set ℝ) (hA : MeasurableSet A) :
    (∫⁻ x, (((A.indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ
      profileReflect (A.indicator (fun _ ↦ (1 : ℝ≥0∞)))) x)^2) ≤ volume A ^ 3 := by
  have hf : Measurable (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) := measurable_const.indicator hA
  calc
    _ ≤ ∫⁻ x, volume A * (((A.indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ
        profileReflect (A.indicator (fun _ ↦ (1 : ℝ≥0∞)))) x) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [pow_two]
      exact mul_le_mul' (indicator_correlation_le_volume A hA x) le_rfl
    _ = volume A * volume A ^ 2 := by
      rw [lintegral_const_mul _ (measurable_lconvolution volume hf (measurable_profileReflect _ hf)),
        indicator_correlation_integral A hA]
    _ = _ := (pow_succ' (volume A) 2).symm

theorem exists_indicator_actual_convolution_L2_bound (kernel : SmoothKernel) :
    ∃ D : ℝ, 0 < D ∧ ∀ (μ : Measure ℝ) [SFinite μ],
      ∀ r : ℝ, 0 < r → ∀ A : Set ℝ, MeasurableSet A →
      (∫⁻ x, ((A.indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ
        (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2)^2 ≤
      ENNReal.ofReal D * volume A ^ 3 * densityL2 (μ ∗ μ) (kernelProfile kernel r) := by
  obtain ⟨D,hD,hself⟩ := exists_actual_smoothed_self_L2_bound kernel
  refine ⟨D,hD,?_⟩
  intro μ _ r hr A hA
  have hf : Measurable (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have hg := measurable_additiveDensity μ _ (measurable_kernelProfile kernel (4*r))
  calc
    _ ≤ (∫⁻ x, (((A.indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ
        profileReflect (A.indicator (fun _ ↦ (1 : ℝ≥0∞)))) x)^2) *
        (∫⁻ x, ((additiveDensity μ (kernelProfile kernel (4*r))) ⋆ₗ
          (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2) :=
      lconvolution_sq_integral_squared_le_self_convolution _ _ hf hg
    _ ≤ volume A ^ 3 * (ENNReal.ofReal D * densityL2 (μ ∗ μ) (kernelProfile kernel r)) :=
      mul_le_mul' (indicator_correlation_sq_integral_le A hA) (hself μ r hr)
    _ = _ := by ac_rfl

#print axioms lintegral_lconvolution_eq_mul
#print axioms indicator_correlation_le_volume
#print axioms indicator_correlation_integral
#print axioms indicator_correlation_sq_integral_le
#print axioms exists_indicator_actual_convolution_L2_bound
end OAI.Falconer
