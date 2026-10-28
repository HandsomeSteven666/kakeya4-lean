import OAI.MeasureTheory.Falconer.FlatteningLayerConvolution

/-! A genuine finite layer is selected from the convolution of the actual density. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal BigOperators

theorem finite_layer_convolution_selection (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (L : ℕ)
    (hfg : ∀ x, f x ≤ g x) (hheight : ∀ x, g x ≤ (2 : ℝ≥0∞)^L)
    (hf1 : (∫⁻ x, f x) ≤ 1) (hh1 : (∫⁻ x, h x) = 1) :
    (∫⁻ x, (f ⋆ₗ h) x ^ 2) ≤ ((L+1 : ℕ) : ℝ≥0∞)^2 ∨
    ∃ j : ℕ, j < L ∧ (∫⁻ x, (f ⋆ₗ h) x ^ 2) ≤
      ((L+1 : ℕ) : ℝ≥0∞)^2 * ((2 : ℝ≥0∞)^(j+1))^2 *
        ∫⁻ x, (((densityDyadicLevel g j).indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ h) x ^ 2 := by
  let F : Fin (L+1) → ℝ → ℝ≥0∞ := Fin.cons (densityLowPart f g ⋆ₗ h)
    (fun j : Fin L ↦ fun x ↦ (2 : ℝ≥0∞)^((j:ℕ)+1) *
      (((densityDyadicLevel g j).indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ h) x)
  have hF : ∀ i, Measurable (F i) := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact measurable_lconvolution volume (measurable_densityLowPart f g hf hg) hh
    · exact measurable_const.mul (measurable_lconvolution volume
        (measurable_const.indicator (measurableSet_densityDyadicLevel g hg j)) hh)
  have hb (x : ℝ) : (f ⋆ₗ h) x ≤ ∑ i, F i x := by
    have hb := lconvolution_le_lowPart_add_layers f g h hf hg hh L hfg hheight x
    convert hb using 1
    dsimp [F]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,pow_succ']
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ (2 : ℝ≥0∞) * 2^j *
      (((densityDyadicLevel g j).indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ h) x) L]
    simp only [mul_assoc,Finset.mul_sum]
  obtain ⟨i,hi⟩ := exists_fin_large_sq_integral (by omega : 0 < L+1) _ F hF hb
  obtain rfl | ⟨j,rfl⟩ := i.eq_zero_or_eq_succ
  · left
    exact hi.trans (by
      simp only [F,Fin.cons_zero]
      simpa only [mul_one] using mul_le_mul_right
        (lowPart_convolution_sq_integral_le_one f g h hf hg hh hfg hf1 hh1)
        (((L+1 : ℕ) : ℝ≥0∞)^2))
  · right
    refine ⟨j,j.isLt,?_⟩
    simp only [F,Fin.cons_succ] at hi
    simp_rw [mul_pow] at hi
    rw [lintegral_const_mul _ ((measurable_lconvolution volume
      (measurable_const.indicator (measurableSet_densityDyadicLevel g hg j)) hh).pow_const 2)] at hi
    simpa only [mul_assoc] using hi

theorem actual_layer_convolution_selection (kernel : SmoothKernel) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) (L : ℕ)
    (hheight : ∀ x, flatteningCellEnvelope (additiveDensity μ (kernelProfile kernel r)) r x ≤
      (2 : ℝ≥0∞)^L) :
    (∫⁻ x, ((additiveDensity μ (kernelProfile kernel r)) ⋆ₗ
      (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2) ≤ ((L+1 : ℕ) : ℝ≥0∞)^2 ∨
    ∃ j : ℕ, j < L ∧
      (∫⁻ x, ((additiveDensity μ (kernelProfile kernel r)) ⋆ₗ
        (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2) ≤
      ((L+1 : ℕ) : ℝ≥0∞)^2 * ((2 : ℝ≥0∞)^(j+1))^2 *
        ∫⁻ x, (((flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j).indicator
          (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2 := by
  have hf := measurable_additiveDensity μ _ (measurable_kernelProfile kernel r)
  have hh := measurable_additiveDensity μ _ (measurable_kernelProfile kernel (4*r))
  have hf1 : (∫⁻ x, additiveDensity μ (kernelProfile kernel r) x) = 1 := by
    rw [lintegral_additiveDensity_probability μ _ (measurable_kernelProfile kernel r),kernelProfile_integral kernel hr.ne']
  have hh1 : (∫⁻ x, additiveDensity μ (kernelProfile kernel (4*r)) x) = 1 := by
    rw [lintegral_additiveDensity_probability μ _ (measurable_kernelProfile kernel (4*r)),
      kernelProfile_integral kernel (by positivity : 4*r ≠ 0)]
  have hsel := finite_layer_convolution_selection _ _ _ hf (measurable_flatteningCellEnvelope _ r) hh L
    (density_le_flatteningCellEnvelope _ hr) hheight hf1.le hh1
  simpa only [← cellDyadicLevel_eq_envelope_level _ hr] using hsel

theorem exists_uniform_actual_double_layer_selection (kernel : SmoothKernel) :
    ∃ M D : ℝ, 0 < M ∧ 0 < D ∧ ∀ r : ℝ, 0 < r → ∃ L : ℕ,
      (2 : ℝ)^L ≤ 2*max 1 (M/r) ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤
        ENNReal.ofReal D * ((L+1 : ℕ) : ℝ≥0∞)^2 ∨
      ∃ j : ℕ, j < L ∧ densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤
        ENNReal.ofReal D * ((L+1 : ℕ) : ℝ≥0∞)^2 * ((2 : ℝ≥0∞)^(j+1))^2 *
        ∫⁻ x, (((flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j).indicator
          (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2 := by
  obtain ⟨C,hC,hcomp⟩ := exists_actual_double_density_lower_bound kernel
  obtain ⟨M,hM,hcut⟩ := exists_actual_cellEnvelope_finite_height kernel
  refine ⟨M,C^2,hM,by positivity,?_⟩
  intro r hr
  obtain ⟨L,hL,hheight⟩ := hcut r hr
  refine ⟨L,hL,?_⟩
  intro μ _
  have hb : densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤ ENNReal.ofReal (C^2) *
      ∫⁻ x, ((additiveDensity μ (kernelProfile kernel r)) ⋆ₗ
        (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2 := by
    calc
      _ ≤ ∫⁻ x, (ENNReal.ofReal C * ((additiveDensity μ (kernelProfile kernel r)) ⋆ₗ
          (additiveDensity μ (kernelProfile kernel (4*r)))) x)^2 :=
        lintegral_mono (fun x ↦ pow_le_pow_left' (hcomp μ r hr x) 2)
      _ = _ := by
        simp_rw [mul_pow, ← ENNReal.ofReal_pow hC.le]
        exact lintegral_const_mul _ ((measurable_lconvolution volume
          (measurable_additiveDensity μ _ (measurable_kernelProfile kernel r))
          (measurable_additiveDensity μ _ (measurable_kernelProfile kernel (4*r)))).pow_const 2)
  rcases actual_layer_convolution_selection kernel μ hr L (hheight μ) with hlo | ⟨j,hj,hhi⟩
  · exact Or.inl (hb.trans (mul_le_mul_right hlo _))
  · right
    refine ⟨j,hj,?_⟩
    simpa only [mul_assoc] using hb.trans (mul_le_mul_right hhi (ENNReal.ofReal (C^2)))

#print axioms finite_layer_convolution_selection
#print axioms actual_layer_convolution_selection
#print axioms exists_uniform_actual_double_layer_selection
end OAI.Falconer
