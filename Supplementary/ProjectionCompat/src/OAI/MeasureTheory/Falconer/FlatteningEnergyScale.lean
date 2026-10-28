import OAI.MeasureTheory.Falconer.FlatteningEnergyContraction

/-! Uniform larger-scale control for the original nontruncated smooth Riesz energy. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem flatteningBox_fine_profile_eq (kernel : SmoothKernel) {δ R : ℝ}
    (hδ : 0 < δ) (hδR : δ ≤ R) {x : ℝ} (hx : |x| ≤ 4*R) :
    additiveDensity (flatteningBoxLaw R) (kernelProfile kernel δ) x =
      (ENNReal.ofReal (10*R))⁻¹ := by
  have hs : Function.support (fun y ↦ kernelProfile kernel δ (x-y)) ⊆ Icc (-5*R) (5*R) := by
    intro y hy
    have hxy : |x-y| ≤ δ := by
      by_contra h
      exact hy (kernelProfile_zero_of_radius kernel hδ (lt_of_not_ge h))
    have hyabs : |y| ≤ 5*R := by
      calc
        _ = |(y-x)+x| := by congr 1; ring
        _ ≤ |y-x|+|x| := abs_add_le _ _
        _ ≤ 5*R := by rw [abs_sub_comm y x]; linarith
    simpa only [mem_Icc,neg_mul] using abs_le.mp hyabs
  rw [additiveDensity,flatteningBoxLaw_eq,lintegral_smul_measure,
    setLIntegral_eq_of_support_subset hs,lintegral_sub_left_eq_self,
    kernelProfile_integral kernel hδ.ne',smul_eq_mul,mul_one]

theorem exists_larger_profile_fine_box_domination (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ R : ℝ, 0 < δ → δ ≤ R → ∀ x : ℝ,
      kernelProfile kernel R x ≤ ENNReal.ofReal C *
        additiveDensity (flatteningBoxLaw R) (kernelProfile kernel δ) x := by
  obtain ⟨M,hM0,hM⟩ := kernel.exists_height
  refine ⟨10*M,by positivity,?_⟩
  intro δ R hδ hδR x
  have hR : 0 < R := hδ.trans_le hδR
  by_cases hx : R < |x|
  · rw [kernelProfile_zero_of_radius kernel hR hx]
    exact bot_le
  rw [flatteningBox_fine_profile_eq kernel hδ hδR (by linarith [le_of_not_gt hx]),
    kernelProfile_eq_ofReal_div kernel hR,← div_eq_mul_inv,
    ← ENNReal.ofReal_div_of_pos (by positivity : 0 < 10*R)]
  apply ENNReal.ofReal_le_ofReal
  have heq : (10*M)/(10*R) = M/R := by field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right (hM _) hR.le

theorem exists_larger_density_fine_box_domination (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      ∀ δ R : ℝ, 0 < δ → δ ≤ R → ∀ x : ℝ,
      additiveDensity μ (kernelProfile kernel R) x ≤ ENNReal.ofReal C *
        additiveDensity (μ ∗ flatteningBoxLaw R) (kernelProfile kernel δ) x := by
  obtain ⟨C,hC,hprofile⟩ := exists_larger_profile_fine_box_domination kernel
  refine ⟨C,hC,?_⟩
  intro μ _ δ R hδ hδR x
  have := flatteningBoxLaw_probability (hδ.trans_le hδR)
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal C *
        additiveDensity (flatteningBoxLaw R) (kernelProfile kernel δ) (x-y) ∂μ :=
      lintegral_mono (fun y ↦ hprofile δ R hδ hδR (x-y))
    _ = ENNReal.ofReal C *
        additiveDensity μ (additiveDensity (flatteningBoxLaw R) (kernelProfile kernel δ)) x :=
      lintegral_const_mul _ ((measurable_additiveDensity _ _
        (measurable_kernelProfile kernel δ)).comp (by fun_prop))
    _ = _ := by rw [additiveDensity_nested_eq_conv μ _ _ (measurable_kernelProfile kernel δ)]

theorem exists_larger_smoothLaw_fine_box_domination (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      ∀ δ R : ℝ, 0 < δ → δ ≤ R →
      smoothLaw kernel.law R μ ≤ ENNReal.ofReal C •
        ((smoothLaw kernel.law δ μ) ∗ flatteningBoxLaw R) := by
  obtain ⟨C,hC,hdensity⟩ := exists_larger_density_fine_box_domination kernel
  refine ⟨C,hC,?_⟩
  intro μ _ δ R hδ hδR
  have := flatteningBoxLaw_probability (hδ.trans_le hδR)
  have hcomm : smoothLaw kernel.law δ (μ ∗ flatteningBoxLaw R) =
      (smoothLaw kernel.law δ μ) ∗ flatteningBoxLaw R := by
    unfold smoothLaw
    rw [Measure.conv_assoc,Measure.conv_comm (flatteningBoxLaw R) _,← Measure.conv_assoc]
  rw [← hcomm,smoothLaw_eq_withDensity kernel μ (hδ.trans_le hδR).ne',
    smoothLaw_eq_withDensity kernel (μ ∗ flatteningBoxLaw R) hδ.ne']
  change volume.withDensity (additiveDensity μ (kernelProfile kernel R)) ≤
    ENNReal.ofReal C • volume.withDensity (additiveDensity (μ ∗ flatteningBoxLaw R) (kernelProfile kernel δ))
  have hfine := measurable_additiveDensity (μ ∗ flatteningBoxLaw R) _ (measurable_kernelProfile kernel δ)
  rw [← withDensity_smul _ hfine]
  apply withDensity_mono
  exact Filter.Eventually.of_forall (hdensity μ δ R hδ hδR)

theorem exists_uniform_larger_smoothEnergy_bound (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      ∀ δ R s : ℝ, 0 < δ → δ ≤ R → 0 < s → s < 1 →
      smoothEnergy kernel.law s R μ ≤ ENNReal.ofReal C * smoothEnergy kernel.law s δ μ := by
  obtain ⟨C,hC,hlaw⟩ := exists_larger_smoothLaw_fine_box_domination kernel
  refine ⟨C^2,by positivity,?_⟩
  intro μ _ δ R s hδ hδR hs hs1
  have := flatteningBoxLaw_probability (hδ.trans_le hδR)
  have : IsFiniteMeasure (smoothLaw kernel.law δ μ) := by unfold smoothLaw; infer_instance
  calc
    _ ≤ (ENNReal.ofReal C * ENNReal.ofReal C) *
        rieszEnergy s ((smoothLaw kernel.law δ μ) ∗ flatteningBoxLaw R) :=
      project_rieszEnergy_le_of_law_le_smul _ _ s _ ENNReal.ofReal_ne_top (hlaw μ δ R hδ hδR)
    _ ≤ (ENNReal.ofReal C * ENNReal.ofReal C) * rieszEnergy s (smoothLaw kernel.law δ μ) :=
      mul_le_mul_right (project_rieszEnergy_conv_probability_le _ _ hs hs1) _
    _ = _ := by rw [← pow_two,← ENNReal.ofReal_pow hC.le]; rfl

#print axioms flatteningBox_fine_profile_eq
#print axioms exists_larger_profile_fine_box_domination
#print axioms exists_larger_density_fine_box_domination
#print axioms exists_larger_smoothLaw_fine_box_domination
#print axioms exists_uniform_larger_smoothEnergy_bound
end OAI.Falconer
