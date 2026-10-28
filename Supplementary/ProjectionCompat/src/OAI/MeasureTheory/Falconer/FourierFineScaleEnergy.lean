import OAI.MeasureTheory.Falconer.FourierScaling

/-! Fixed finer-scale input energies, proved from the actual kernel's positive core. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem exists_fixed_finer_profile_domination (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ R δ : ℝ, 2 ≤ R → 0 < δ → ∀ x : ℝ,
      kernelProfile kernel (δ/R) x ≤ ENNReal.ofReal (C*R)*kernelProfile kernel δ x := by
  obtain ⟨M,hM,hheight⟩ := kernel.exists_height
  obtain ⟨m,hm,hcore⟩ := smoothKernel_exists_positive_core kernel
  let C : ℝ := M/m
  refine ⟨C,div_pos hM hm,?_⟩
  intro R δ hR2 hδ x
  have hR : 0 < R := by linarith
  have hfine : 0 < δ/R := div_pos hδ hR
  by_cases hx : δ/R < |x|
  · rw [kernelProfile_zero_of_radius kernel hfine hx]
    exact bot_le
  have hsmall : |x| ≤ δ/2 := (le_of_not_gt hx).trans
    (div_le_div_of_nonneg_left hδ.le (by norm_num) hR2)
  have hprofile := hcore (x/δ) (by
    rw [abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).mpr (by linarith))
  have hcoeff : M ≤ C*kernel.density (x/δ) := by
    have h := mul_le_mul_of_nonneg_left hprofile (div_nonneg hM.le hm.le)
    simpa only [C,div_mul_cancel₀ M hm.ne'] using h
  rw [kernelProfile_eq_ofReal_div kernel hfine,kernelProfile_eq_ofReal_div kernel hδ,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ C*R)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ M/(δ/R) := div_le_div_of_nonneg_right (hheight _) hfine.le
    _ ≤ (C*kernel.density (x/δ))/(δ/R) := div_le_div_of_nonneg_right hcoeff hfine.le
    _ = _ := by field_simp

theorem exists_fixed_finer_smoothLaw_domination (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ R δ : ℝ, 2 ≤ R → 0 < δ →
      smoothLaw kernel.law (δ/R) μ ≤ ENNReal.ofReal (C*R) • smoothLaw kernel.law δ μ := by
  obtain ⟨C,hC,hprofile⟩ := exists_fixed_finer_profile_domination kernel
  refine ⟨C,hC,?_⟩
  intro μ _ R δ hR hδ
  have hRpos : 0 < R := by linarith
  rw [smoothLaw_eq_withDensity kernel μ (div_pos hδ hRpos).ne',smoothLaw_eq_withDensity kernel μ hδ.ne']
  change volume.withDensity (additiveDensity μ (kernelProfile kernel (δ/R))) ≤
    ENNReal.ofReal (C*R) • volume.withDensity (additiveDensity μ (kernelProfile kernel δ))
  rw [← withDensity_smul _ (measurable_additiveDensity μ _ (measurable_kernelProfile kernel δ))]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro x
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (C*R)*kernelProfile kernel δ (x-y) ∂μ :=
      lintegral_mono (fun y ↦ hprofile R δ hR hδ (x-y))
    _ = _ := lintegral_const_mul _ ((measurable_kernelProfile kernel δ).comp (by fun_prop))

theorem exists_fixed_finer_smoothEnergy_bound (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ R δ s : ℝ, 2 ≤ R → 0 < δ →
      smoothEnergy kernel.law s (δ/R) μ ≤ ENNReal.ofReal (C*R^2)*smoothEnergy kernel.law s δ μ := by
  obtain ⟨C,hC,hlaw⟩ := exists_fixed_finer_smoothLaw_domination kernel
  refine ⟨C^2,by positivity,?_⟩
  intro μ _ R δ s hR hδ
  have hRpos : 0 < R := by linarith
  have hb := project_rieszEnergy_le_of_law_le_smul _ _ s _ ENNReal.ofReal_ne_top (hlaw μ R δ hR hδ)
  exact hb.trans_eq (by
    rw [← pow_two,← ENNReal.ofReal_pow (by positivity : 0 ≤ C*R),mul_pow]
    rfl)

#print axioms exists_fixed_finer_profile_domination
#print axioms exists_fixed_finer_smoothLaw_domination
#print axioms exists_fixed_finer_smoothEnergy_bound
end OAI.Falconer
