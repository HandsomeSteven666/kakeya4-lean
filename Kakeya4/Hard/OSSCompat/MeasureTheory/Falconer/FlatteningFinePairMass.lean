






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningPairMass

/-! Fine-radius pair mass keeps the actual delta-scale L2 gain. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem translated_correlation_le_sq_integral (f : ℝ → ℝ≥0∞) (hf : Measurable f) (h : ℝ) :
    (∫⁻ x, f x*f (x+h)) ≤ ∫⁻ x, f x^2 := by
  have hg : Measurable (fun x : ℝ ↦ f (x+h)) := hf.comp (by fun_prop)
  have hc := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show (2:ℝ).HolderConjugate 2 by constructor <;> norm_num) hf.aemeasurable hg.aemeasurable
  simp only [Pi.mul_apply,ENNReal.rpow_two] at hc
  rw [lintegral_add_right_eq_self (fun x ↦ f x^2) h] at hc
  have hs := pow_le_pow_left' hc 2
  have he (a : ℝ≥0∞) : (a^(1/(2:ℝ)))^(2:ℕ)=a := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    norm_num
  rw [mul_pow,he] at hs
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2:ℕ)≠0)).mp
  simpa only [pow_two] using hs

theorem withDensity_closedBall_eq_shift_integral (f : ℝ → ℝ≥0∞) (r x : ℝ) :
    (volume.withDensity f) (closedBall x r) = ∫⁻ h in Icc (-r) r, f (x+h) := by
  rw [withDensity_apply _ measurableSet_closedBall,← lintegral_indicator measurableSet_closedBall,
    ← lintegral_add_left_eq_self ((closedBall x r).indicator f) x,
    ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro h
  have hm : x+h∈closedBall x r ↔ h∈Icc (-r) r := by
    simp only [mem_closedBall,Real.dist_eq,add_sub_cancel_left,mem_Icc,abs_le]
  by_cases hh : h∈Icc (-r) r
  · simp only [indicator_of_mem hh,indicator_of_mem (hm.mpr hh)]
  · simp only [indicator_of_notMem hh,indicator_of_notMem (fun hx ↦ hh (hm.mp hx))]

theorem pairMass_withDensity_le_sq_integral (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {r : ℝ} (_hr : 0 ≤ r) :
    pairMass r (volume.withDensity f) ≤ ENNReal.ofReal (2*r)*(∫⁻ x, f x^2) := by
  have hm : Measurable (fun x : ℝ ↦ ∫⁻ h in Icc (-r) r, f (x+h)) := by fun_prop
  unfold pairMass
  simp_rw [withDensity_closedBall_eq_shift_integral]
  rw [lintegral_withDensity_eq_lintegral_mul volume hf hm]
  have hmul (x : ℝ) : f x*(∫⁻ h in Icc (-r) r, f (x+h)) =
      ∫⁻ h in Icc (-r) r, f x*f (x+h) :=
    (lintegral_const_mul _ (hf.comp (by fun_prop : Measurable (fun h : ℝ ↦ x+h)))).symm
  simp only [Pi.mul_apply]
  simp_rw [hmul]
  rw [lintegral_lintegral_swap (by apply Measurable.aemeasurable; fun_prop)]
  calc
    _ ≤ ∫⁻ _ in Icc (-r) r, ∫⁻ x, f x^2 :=
      lintegral_mono (fun h ↦ translated_correlation_le_sq_integral f hf h)
    _ = _ := by rw [setLIntegral_const,Real.volume_Icc,show r-(-r)=2*r by ring,mul_comm]

theorem smooth_pairMass_fine_radius_bound (kernel : SmoothKernel) (μ : Measure ℝ)
    [SFinite μ] {δ r : ℝ} (hδ : δ ≠ 0) (hr : 0 ≤ r) :
    pairMass r (smoothLaw kernel.law δ μ) ≤
      ENNReal.ofReal (2*r)*densityL2 μ (kernelProfile kernel δ) := by
  rw [smoothLaw_eq_withDensity kernel μ hδ]
  exact pairMass_withDensity_le_sq_integral _
    (measurable_additiveDensity μ _ (measurable_kernelProfile kernel δ)) hr

theorem OSS_original_energy_fine_pairMass (kernel : SmoothKernel) {s t β a : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t ≤ 1) (hβ : 0 < β) (ha : 0 < a) :
    ∃ ε r₀ : ℝ, ∃ K : ℕ, 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 2 ≤ K ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ^a → δ ≤ r₀ →
    ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
      smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
      ∀ k : ℕ, K ≤ k → ∀ r : ℝ, 0 ≤ r →
      pairMass r (smoothLaw kernel.law δ
        (additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k)) ≤
        ENNReal.ofReal (2*r*δ^(s+t-1-β)) := by
  obtain ⟨ε,r₀,K,hε,hr₀,hr₀1,hK,hflat⟩ :=
    OSS_original_energy_intermediate_L2_flattening kernel hs ht hst hβ ha
  refine ⟨ε,r₀,K,hε,hr₀,hr₀1,hK,?_⟩
  intro δ hδ hwindow hδr μ ν _ _ hμU hνU hμE hνE k hk r hr
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have hL := hflat δ δ hδ hδ le_rfl hwindow hδr μ ν hμU hνU hμE hνE k hk
  exact (smooth_pairMass_fine_radius_bound kernel _ hδ.ne' hr).trans
    ((mul_le_mul_right hL _).trans_eq (ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)).symm)

#print axioms translated_correlation_le_sq_integral
#print axioms withDensity_closedBall_eq_shift_integral
#print axioms pairMass_withDensity_le_sq_integral
#print axioms smooth_pairMass_fine_radius_bound
#print axioms OSS_original_energy_fine_pairMass
end OAI.Falconer
