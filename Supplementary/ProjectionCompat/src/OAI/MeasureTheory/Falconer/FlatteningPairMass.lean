import OAI.MeasureTheory.Falconer.FlatteningIntermediateL2

/-! The missing reverse direction: actual L2 bounds control actual close-pair mass. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem kernelProfile_core_lower (kernel : SmoothKernel) {m r z : ℝ}
    (hm : ∀ w : ℝ, |w| ≤ 1/2 → m ≤ kernel.density w) (hr : 0 < r) (hz : |z| ≤ r/2) :
    ENNReal.ofReal (m/r) ≤ kernelProfile kernel r z := by
  rw [kernelProfile_eq_ofReal_div kernel hr]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right (hm _ ?_) hr.le
  rw [abs_div,abs_of_pos hr]
  exact (div_le_iff₀ hr).mpr (by linarith)

theorem densityPairKernel_core_lower (kernel : SmoothKernel) {m r : ℝ}
    (hm0 : 0 < m) (hm : ∀ w : ℝ, |w| ≤ 1/2 → m ≤ kernel.density w)
    (hr : 0 < r) (x y : ℝ) (hxy : |x-y| ≤ r) :
    ENNReal.ofReal (m^2/(8*r)) ≤ densityPairKernel (kernelProfile kernel (4*r)) x y := by
  let A : Set ℝ := Icc (x-r) (x+r)
  have hpoint : ∀ z ∈ A, ENNReal.ofReal (m/(4*r))^2 ≤
      kernelProfile kernel (4*r) (z-x) * kernelProfile kernel (4*r) (z-y) := by
    intro z hz
    have hzx : |z-x| ≤ r := abs_le.mpr (by constructor <;> linarith [hz.1,hz.2])
    have hzy : |z-y| ≤ 2*r := by
      calc
        _ = |(z-x)+(x-y)| := by congr 1; ring
        _ ≤ |z-x|+|x-y| := abs_add_le _ _
        _ ≤ 2*r := by linarith
    simpa only [pow_two] using mul_le_mul'
      (kernelProfile_core_lower kernel hm (by positivity : 0 < 4*r) (by linarith : |z-x| ≤ (4*r)/2))
      (kernelProfile_core_lower kernel hm (by positivity : 0 < 4*r) (by linarith : |z-y| ≤ (4*r)/2))
  have hint : (∫⁻ z in A, ENNReal.ofReal (m/(4*r))^2) = ENNReal.ofReal (m^2/(8*r)) := by
    rw [setLIntegral_const]
    dsimp [A]
    rw [Real.volume_Icc,show x+r-(x-r)=2*r by ring,
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ m/(4*r)),
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    field_simp [hr.ne']
    ring
  rw [← hint]
  calc
    _ ≤ ∫⁻ z in A, kernelProfile kernel (4*r) (z-x)*kernelProfile kernel (4*r) (z-y) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      exact hpoint z hz
    _ ≤ _ := setLIntegral_le_lintegral _ _

theorem exists_pairMass_le_actual_L2 (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ r : ℝ, 0 < r →
      pairMass r μ ≤ ENNReal.ofReal (C*r)*densityL2 μ (kernelProfile kernel (4*r)) := by
  obtain ⟨m,hm0,hm⟩ := smoothKernel_exists_positive_core kernel
  let C : ℝ := 8/m^2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro μ _ r hr
  have hlower : ENNReal.ofReal (m^2/(8*r))*pairMass r μ ≤
      densityL2 μ (kernelProfile kernel (4*r)) := by
    rw [densityL2_eq_pairKernel μ _ (measurable_kernelProfile kernel (4*r)),pairMass]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    dsimp only
    rw [← setLIntegral_const,← lintegral_indicator measurableSet_closedBall]
    apply lintegral_mono
    intro y
    by_cases hy : y∈closedBall x r
    · rw [indicator_of_mem hy]
      exact densityPairKernel_core_lower kernel hm0 hm hr x y
        (by simpa only [mem_closedBall,Real.dist_eq,abs_sub_comm] using hy)
    · rw [indicator_of_notMem hy]
      exact bot_le
  have hcancel : ENNReal.ofReal (C*r)*ENNReal.ofReal (m^2/(8*r))=1 := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C*r)]
    have heq : C*r*(m^2/(8*r))=1 := by
      dsimp [C]
      field_simp [hm0.ne',hr.ne']
    rw [heq,ENNReal.ofReal_one]
  have h := mul_le_mul_right hlower (ENNReal.ofReal (C*r))
  simpa only [← mul_assoc,hcancel,one_mul] using h

theorem exists_smooth_pairMass_le_actual_L2 (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ δ r : ℝ, 0 < r →
      pairMass r (smoothLaw kernel.law δ μ) ≤
        ENNReal.ofReal (C*r)*densityL2 μ (kernelProfile kernel (4*r)) := by
  obtain ⟨C,hC,hpair⟩ := exists_pairMass_le_actual_L2 kernel
  refine ⟨C,hC,?_⟩
  intro μ _ δ r hr
  have : SFinite (smoothLaw kernel.law δ μ) := by unfold smoothLaw; infer_instance
  have hd : densityL2 (smoothLaw kernel.law δ μ) (kernelProfile kernel (4*r)) ≤
      densityL2 μ (kernelProfile kernel (4*r)) := by
    change densityL2 (μ ∗ flatteningNoiseLaw kernel δ) _ ≤ _
    exact densityL2_conv_probability_le μ _ _ (measurable_kernelProfile kernel (4*r))
  exact (hpair (smoothLaw kernel.law δ μ) r hr).trans (mul_le_mul_right hd _)

theorem OSS_original_energy_intermediate_pairMass (kernel : SmoothKernel) {s t β a : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t ≤ 1) (hβ : 0 < β) (ha : 0 < a) :
    ∃ C ε r₀ : ℝ, ∃ K : ℕ, 0 < C ∧ 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 2 ≤ K ∧
    ∀ δ r : ℝ, 0 < δ → 0 < r → δ ≤ 4*r → 4*r ≤ δ^a → 4*r ≤ r₀ →
    ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
      smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
      ∀ k : ℕ, K ≤ k →
      pairMass r (smoothLaw kernel.law δ
        (additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k)) ≤
        ENNReal.ofReal (C*r*(4*r)^(s+t-1-β)) := by
  obtain ⟨C,hC,hpair⟩ := exists_smooth_pairMass_le_actual_L2 kernel
  obtain ⟨ε,r₀,K,hε,hr₀,hr₀1,hK,hflat⟩ :=
    OSS_original_energy_intermediate_L2_flattening kernel hs ht hst hβ ha
  refine ⟨C,ε,r₀,K,hC,hε,hr₀,hr₀1,hK,?_⟩
  intro δ r hδ hr hδr hwindow hrr μ ν _ _ hμU hνU hμE hνE k hk
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have hb := hflat δ (4*r) hδ (by positivity) hδr hwindow hrr μ ν hμU hνU hμE hνE k hk
  exact (hpair _ δ r hr).trans ((mul_le_mul_right hb _).trans_eq
    (ENNReal.ofReal_mul (by positivity : 0 ≤ C*r)).symm)

#print axioms kernelProfile_core_lower
#print axioms densityPairKernel_core_lower
#print axioms exists_pairMass_le_actual_L2
#print axioms exists_smooth_pairMass_le_actual_L2
#print axioms OSS_original_energy_intermediate_pairMass
end OAI.Falconer
