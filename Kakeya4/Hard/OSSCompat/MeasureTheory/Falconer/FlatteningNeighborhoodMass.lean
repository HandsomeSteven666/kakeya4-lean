






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningSlowLayerMass
import Mathlib.Topology.MetricSpace.Thickening

/-! From actual interval-layer volume to the original law's neighborhood mass. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem actual_cell_layer_volume_ne_top (kernel : SmoothKernel) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) (j : ℕ) :
    volume (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j) ≠ ⊤ := by
  obtain ⟨B,_,hB⟩ := exists_actual_cell_layer_sq_mass_bound kernel
  obtain ⟨H,_,hH⟩ := kernel.exists_height
  have hE : densityL2 μ (kernelProfile kernel r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (densityL2_kernelProfile_le_height_probability kernel hH μ hr)
  have ha : ((2 : ℝ≥0∞)^j)^2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  have hfinite := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE) (hB μ r hr j)
  intro htop
  rw [htop,ENNReal.mul_top ha] at hfinite
  exact hfinite rfl

theorem smoothLaw_mass_le_original_cthickening (kernel : SmoothKernel)
    (μ : Measure ℝ) [SFinite μ] {r : ℝ} (hr : 0 ≤ r) (A : Set ℝ) (hA : MeasurableSet A) :
    smoothLaw kernel.law r μ A ≤ μ (cthickening r A) := by
  let f : ℝ → ℝ≥0∞ := A.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hnoise (x u : ℝ) (hu : |u| ≤ 1) :
      f (x+r*u) ≤ (cthickening r A).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
    by_cases hpoint : x+r*u ∈ A
    · have hx : x ∈ cthickening r A := by
        apply mem_cthickening_of_dist_le _ (x+r*u) _ _ hpoint
        rw [Real.dist_eq,show x-(x+r*u) = -(r*u) by ring,abs_neg,abs_mul,abs_of_nonneg hr]
        exact (mul_le_mul_of_nonneg_left hu hr).trans_eq (mul_one r)
      simp only [f,indicator_of_mem hpoint,indicator_of_mem hx,le_refl]
    · simp only [f,indicator_of_notMem hpoint]
      exact zero_le
  have hmass : smoothLaw kernel.law r μ A = ∫⁻ x, ∫⁻ u, f (x+r*u) ∂kernel.law ∂μ := by
    calc
      _ = ∫⁻ z, f z ∂smoothLaw kernel.law r μ := by simp [f,lintegral_indicator hA]
      _ = _ := by
        rw [smoothLaw,Measure.lintegral_conv hf]
        apply lintegral_congr
        intro x
        have hm : Measurable (fun z : ℝ ↦ f (x+z)) := hf.comp (by fun_prop)
        exact lintegral_map hm (by fun_prop)
  rw [hmass]
  calc
    _ ≤ ∫⁻ x, ∫⁻ _ : ℝ, (cthickening r A).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂kernel.law ∂μ := by
      apply lintegral_mono
      intro x
      apply lintegral_mono_ae
      filter_upwards [kernel.law_unitSupported] with u hu
      exact hnoise x u hu
    _ = _ := by simp [lintegral_indicator isClosed_cthickening.measurableSet]

theorem exists_actual_cell_layer_original_mass_bound (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ],
      ∀ r : ℝ, 0 < r → ∀ j : ℕ,
      (2 : ℝ≥0∞)^j * volume
        (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j) ≤
      ENNReal.ofReal C * μ (cthickening (4*r)
        (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j)) := by
  obtain ⟨C,hC,hpoint⟩ := exists_actual_cellDyadicLevel_lower_bound kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr j
  let A := flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j
  have hA : MeasurableSet A := measurableSet_flatteningCellDyadicLevel _ r j
  have hd : Measurable (additiveDensity μ (kernelProfile kernel (4*r))) :=
    measurable_additiveDensity μ _ (measurable_kernelProfile kernel (4*r))
  have hmass : (∫⁻ x in A, additiveDensity μ (kernelProfile kernel (4*r)) x) =
      smoothLaw kernel.law (4*r) μ A := by
    rw [smoothLaw_eq_withDensity kernel μ (by positivity : 4*r ≠ 0),withDensity_apply _ hA]
    rfl
  calc
    _ = ∫⁻ _ in A, (2 : ℝ≥0∞)^j := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in A, ENNReal.ofReal C * additiveDensity μ (kernelProfile kernel (4*r)) x := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      exact hpoint μ r hr j x hx
    _ = ENNReal.ofReal C * smoothLaw kernel.law (4*r) μ A := by
      rw [lintegral_const_mul _ hd,hmass]
    _ ≤ _ := mul_le_mul_right
      (smoothLaw_mass_le_original_cthickening kernel μ (by positivity) A hA) _

theorem exists_uniform_original_slow_neighborhood_mass (kernel : SmoothKernel) :
    ∃ M T Q : ℝ, 0 < M ∧ 0 < T ∧ 0 < Q ∧ ∀ r : ℝ, 0 < r → ∃ L : ℕ,
      (2 : ℝ)^L ≤ 2*max 1 (M/r) ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], ∀ q : ℝ≥0∞,
      q*densityL2 μ (kernelProfile kernel r) ≤ densityL2 (μ ∗ μ) (kernelProfile kernel r) →
      densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤ ENNReal.ofReal T * ((L+1 : ℕ) : ℝ≥0∞)^2 ∨
      ∃ j : ℕ, j < L ∧ q ≤ ENNReal.ofReal Q * ((L+1 : ℕ) : ℝ≥0∞)^4 *
        (μ (cthickening (4*r)
          (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j)))^2 := by
  obtain ⟨M,T,Q,hM,hT,hQ,hsel⟩ := exists_uniform_actual_slow_layer_mass kernel
  obtain ⟨C,hC,htransport⟩ := exists_actual_cell_layer_original_mass_bound kernel
  refine ⟨M,T,Q*C^2,hM,hT,by positivity,?_⟩
  intro r hr
  obtain ⟨L,hL,hchoose⟩ := hsel r hr
  refine ⟨L,hL,?_⟩
  intro μ _ q hslow
  rcases hchoose μ q hslow with hlo | ⟨j,hj,hbound⟩
  · exact Or.inl hlo
  right
  refine ⟨j,hj,hbound.trans ?_⟩
  calc
    _ ≤ ENNReal.ofReal Q * ((L+1 : ℕ) : ℝ≥0∞)^4 *
        (ENNReal.ofReal C * μ (cthickening (4*r)
          (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j)))^2 :=
      mul_le_mul_right (pow_le_pow_left' (htransport μ r hr j) 2) _
    _ = _ := by
      rw [ENNReal.ofReal_mul hQ.le,ENNReal.ofReal_pow hC.le,mul_pow]
      ring

#print axioms actual_cell_layer_volume_ne_top
#print axioms smoothLaw_mass_le_original_cthickening
#print axioms exists_actual_cell_layer_original_mass_bound
#print axioms exists_uniform_original_slow_neighborhood_mass
end OAI.Falconer
