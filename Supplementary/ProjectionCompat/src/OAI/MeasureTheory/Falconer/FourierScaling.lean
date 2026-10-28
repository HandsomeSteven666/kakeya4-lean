import OAI.MeasureTheory.Falconer.FourierFlatteningTransfer

/-! Exact physical scaling, with the original noise and Fourier convention. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem map_additive_convolution_mul (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (c : ℝ) :
    (μ ∗ ν).map (fun x : ℝ ↦ c*x) =
      (μ.map (fun x : ℝ ↦ c*x)) ∗ (ν.map (fun x : ℝ ↦ c*x)) := by
  exact Measure.map_conv_continuousLinearMap
    (μ := μ) (ν := ν) (c • ContinuousLinearMap.id ℝ ℝ)

theorem smoothLaw_scale_exact (κ μ : Measure ℝ) [IsFiniteMeasure κ] [IsFiniteMeasure μ]
    (c r : ℝ) :
    smoothLaw κ (c*r) (μ.map (fun x : ℝ ↦ c*x)) =
      (smoothLaw κ r μ).map (fun x : ℝ ↦ c*x) := by
  rw [smoothLaw,smoothLaw,map_additive_convolution_mul,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 2
  funext x
  simp only [Function.comp_apply]
  ring

theorem smoothEnergy_scale_exact (κ μ : Measure ℝ) [IsFiniteMeasure κ] [IsFiniteMeasure μ]
    (s c r : ℝ) :
    smoothEnergy κ s (c*r) (μ.map (fun x : ℝ ↦ c*x)) =
      ENNReal.ofReal |c|^(-s)*smoothEnergy κ s r μ := by
  unfold smoothEnergy
  rw [smoothLaw_scale_exact,rieszEnergy_scale]

theorem normalized_smoothEnergy_exact (kernel : SmoothKernel) (μ : Measure ℝ)
    [IsFiniteMeasure μ] {R : ℝ} (hR : 0 < R) (s δ : ℝ) :
    smoothEnergy kernel.law s (δ/R) (μ.map (fun x : ℝ ↦ x/R)) =
      ENNReal.ofReal (R^s)*smoothEnergy kernel.law s δ μ := by
  have hm : (fun x : ℝ ↦ x/R) = (fun x : ℝ ↦ R⁻¹*x) := by funext x; ring
  rw [hm,show δ/R=R⁻¹*δ by ring,smoothEnergy_scale_exact,abs_of_pos (inv_pos.mpr hR),
    ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hR),Real.inv_rpow hR.le,← Real.rpow_neg hR.le,neg_neg]

theorem fourier_mconv_normalization (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {R : ℝ} (hR : R ≠ 0) (ξ : ℝ) :
    fourier ((μ.map (fun x : ℝ ↦ x/R)) ∗ₘ ν) (R*ξ) = fourier (μ ∗ₘ ν) ξ := by
  rw [fourier_multiplicativeConvolution,fourier_multiplicativeConvolution,
    integral_map (by fun_prop) (by unfold Kakeya4.Hard.MultiplicativeConvolution.fourier; fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  field_simp

theorem normalized_frequency_band {δ R ξ : ℝ} (_hδ : 0 < δ) (hR : 0 < R)
    (hlo : δ⁻¹ ≤ |ξ|) (hhi : |ξ|≤2*δ⁻¹) :
    (δ/R)⁻¹ ≤ |R*ξ| ∧ |R*ξ|≤2*(δ/R)⁻¹ := by
  rw [abs_mul,abs_of_pos hR,inv_div,div_eq_mul_inv]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlo hR.le
  · nlinarith [mul_le_mul_of_nonneg_left hhi hR.le]

#print axioms map_additive_convolution_mul
#print axioms smoothLaw_scale_exact
#print axioms smoothEnergy_scale_exact
#print axioms normalized_smoothEnergy_exact
#print axioms fourier_mconv_normalization
#print axioms normalized_frequency_band
end OAI.Falconer
