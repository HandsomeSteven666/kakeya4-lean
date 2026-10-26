import Kakeya4.Hard.MultiplicativeConvolution.RieszEnergy

/-! Genuine source-law transport of the extended Riesz integral. No toReal is
taken, so atoms and infinite energies are retained throughout. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Tonelli identifies the double energy with the actual product-measure integral. -/
theorem rieszEnergy_eq_lintegral_prod (s : ℝ) (μ : Measure ℝ) [SFinite μ] :
    rieszEnergy s μ = ∫⁻ p : ℝ × ℝ, rieszKernel s p.1 p.2 ∂μ.prod μ := by
  exact (lintegral_prod _ (measurable_rieszKernel s).aemeasurable).symm

/-- Exact energy of a measurable image law, without injectivity or density assumptions. -/
theorem rieszEnergy_map {α : Type*} [MeasurableSpace α] (s : ℝ)
    (μ : Measure α) [SFinite μ] (f : α → ℝ) (hf : Measurable f) :
    rieszEnergy s (μ.map f) =
      ∫⁻ p : α × α, rieszKernel s (f p.1) (f p.2) ∂μ.prod μ := by
  rw [rieszEnergy_eq_lintegral_prod, Measure.map_prod_map μ μ hf hf]
  exact lintegral_map (measurable_rieszKernel s) (hf.prodMap hf)

/-- Translation does not change the distance kernel, including diagonal infinities. -/
theorem rieszKernel_translate (s a x y : ℝ) :
    rieszKernel s (a + x) (a + y) = rieszKernel s x y := by
  unfold rieszKernel
  congr 3
  ring

/-- Riesz energy is translation invariant for arbitrary finite or sigma-finite laws. -/
theorem rieszEnergy_translate (s a : ℝ) (μ : Measure ℝ) [SFinite μ] :
    rieszEnergy s (μ.map (fun x ↦ a + x)) = rieszEnergy s μ := by
  rw [rieszEnergy_map s μ _ (by fun_prop), rieszEnergy_eq_lintegral_prod]
  exact lintegral_congr (fun p ↦ rieszKernel_translate s a p.1 p.2)

/-- Exact dilation of the extended distance kernel. -/
theorem rieszKernel_scale (s c x y : ℝ) :
    rieszKernel s (c * x) (c * y) = ENNReal.ofReal |c| ^ (-s) * rieszKernel s x y := by
  unfold rieszKernel
  rw [show c * x - c * y = c * (x - y) by ring, abs_mul,
    ENNReal.ofReal_mul (abs_nonneg c)]
  exact ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top _

/-- Exact energy scaling, still without discarding infinite values. -/
theorem rieszEnergy_scale (s c : ℝ) (μ : Measure ℝ) [SFinite μ] :
    rieszEnergy s (μ.map (fun x ↦ c * x)) =
      ENNReal.ofReal |c| ^ (-s) * rieszEnergy s μ := by
  rw [rieszEnergy_map s μ _ (by fun_prop), rieszEnergy_eq_lintegral_prod]
  simp_rw [rieszKernel_scale]
  exact lintegral_const_mul _ (measurable_rieszKernel s)

end Kakeya4.Hard.MultiplicativeConvolution
