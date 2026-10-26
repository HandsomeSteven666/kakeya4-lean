import Kakeya4.Hard.MultiplicativeConvolution.ProductLaw
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Actual extended-valued Riesz energy

The kernel has value infinity on the diagonal for positive exponents. In
particular an atom is not accidentally assigned zero self-energy by Real.rpow.
Smoothing below is genuine additive convolution with the dilated fixed kernel
law. Smoothness, normalization and selection of a particular approximate identity
are separate obligations; no Fourier decay or flattening assertion is assumed.
Source: arXiv:2309.03068v2, Theorem 1.5 and its notation paragraph.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Extended Riesz kernel, including infinite diagonal singularities. -/
def rieszKernel (s x y : ℝ) : ℝ≥0∞ := ENNReal.ofReal |x - y| ^ (-s)

/-- The genuine nonnegative double Riesz integral. -/
def rieszEnergy (s : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, rieszKernel s x y ∂μ ∂μ

/-- A fixed kernel law dilated to scale r, then added independently to μ. -/
def smoothLaw (κ : Measure ℝ) (r : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  μ ∗ κ.map (fun x ↦ r * x)

/-- Smoothing uses existing convolution and image-law finiteness infrastructure. -/
instance smoothLaw_sfinite (κ : Measure ℝ) [SFinite κ] (r : ℝ) (μ : Measure ℝ)
    [SFinite μ] : SFinite (smoothLaw κ r μ) := by
  unfold smoothLaw
  infer_instance

/-- Smoothed Riesz energy, with the kernel law explicit and fixed. -/
def smoothEnergy (κ : Measure ℝ) (s r : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  rieszEnergy s (smoothLaw κ r μ)

/-- The diagonal carries the true positive-exponent singularity. -/
theorem rieszKernel_self {s : ℝ} (hs : 0 < s) (x : ℝ) :
    rieszKernel s x x = ⊤ := by
  simp only [rieszKernel, sub_self, abs_zero, ENNReal.ofReal_zero]
  exact ENNReal.zero_rpow_of_neg (neg_neg_of_pos hs)

/-- Riesz kernels are symmetric. -/
theorem rieszKernel_comm (s x y : ℝ) : rieszKernel s x y = rieszKernel s y x := by
  simp only [rieszKernel, abs_sub_comm]

/-- Kernel measurability holds across the infinite diagonal as well. -/
theorem measurable_rieszKernel (s : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ rieszKernel s p.1 p.2) := by
  unfold rieszKernel
  fun_prop

/-- A Dirac mass has infinite positive-exponent Riesz energy. -/
theorem rieszEnergy_dirac {s : ℝ} (hs : 0 < s) (x : ℝ) :
    rieszEnergy s (Measure.dirac x) = ⊤ := by
  simp [rieszEnergy, rieszKernel_self hs]

/-- Zero law has zero energy, even though the kernel can be infinite. -/
theorem rieszEnergy_zero (s : ℝ) : rieszEnergy s 0 = 0 := by
  simp [rieszEnergy]

/-- Zero smoothing scale gives back the original law for probability kernel laws. -/
theorem smoothLaw_zero (κ : Measure ℝ) [IsProbabilityMeasure κ] (μ : Measure ℝ)
    [IsFiniteMeasure μ] : smoothLaw κ 0 μ = μ := by
  simp [smoothLaw, Measure.map_const]

/-- Fourier transport through smoothing has the exact rescaled frequency. -/
theorem fourier_smoothLaw (κ μ : Measure ℝ) [IsFiniteMeasure κ]
    [IsFiniteMeasure μ] (r ξ : ℝ) :
    fourier (smoothLaw κ r μ) ξ = fourier μ ξ * fourier κ (r * ξ) := by
  rw [smoothLaw, fourier_additiveConvolution]
  unfold fourier
  rw [charFun_map_mul]
  congr 2
  ring

end Kakeya4.Hard.MultiplicativeConvolution
