





import Kakeya4.Hard.SpectralCompat.Causalean.Stat.CLT.BerryEsseen.SmoothingKernel
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Real.Pi.Bounds

/-! Local bridge from the pinned Apache-2.0 sinc kernel to the majorant
required by manuscript re:flat-coefficients. Frequencies here are radians. -/

noncomputable section
open MeasureTheory Set
open Causalean.Stat.CLT.BerryEsseen

namespace Kakeya4.Hard.MultiplicativeConvolution

theorem exists_generatedCoefficientMajorant :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Integrable ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∀ x, |x| ≤ 1 → 1 ≤ ψ x) ∧
      ∀ t : ℝ, 1 ≤ |t| →
        (∫ x : ℝ, Complex.exp (((t*x : ℝ) : ℂ) * Complex.I) * (ψ x : ℂ)) = 0 := by
  have hs : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → 0 < Real.sinc z := by
    intro z hz hz1
    by_cases hz0 : z = 0
    · simp [hz0]
    have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    rw [Real.sinc_of_ne_zero hz0]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hzpos
      (hz1.trans_lt (by linarith [Real.pi_gt_three]))) hzpos
  have hpositive : ∀ x : ℝ, |x| ≤ 1 → 0 < sinc4Kernel 1 x := by
    intro x hx
    have ha : Real.sinc (|x|/4) = Real.sinc (x/4) := by
      by_cases hx0 : 0 ≤ x
      · rw [abs_of_nonneg hx0]
      · rw [abs_of_neg (lt_of_not_ge hx0), neg_div, Real.sinc_neg]
    have hsx := hs (|x|/4) (by positivity) (by linarith)
    rw [ha] at hsx
    simp only [sinc4Kernel, one_mul]
    positivity
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
    (f := sinc4Kernel 1) (show (Icc (-1:ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
    (by unfold sinc4Kernel; fun_prop)
  have hm : 0 < sinc4Kernel 1 a := hpositive a (abs_le.mpr ha)
  let ψ : ℝ → ℝ := fun x ↦ (sinc4Kernel 1 a)⁻¹ * sinc4Kernel 1 x
  refine ⟨ψ, ?_, (sinc4Kernel_integrable 1 (by norm_num)).const_mul _, ?_, ?_, ?_⟩
  · dsimp [ψ]
    unfold sinc4Kernel
    fun_prop
  · intro x
    exact mul_nonneg (inv_nonneg.mpr hm.le) (sinc4Kernel_nonneg 1 (by norm_num) x)
  · intro x hx
    calc
      1 = (sinc4Kernel 1 a)⁻¹ * sinc4Kernel 1 a := (inv_mul_cancel₀ hm.ne').symm
      _ ≤ ψ x := mul_le_mul_of_nonneg_left (hmin (abs_le.mp hx)) (inv_nonneg.mpr hm.le)
  · intro t ht
    have heq : (fun x : ℝ ↦ Complex.exp (((t*x : ℝ) : ℂ) * Complex.I) * (ψ x : ℂ)) =
        fun x : ℝ ↦ ((sinc4Kernel 1 a)⁻¹ : ℂ) *
          (Complex.exp (((t*x : ℝ) : ℂ) * Complex.I) * (sinc4Kernel 1 x : ℂ)) := by
      funext x
      dsimp [ψ]
      push_cast
      ring
    rw [heq, integral_const_mul, sinc4Kernel_fourier_eq_zero 1 t (by norm_num) ht, mul_zero]

#print axioms exists_generatedCoefficientMajorant

/-- The same actual majorant in the project's negative-2π Fourier convention. -/
theorem exists_generatedCoefficientFourierMajorant :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Integrable ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∀ x, |x| ≤ 1 → 1 ≤ ψ x) ∧
      ∀ ξ : ℝ, 1 ≤ |ξ| → FourierTransform.fourier (fun x ↦ (ψ x : ℂ)) ξ = 0 := by
  obtain ⟨ψ, hc, hi, hn, hm, hz⟩ := exists_generatedCoefficientMajorant
  refine ⟨ψ, hc, hi, hn, hm, ?_⟩
  intro ξ hξ
  have hband : 1 ≤ |(-(2 * Real.pi)) * ξ| := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    calc
      1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      _ ≤ (2 * Real.pi) * |ξ| := le_mul_of_one_le_right (by positivity) hξ
  rw [Real.fourier_eq']
  convert hz (-(2 * Real.pi) * ξ) hband using 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, RCLike.inner_apply', starRingEnd_apply, star_trivial]
  congr 2
  push_cast
  ring

#print axioms exists_generatedCoefficientFourierMajorant

/-- The compact spectral support supplies the second L¹ hypothesis of inversion. -/
theorem exists_generatedCoefficientInversionMajorant :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Integrable ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∀ x, |x| ≤ 1 → 1 ≤ ψ x) ∧
      Integrable (FourierTransform.fourier (fun x ↦ (ψ x : ℂ))) ∧
      (∀ ξ : ℝ, 1 ≤ |ξ| → FourierTransform.fourier (fun x ↦ (ψ x : ℂ)) ξ = 0) ∧
      ∀ x : ℝ, (ψ x : ℂ) = FourierTransform.fourierInv
        (FourierTransform.fourier (fun y ↦ (ψ y : ℂ))) x := by
  obtain ⟨ψ, hc, hi, hn, hm, hz⟩ := exists_generatedCoefficientFourierMajorant
  have hfcont : Continuous (FourierTransform.fourier (fun x ↦ (ψ x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi.ofReal
  have hsupp : Function.support (FourierTransform.fourier (fun x ↦ (ψ x : ℂ))) ⊆
      Icc (-1:ℝ) 1 := by
    intro ξ hξ
    have hlt : |ξ| < 1 := by
      by_contra hh
      exact hξ (hz ξ (le_of_not_gt hh))
    exact abs_le.mp hlt.le
  have hfi : Integrable (FourierTransform.fourier (fun x ↦ (ψ x : ℂ))) :=
    (integrableOn_iff_integrable_of_support_subset hsupp).mp hfcont.integrableOn_Icc
  refine ⟨ψ, hc, hi, hn, hm, hfi, hz, ?_⟩
  intro x
  exact (hi.ofReal.fourierInv_fourier_eq hfi
    (show ContinuousAt (fun y ↦ (ψ y : ℂ)) x from
      (Complex.continuous_ofReal.comp hc).continuousAt)).symm

#print axioms exists_generatedCoefficientInversionMajorant
end Kakeya4.Hard.MultiplicativeConvolution
