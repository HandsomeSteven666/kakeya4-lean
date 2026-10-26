





import Kakeya4.Hard.MultiplicativeConvolution.GeneratedMajorant
import Kakeya4.Hard.MultiplicativeConvolution.ProductLaw
import Kakeya4.Hard.MultiplicativeConvolution.GeneratedLaw
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

noncomputable section
open MeasureTheory

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Fourier inversion may be integrated against the original finite law.
No density or absolute continuity assumption is imposed on that law. -/
theorem integral_scaledMajorant_eq_fourier (ψ : ℝ → ℝ) (hi : Integrable ψ)
    (hfi : Integrable (FourierTransform.fourier (fun y ↦ (ψ y : ℂ))))
    (hinv : ∀ x : ℝ, (ψ x : ℂ) = FourierTransform.fourierInv
      (FourierTransform.fourier (fun y ↦ (ψ y : ℂ))) x)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (x h : ℝ) :
    (∫ u : ℝ, (ψ ((u-x)/h) : ℂ) ∂ν) =
      ∫ t : ℝ, Complex.exp (((-2*Real.pi*x/h*t : ℝ) : ℂ) * Complex.I) *
        FourierTransform.fourier (fun y ↦ (ψ y : ℂ)) t * fourier ν (-t/h) := by
  let F := FourierTransform.fourier (fun y ↦ (ψ y : ℂ))
  let G : ℝ → ℝ → ℂ := fun u t ↦
    Complex.exp (((2*Real.pi*((u-x)/h)*t : ℝ) : ℂ) * Complex.I) * F t
  have hFc : Continuous F := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi.ofReal
  have hbound : Integrable (fun p : ℝ × ℝ ↦ (1:ℝ) * ‖F p.2‖) (ν.prod volume) :=
    (integrable_const (1:ℝ)).mul_prod hfi.norm
  have hG : Integrable (Function.uncurry G) (ν.prod volume) := by
    apply hbound.mono'
    · have hc : Continuous (Function.uncurry G) := by dsimp [G]; fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards with p
      dsimp [G, Function.uncurry]
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_rfl
  have hpoint (u : ℝ) : (ψ ((u-x)/h) : ℂ) = ∫ t : ℝ, G u t := by
    rw [hinv, Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with t
    dsimp [G]
    simp only [starRingEnd_apply, star_trivial]
    congr 2
    push_cast
    ring
  simp_rw [hpoint]
  rw [integral_integral_swap hG]
  apply integral_congr_ae
  filter_upwards with t
  have heq : (fun u : ℝ ↦ G u t) = fun u : ℝ ↦
      (Complex.exp (((-2*Real.pi*x/h*t : ℝ) : ℂ) * Complex.I) * F t) *
        Complex.exp (((-(2*Real.pi)*(-t/h)*u : ℝ) : ℂ) * Complex.I) := by
    funext u
    dsimp [G]
    have he : (((2*Real.pi*((u-x)/h)*t : ℝ) : ℂ) * Complex.I) =
        (((-2*Real.pi*x/h*t : ℝ) : ℂ) * Complex.I) +
        (((-(2*Real.pi)*(-t/h)*u : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [he, Complex.exp_add]
    ring
  rw [heq, integral_const_mul, fourier_eq_integral]

#print axioms integral_scaledMajorant_eq_fourier

/-- The literal closed interval mass is controlled by a compactly supported
spectral majorant. The original finite measure need not have a density. -/
theorem closedInterval_mass_le_spectralMajorant (ψ : ℝ → ℝ) (hc : Continuous ψ)
    (hi : Integrable ψ) (hn : ∀ u, 0 ≤ ψ u) (hm : ∀ u, |u| ≤ 1 → 1 ≤ ψ u)
    (hfi : Integrable (FourierTransform.fourier (fun y ↦ (ψ y : ℂ))))
    (hinv : ∀ x : ℝ, (ψ x : ℂ) = FourierTransform.fourierInv
      (FourierTransform.fourier (fun y ↦ (ψ y : ℂ))) x)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ν.real (Set.Icc (x-h) (x+h)) ≤
      ∫ t : ℝ, ‖FourierTransform.fourier (fun y ↦ (ψ y : ℂ)) t‖ * ‖fourier ν (-t/h)‖ := by
  let F := FourierTransform.fourier (fun y ↦ (ψ y : ℂ))
  have hnorm (u : ℝ) : ‖ψ ((u-x)/h)‖ ≤ ∫ t : ℝ, ‖F t‖ := by
    have hiu := hinv ((u-x)/h)
    have he : ‖ψ ((u-x)/h)‖ = ‖(ψ ((u-x)/h) : ℂ)‖ := by simp
    rw [he, hiu, Real.fourierInv_eq']
    apply (norm_integral_le_integral_norm _).trans_eq
    congr 1
    funext t
    simp only [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rfl
  have hscaled : Integrable (fun u : ℝ ↦ ψ ((u-x)/h)) ν := by
    apply (integrable_const (∫ t : ℝ, ‖F t‖)).mono'
    · have hcont : Continuous (fun u : ℝ ↦ ψ ((u-x)/h)) := by fun_prop
      exact hcont.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hnorm
  have hmass : ν.real (Set.Icc (x-h) (x+h)) ≤ ∫ u : ℝ, ψ ((u-x)/h) ∂ν := by
    rw [← integral_indicator_one measurableSet_Icc]
    apply integral_mono ((integrable_const (1:ℝ)).indicator measurableSet_Icc) hscaled
    intro u
    by_cases hu : u ∈ Set.Icc (x-h) (x+h)
    · rw [Set.indicator_of_mem hu]
      apply hm
      rw [abs_le]
      constructor
      · exact (le_div_iff₀ hh).2 (by linarith [hu.1])
      · exact (div_le_iff₀ hh).2 (by linarith [hu.2])
    · rw [Set.indicator_of_notMem hu]
      exact hn _
  have he : (∫ u : ℝ, ψ ((u-x)/h) ∂ν) = ‖∫ u : ℝ, (ψ ((u-x)/h) : ℂ) ∂ν‖ := by
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg (fun u ↦ hn _))]
  apply hmass.trans
  rw [he, integral_scaledMajorant_eq_fourier ψ hi hfi hinv ν x h]
  calc
    _ ≤ ∫ t : ℝ, ‖Complex.exp (((-2*Real.pi*x/h*t : ℝ) : ℂ) * Complex.I) * F t *
        fourier ν (-t/h)‖ := norm_integral_le_integral_norm _
    _ = _ := by
      congr 1
      funext t
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rfl

#print axioms closedInterval_mass_le_spectralMajorant

/-- A single actually constructed kernel controls all original finite laws,
centres and positive scales, with its Fourier support in the unit band. -/
theorem exists_closedIntervalSpectralMajorant :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Integrable ψ ∧
      Integrable (FourierTransform.fourier (fun y ↦ (ψ y : ℂ))) ∧
      (∀ u, 0 ≤ ψ u) ∧ (∀ u, |u| ≤ 1 → 1 ≤ ψ u) ∧
      (∀ ξ : ℝ, 1 ≤ |ξ| → FourierTransform.fourier (fun y ↦ (ψ y : ℂ)) ξ = 0) ∧
      ∀ (ν : Measure ℝ), IsFiniteMeasure ν → ∀ (x h : ℝ), 0 < h →
        ν.real (Set.Icc (x-h) (x+h)) ≤
          ∫ t : ℝ, ‖FourierTransform.fourier (fun y ↦ (ψ y : ℂ)) t‖ * ‖fourier ν (-t/h)‖ := by
  obtain ⟨ψ, hc, hi, hn, hm, hfi, hz, hinv⟩ := exists_generatedCoefficientInversionMajorant
  refine ⟨ψ, hc, hi, hfi, hn, hm, hz, ?_⟩
  intro ν hν x h hh
  let : IsFiniteMeasure ν := hν
  exact closedInterval_mass_le_spectralMajorant ψ hc hi hn hm hfi hinv ν x hh

#print axioms exists_closedIntervalSpectralMajorant

/-- The weighted spectral estimate yields an absolute finite-band comparison. -/
theorem exists_closedIntervalFourierBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : Measure ℝ), IsFiniteMeasure ν →
      ∀ (x h : ℝ), 0 < h → ν.real (Set.Icc (x-h) (x+h)) ≤
        C * ∫ t in Set.Icc (-1:ℝ) 1, ‖fourier ν (-t/h)‖ := by
  obtain ⟨ψ, hc, hi, hfi, hn, hm, hz, hmass⟩ := exists_closedIntervalSpectralMajorant
  let F := FourierTransform.fourier (fun y ↦ (ψ y : ℂ))
  let C : ℝ := (∫ y : ℝ, |ψ y|) + 1
  have hC : 0 < C := by
    have hnon : 0 ≤ ∫ y : ℝ, |ψ y| := integral_nonneg (fun y ↦ abs_nonneg (ψ y))
    dsimp [C]
    linarith only [hnon]
  have hFbound (t : ℝ) : ‖F t‖ ≤ C := by
    have hb : ‖F t‖ ≤ ∫ y : ℝ, |ψ y| := by
      dsimp [F]
      rw [Real.fourier_eq']
      apply (norm_integral_le_integral_norm _).trans_eq
      congr 1
      funext y
      simp only [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
    exact hb.trans (by dsimp [C]; linarith)
  refine ⟨C, hC, ?_⟩
  intro ν hν x h hh
  let : IsFiniteMeasure ν := hν
  have hFc : Continuous F := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi.ofReal
  have hνc : Continuous (fun t : ℝ ↦ ‖fourier ν (-t/h)‖) := by
    unfold fourier
    fun_prop
  have hweight : Integrable (fun t : ℝ ↦ ‖F t‖ * ‖fourier ν (-t/h)‖) := by
    apply (hfi.norm.mul_const (ν.real Set.univ)).mono'
    · exact (hFc.norm.mul hνc).aestronglyMeasurable
    · filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (norm_charFun_le _) (norm_nonneg _)
  have hind : Integrable ((Set.Icc (-1:ℝ) 1).indicator
      (fun t : ℝ ↦ C * ‖fourier ν (-t/h)‖)) :=
    (continuous_const.mul hνc).integrableOn_Icc.integrable_indicator measurableSet_Icc
  apply (hmass ν hν x h hh).trans
  change (∫ t : ℝ, ‖F t‖ * ‖fourier ν (-t/h)‖) ≤ _
  calc
    _ ≤ ∫ t : ℝ, (Set.Icc (-1:ℝ) 1).indicator (fun t ↦ C * ‖fourier ν (-t/h)‖) t := by
      apply integral_mono hweight hind
      intro t
      by_cases ht : t ∈ Set.Icc (-1:ℝ) 1
      · rw [Set.indicator_of_mem ht]
        exact mul_le_mul_of_nonneg_right (hFbound t) (norm_nonneg _)
      · have hlarge : 1 ≤ |t| := by
          apply le_of_lt
          apply lt_of_not_ge
          exact fun ht' ↦ ht (abs_le.mp ht')
        simp only [Set.indicator_of_notMem ht, F, hz t hlarge, norm_zero, zero_mul, le_refl]
    _ = _ := by rw [integral_indicator measurableSet_Icc, integral_const_mul]

#print axioms exists_closedIntervalFourierBound

/-- A finite spectral window suffices for interval flatness: the missing low
frequencies cost their length. No assumption is made beyond frequency h⁻¹. -/
theorem exists_closedIntervalFlatnessFromBand :
    ∃ D : ℝ, 0 < D ∧ ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∀ (x h a : ℝ), 0 < h → 0 < a → a ≤ 1 →
        (∀ ξ : ℝ, a/h ≤ |ξ| → |ξ| ≤ h⁻¹ → ‖fourier ν ξ‖ ≤ a) →
        ν.real (Set.Icc (x-h) (x+h)) ≤ D*a := by
  obtain ⟨C, hC, hbound⟩ := exists_closedIntervalFourierBound
  refine ⟨4*C, by positivity, ?_⟩
  intro ν hν x h a hh ha ha1 hdecay
  let : IsProbabilityMeasure ν := hν
  let low : ℝ → ℝ := (Set.Icc (-a) a).indicator (fun _ ↦ 1)
  have hνc : Continuous (fun t : ℝ ↦ ‖fourier ν (-t/h)‖) := by
    unfold fourier
    fun_prop
  have hlowi : Integrable low :=
    (continuous_const.integrableOn_Icc (a := -a) (b := a)).integrable_indicator measurableSet_Icc
  have hupperi : IntegrableOn (fun t ↦ low t + a) (Set.Icc (-1:ℝ) 1) :=
    hlowi.integrableOn.add continuous_const.integrableOn_Icc
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
      ‖fourier ν (-t/h)‖ ≤ low t + a := by
    by_cases hsmall : |t| ≤ a
    · have hl : low t = 1 := by
        exact Set.indicator_of_mem (show t ∈ Set.Icc (-a) a from abs_le.mp hsmall) _
      rw [hl]
      exact (norm_fourier_le_one ν _).trans (by linarith)
    · have hl : low t = 0 := by
        exact Set.indicator_of_notMem
          (show t ∉ Set.Icc (-a) a from fun ht' ↦ hsmall (abs_le.mpr ht')) _
      rw [hl, zero_add]
      apply hdecay
      · rw [abs_div, abs_neg, abs_of_pos hh]
        exact div_le_div_of_nonneg_right (le_of_lt (lt_of_not_ge hsmall)) hh.le
      · rw [abs_div, abs_neg, abs_of_pos hh, ← one_div]
        exact div_le_div_of_nonneg_right (abs_le.mpr ht) hh.le
  have hsub : Set.Icc (-a) a ⊆ Set.Icc (-1:ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hlow : (∫ t in Set.Icc (-1:ℝ) 1, low t) = 2*a := by
    dsimp [low]
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply measurableSet_Icc,
      Set.inter_eq_left.mpr hsub, Real.volume_real_Icc_of_le (by linarith)]
    ring
  have hconstant : (∫ _t in Set.Icc (-1:ℝ) 1, a) = 2*a := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num)]
    simp only [smul_eq_mul]
    ring
  have hint : (∫ t in Set.Icc (-1:ℝ) 1, ‖fourier ν (-t/h)‖) ≤ 4*a := by
    calc
      _ ≤ ∫ t in Set.Icc (-1:ℝ) 1, (low t + a) :=
        setIntegral_mono_on hνc.integrableOn_Icc hupperi measurableSet_Icc hpoint
      _ = 4*a := by rw [integral_add hlowi.integrableOn continuous_const.integrableOn_Icc, hlow, hconstant]; ring
  calc
    _ ≤ C * ∫ t in Set.Icc (-1:ℝ) 1, ‖fourier ν (-t/h)‖ := hbound ν inferInstance x h hh
    _ ≤ C*(4*a) := mul_le_mul_of_nonneg_left hint hC.le
    _ = (4*C)*a := by ring

#print axioms exists_closedIntervalFlatnessFromBand

/-- The finite-band estimate acts on the actual independent sum-of-products law.
The power payment is explicit and the constant precedes every parameter. -/
theorem exists_generatedProductSumLaw_intervalBound :
    ∃ D : ℝ, 0 < D ∧ ∀ (n : ℕ) (μ : Fin n → Measure ℝ),
      (∀ j, IsProbabilityMeasure (μ j)) → ∀ (k : ℕ) (x h a b : ℝ),
        0 < h → 0 < a → a ≤ 1 → b^k ≤ a →
        (∀ ξ : ℝ, a/h ≤ |ξ| → |ξ| ≤ h⁻¹ → ‖fourier (productLaw μ) ξ‖ ≤ b) →
        (generatedProductSumLaw μ k).real (Set.Icc (x-h) (x+h)) ≤ D*a := by
  obtain ⟨D, hD, hbound⟩ := exists_closedIntervalFlatnessFromBand
  refine ⟨D, hD, ?_⟩
  intro n μ hμ k x h a b hh ha ha1 hpay hband
  let : ∀ j, IsProbabilityMeasure (μ j) := hμ
  apply hbound (generatedProductSumLaw μ k) inferInstance x h a hh ha ha1
  intro ξ hξ hξ'
  rw [norm_fourier_generatedProductSumLaw]
  exact (pow_le_pow_left₀ (norm_nonneg _) (hband ξ hξ hξ') k).trans hpay

#print axioms exists_generatedProductSumLaw_intervalBound
end Kakeya4.Hard.MultiplicativeConvolution
