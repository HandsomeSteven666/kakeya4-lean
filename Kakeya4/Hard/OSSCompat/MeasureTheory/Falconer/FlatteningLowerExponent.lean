






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningSeparatedEnergy

/-! Lower the two original energy exponents with a uniform coefficient before finite gridding. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem unit_noisy_pair_distance_le_four {δ x y w z : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hw : |w| ≤ 1) (hz : |z| ≤ 1) : |(x+δ*w)-(y+δ*z)| ≤ 4 := by
  have hdx : δ*|w| ≤ 1 := (mul_le_mul_of_nonneg_left hw hδ).trans (by simpa using hδ1)
  have hdy : δ*|z| ≤ 1 := (mul_le_mul_of_nonneg_left hz hδ).trans (by simpa using hδ1)
  have hax := abs_add_le x (δ*w)
  have hay := abs_add_le y (δ*z)
  rw [abs_mul,abs_of_nonneg hδ] at hax hay
  have hh := abs_sub_le (x+δ*w) 0 (y+δ*z)
  simp only [sub_zero,zero_sub,abs_neg] at hh
  linarith

theorem smoothEnergy_lower_exponent_le_four (kernel : SmoothKernel) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : UnitSupported μ) {δ u s : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hu : 0 < u) (hus : u ≤ s) (hs1 : s ≤ 1) :
    smoothEnergy kernel.law u δ μ ≤ 4*smoothEnergy kernel.law s δ μ := by
  rcases eq_or_lt_of_le hus with heq | hlt
  · subst s
    exact le_mul_of_one_le_left bot_le (by norm_num : (1:ℝ≥0∞) ≤ 4)
  have hcoef : ENNReal.ofReal ((4:ℝ)^(s-u)) ≤ (4:ℝ≥0∞) := by
    apply ENNReal.ofReal_le_of_le_toReal
    norm_num
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) (by linarith : s-u ≤ 1)
  rw [smoothEnergy_eq_noiseKernel,smoothEnergy_eq_noiseKernel]
  unfold noiseKernel
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ∫⁻ w, ∫⁻ z, (4:ℝ≥0∞)*rieszKernel s (x+δ*w) (y+δ*z)
        ∂kernel.law ∂kernel.law ∂μ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hμ] with x hx
      apply lintegral_mono_ae
      filter_upwards [hμ] with y hy
      apply lintegral_mono_ae
      filter_upwards [kernel.law_unitSupported] with w hw
      apply lintegral_mono_ae
      filter_upwards [kernel.law_unitSupported] with z hz
      have hdist := unit_noisy_pair_distance_le_four hδ hδ1 hx hy hw hz
      exact (OAI.PlanarFalconer.bounded_riesz_kernel (abs_nonneg _) (by norm_num)
        hdist hu hlt).trans (mul_le_mul_left hcoef _)
    _ = _ := by simp_rw [lintegral_const_mul' _ _ (by norm_num : (4:ℝ≥0∞)≠⊤)]

theorem exists_uniform_lower_exponent_cap (kernel : SmoothKernel) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], UnitSupported μ →
      ∀ u s : ℝ, 0 < u → u ≤ s → s ≤ 1 →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-(ε/2))) →
      smoothEnergy kernel.law u δ μ ≤ ENNReal.ofReal (δ^(-ε)) := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hsmall⟩ := exists_small_scale_power_bound
    (C := 4) (a := ε/2) (τ := 0) (by norm_num) (by positivity)
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro δ hδ hδsmall μ _ hμ u s hu hus hs1 hcap
  have hs : (4:ℝ)*δ^(ε/2) ≤ 1 := by
    simpa only [neg_zero,Real.rpow_zero,mul_one] using hsmall δ hδ hδsmall
  have hpay : 4*δ^(-(ε/2)) ≤ δ^(-ε) := by
    calc
      _ = (4*δ^(ε/2))*δ^(-ε) := by rw [mul_assoc,← Real.rpow_add hδ]; congr 2; ring
      _ ≤ 1*δ^(-ε) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := one_mul _
  exact (smoothEnergy_lower_exponent_le_four kernel μ hμ hδ.le (hδsmall.trans hδ₀1) hu hus hs1).trans
    ((mul_le_mul_right hcap 4).trans (by
      have hp := ENNReal.ofReal_le_ofReal hpay
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),ENNReal.ofReal_ofNat] using hp))

#print axioms unit_noisy_pair_distance_le_four
#print axioms smoothEnergy_lower_exponent_le_four
#print axioms exists_uniform_lower_exponent_cap
end OAI.Falconer
