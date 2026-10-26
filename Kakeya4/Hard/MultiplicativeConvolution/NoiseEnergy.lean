import Kakeya4.Hard.MultiplicativeConvolution.CappedEnergy
import Kakeya4.Hard.MultiplicativeConvolution.FixedKernel

/-!
# True noise-law representation of smoothed Riesz energy

The same independent additive noise used in smoothLaw is integrated here; no
comparison certificate or substitute smoothing operator is introduced.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- A normalized smooth profile has a unit-supported actual kernel law. -/
theorem SmoothKernel.law_unitSupported (κ : SmoothKernel) : UnitSupported κ.law := by
  unfold UnitSupported SmoothKernel.law
  rw [ae_withDensity_iff (κ.smooth.continuous.measurable.ennreal_ofReal)]
  filter_upwards [] with x hx
  by_contra h
  have hzero := κ.outside x (lt_of_not_ge h)
  exact hx (by simp [hzero])

/-- The actual average Riesz kernel after the two independent additive noises. -/
def noiseKernel (κ : Measure ℝ) (s r x y : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ∫⁻ v, rieszKernel s (x + r * u) (y + r * v) ∂κ ∂κ

/-- Smoothed energy is precisely the integral over the original pair and the noises. -/
theorem smoothEnergy_eq_noiseKernel (κ : Measure ℝ) [SFinite κ]
    (μ : Measure ℝ) [SFinite μ] (s r : ℝ) :
    smoothEnergy κ s r μ = ∫⁻ x, ∫⁻ y, noiseKernel κ s r x y ∂μ ∂μ := by
  have hm : Measurable (fun p : ℝ × ℝ ↦ rieszKernel s p.1 p.2) := measurable_rieszKernel s
  have hi : Measurable (fun x ↦ ∫⁻ y, rieszKernel s x y ∂smoothLaw κ r μ) :=
    hm.lintegral_prod_right'
  rw [smoothEnergy, rieszEnergy]
  change (∫⁻ x, ∫⁻ y, rieszKernel s x y ∂smoothLaw κ r μ
    ∂μ ∗ κ.map (fun x ↦ r * x)) = _
  rw [Measure.lintegral_conv hi]
  apply lintegral_congr
  intro x
  have hix : Measurable (fun z : ℝ ↦ ∫⁻ y, rieszKernel s (x+z) y ∂smoothLaw κ r μ) :=
    hi.comp (measurable_const.add measurable_id)
  rw [lintegral_map hix (by fun_prop)]
  have he (u : ℝ) :
      (∫⁻ y, rieszKernel s (x + r * u) y ∂smoothLaw κ r μ) =
        ∫⁻ y, ∫⁻ v, rieszKernel s (x + r * u) (y + r * v) ∂κ ∂μ := by
    have hku : Measurable (fun y : ℝ ↦ rieszKernel s (x+r*u) y) :=
      hm.comp (measurable_const.prodMk measurable_id)
    rw [smoothLaw, Measure.lintegral_conv hku]
    apply lintegral_congr
    intro y
    have hkuy : Measurable (fun z : ℝ ↦ rieszKernel s (x+r*u) (y+z)) :=
      hm.comp (measurable_const.prodMk (by fun_prop))
    exact lintegral_map hkuy (by fun_prop)
  simp_rw [he]
  exact lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    unfold Function.uncurry rieszKernel
    fun_prop)

/-- Unit noise moves a pair distance by at most twice its physical scale. -/
theorem noisy_pair_distance_le {r u v : ℝ} (hr : 0 ≤ r) (hu : |u| ≤ 1)
    (hv : |v| ≤ 1) (x y : ℝ) :
    |(x + r * u) - (y + r * v)| ≤ 3 * max r |x-y| := by
  have huv : |u-v| ≤ 2 := by
    have h := abs_sub_le u 0 v
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith
  calc
    |(x + r*u) - (y + r*v)| = |(x-y) + r*(u-v)| := by congr 1; ring
    _ ≤ |x-y| + |r*(u-v)| := abs_add_le _ _
    _ ≤ |x-y| + r*2 := by rw [abs_mul, abs_of_nonneg hr]; gcongr
    _ ≤ _ := by nlinarith [le_max_left r |x-y|, le_max_right r |x-y|]

/-- A pointwise quantitative lower comparison with the actual noisy kernel. -/
theorem noisy_rieszKernel_ge_capped {s r u v : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (x y : ℝ) :
    ENNReal.ofReal 3 ^ (-s) * cappedKernel s r x y ≤
      rieszKernel s (x + r*u) (y + r*v) := by
  have h := ennreal_neg_rpow_antitone hs
    (ENNReal.ofReal_le_ofReal (noisy_pair_distance_le hr hu hv x y))
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top] at h
  exact h

/-- Averaging the genuine independent noise preserves the lower comparison. -/
theorem noiseKernel_ge_capped (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : UnitSupported κ) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (x y : ℝ) :
    ENNReal.ofReal 3 ^ (-s) * cappedKernel s r x y ≤ noiseKernel κ s r x y := by
  calc
    _ = ∫⁻ _ : ℝ, ∫⁻ _ : ℝ, ENNReal.ofReal 3 ^ (-s) * cappedKernel s r x y ∂κ ∂κ := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hκ] with u hu
      apply lintegral_mono_ae
      filter_upwards [hκ] with v hv
      exact noisy_rieszKernel_ge_capped hs hr hu hv x y

/-- The actual smoothed Riesz energy controls capped energy of the original law. -/
theorem smoothEnergy_ge_capped (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : UnitSupported κ) (μ : Measure ℝ) [SFinite μ] {s r : ℝ}
    (hs : 0 ≤ s) (hr : 0 ≤ r) :
    ENNReal.ofReal 3 ^ (-s) * cappedEnergy s r μ ≤ smoothEnergy κ s r μ := by
  have hc : ENNReal.ofReal 3 ^ (-s) ≠ ⊤ := by
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 3)]
    exact ENNReal.ofReal_ne_top
  rw [smoothEnergy_eq_noiseKernel]
  calc
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal 3 ^ (-s) * cappedKernel s r x y ∂μ ∂μ := by
      simp_rw [lintegral_const_mul' _ _ hc]
      rfl
    _ ≤ _ := lintegral_mono (fun x ↦ lintegral_mono (fun y ↦ noiseKernel_ge_capped κ hκ hs hr x y))

end Kakeya4.Hard.MultiplicativeConvolution
