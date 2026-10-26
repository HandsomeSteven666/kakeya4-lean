import Kakeya4.Hard.MultiplicativeConvolution.TwoFactorQuantitative
import Kakeya4.Hard.MultiplicativeConvolution.SmallScalePowers

/-!
# Genuine two-factor finite-scale Fourier decay

The original smoothing energy caps imply positive-power decay throughout the
whole frequency band, for every unit-supported Borel probability law, including
laws supported through zero. All constants precede the laws.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The two-factor optimal-energy base case, with the original law quantifiers. -/
theorem exists_twoFactor_decay (κ : SmoothKernel) {s t : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    ∃ r₀ ε τ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < τ ∧ τ ≤ 1 ∧
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        UnitSupported μ → UnitSupported ν →
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
          smoothEnergy κ.law t r ν ≤ ENNReal.ofReal (r^(-ε)) →
          ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2*r⁻¹ →
            ‖fourier (μ ∗ₘ ν) ξ‖ ≤ |ξ|^(-τ) := by
  let d := s+t-1
  let ε := d/8
  let τ := d/8
  let a := d/4
  have hd : 0 < d := by dsimp [d]; linarith
  have hd1 : d ≤ 1 := by dsimp [d]; linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hτ : 0 < τ := hε
  have hε1 : ε ≤ 1 := by dsimp [ε]; linarith
  have hτ1 : τ ≤ 1 := hε1
  have hgap : τ < a := by dsimp [τ,a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hcent : 0 ≤ twoFactorCentralConstant s t := Real.sqrt_nonneg _
  have htail : 0 ≤ twoFactorTailConstant :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le gaussianTailMoment_nonneg) (by norm_num)
  obtain ⟨r₀,hr₀,hr₀1,hsmall⟩ :=
    exists_small_scale_power_bound (add_nonneg hcent htail) hgap
  refine ⟨r₀,ε,τ,hr₀,hr₀1,hε,hε1,hτ,hτ1,?_⟩
  intro μ ν _ _ hμ hν r hr hrr heμ heν ξ hξlo hξhi
  have hr1 : r ≤ 1 := hrr.trans hr₀1
  have hξpos : 0 < |ξ| := (inv_pos.mpr hr).trans_le hξlo
  have hξr : 1 ≤ |ξ| * r := by
    have h := mul_le_mul_of_nonneg_right hξlo hr.le
    simpa only [inv_mul_cancel₀ hr.ne'] using h
  have hξhi' : |ξ| ≤ 2/r := by simpa only [div_eq_mul_inv] using hξhi
  have hbase := norm_fourier_mconv_le_energy_powers κ hs.le hs1 ht.le ht1 hr hξr hξhi' μ ν hμ hν heμ heν
  have hpow : r^((s+t-1-2*ε)/2) ≤ r^a := by
    apply Real.rpow_le_rpow_of_exponent_ge hr hr1
    dsimp [a,ε,d]
    linarith
  have htailr : twoFactorTailConstant/|ξ| ≤ twoFactorTailConstant*r^a := by
    have hdiv : 1/|ξ| ≤ r := (div_le_iff₀ hξpos).mpr (by nlinarith [hξr])
    have hrpow : r ≤ r^a := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hr1 ha1
    have h := mul_le_mul_of_nonneg_left (hdiv.trans hrpow) htail
    simpa only [mul_one_div] using h
  have hfreq : (2:ℝ)^(-τ)*r^τ ≤ |ξ|^(-τ) := by
    have hpos := Real.rpow_pos_of_pos hξpos τ
    have hmono : |ξ|^τ ≤ (2/r)^τ := Real.rpow_le_rpow hξpos.le hξhi' hτ.le
    rw [Real.rpow_neg hξpos.le]
    rw [← one_div]
    apply (le_div_iff₀ hpos).mpr
    have he : (2:ℝ)^(-τ)*r^τ * (2/r)^τ = 1 := by
      rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le τ,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    exact (mul_le_mul_of_nonneg_left hmono (by positivity)).trans_eq he
  calc
    _ ≤ twoFactorCentralConstant s t * r^((s+t-1-2*ε)/2) + twoFactorTailConstant/|ξ| := hbase
    _ ≤ (twoFactorCentralConstant s t + twoFactorTailConstant)*r^a := by
      nlinarith [mul_le_mul_of_nonneg_left hpow hcent]
    _ ≤ (2:ℝ)^(-τ)*r^τ := hsmall r hr hrr
    _ ≤ _ := hfreq

end Kakeya4.Hard.MultiplicativeConvolution
