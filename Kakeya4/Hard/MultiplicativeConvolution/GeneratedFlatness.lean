





import Kakeya4.Hard.MultiplicativeConvolution.GeneratedSpectral
import Kakeya4.Hard.MultiplicativeConvolution.Complete

/-! Actual OSS consumer for re:flat-coefficients: original smooth-energy inputs
on a finite scale window produce a flat sum-of-products law. The ratio-law
interval cap must still produce these energy inputs. -/

set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

theorem generatedProductSumLaw_flatness_of_uniformEnergy (kernel : SmoothKernel)
    (n : ℕ) (hn : 2 ≤ n) (s : Fin n → ℝ)
    (hs : ∀ j, 0 < s j ∧ s j ≤ 1) (hsum : 1 < ∑ j, s j)
    {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    ∃ (k : ℕ) (h₀ ε D : ℝ), 0 < k ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < D ∧
      ∀ (μ : Fin n → Measure ℝ), (∀ j, IsProbabilityMeasure (μ j)) →
        (∀ j, UnitSupported (μ j)) → ∀ h : ℝ, 0 < h → h ≤ h₀ →
          (∀ r : ℝ, h ≤ r → r ≤ h^e → ∀ j,
            smoothEnergy kernel.law (s j) r (μ j) ≤ ENNReal.ofReal (r ^ (-ε))) →
          ∀ x : ℝ, (generatedProductSumLaw μ k).real (Set.Icc (x-h) (x+h)) ≤ D*h^(1-e) := by
  obtain ⟨r₀, ε, τ, hr₀, hr₀1, hε, hε1, hτ, hτ1, hdecay⟩ :=
    finiteScaleDecay_proof kernel n hn s hs hsum
  obtain ⟨D, hD, hinterval⟩ := exists_generatedProductSumLaw_intervalBound
  let k : ℕ := ⌈1/(e*τ)⌉₊ + 1
  have hk : 1 ≤ (e*τ)*(k:ℝ) := by
    have hceil : 1/(e*τ) ≤ (k:ℝ) := by
      have hc := Nat.le_ceil (1/(e*τ))
      dsimp [k]
      push_cast
      linarith only [hc]
    have hh := (div_le_iff₀ (mul_pos he hτ)).mp hceil
    nlinarith only [hh]
  let h₀ : ℝ := min 1 (r₀^(1/e))
  have hh₀ : 0 < h₀ := lt_min zero_lt_one (Real.rpow_pos_of_pos hr₀ _)
  refine ⟨k, h₀, ε, D, by dsimp [k]; omega, hh₀, min_le_left _ _, hε, hε1, hD, ?_⟩
  intro μ hμ hsupp h hh hhh henergy x
  let : ∀ j, IsProbabilityMeasure (μ j) := hμ
  have hh1 : h ≤ 1 := hhh.trans (min_le_left _ _)
  have hpow : h^e ≤ r₀ := by
    have hb := Real.rpow_le_rpow hh.le (hhh.trans (min_le_right _ _)) he.le
    have hroot : (r₀^(1/e))^e = r₀ := by
      rw [← Real.rpow_mul hr₀.le, one_div_mul_cancel he.ne', Real.rpow_one]
    exact hb.trans_eq hroot
  have hscale : h^(1-e)/h = h^(-e) := by
    calc
      _ = h^(1-e)/h^1 := by rw [Real.rpow_one]
      _ = h^((1-e)-1) := (Real.rpow_sub hh _ _).symm
      _ = h^(-e) := by congr 1; ring
  apply hinterval n μ hμ k x h (h^(1-e)) (h^(e*τ)) hh
    (Real.rpow_pos_of_pos hh _) (Real.rpow_le_one hh.le hh1 (by linarith))
  · rw [← Real.rpow_mul_natCast hh.le]
    exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith only [hk, he])
  · intro ξ hξ hξ'
    rw [hscale] at hξ
    have hξpos : 0 < |ξ| := (Real.rpow_pos_of_pos hh (-e)).trans_le hξ
    have hrlo : h ≤ |ξ|⁻¹ := by
      have hi := (inv_le_inv₀ (inv_pos.mpr hh) hξpos).mpr hξ'
      simpa only [inv_inv] using hi
    have hrhi : |ξ|⁻¹ ≤ h^e := by
      have hi := (inv_le_inv₀ hξpos (Real.rpow_pos_of_pos hh (-e))).mpr hξ
      simpa only [Real.rpow_neg hh.le, inv_inv] using hi
    have hd := hdecay μ hμ hsupp (|ξ|⁻¹) (inv_pos.mpr hξpos) (hrhi.trans hpow)
      (henergy _ hrlo hrhi) ξ (by simp) (by simp only [inv_inv]; linarith only [hξpos])
    apply hd.trans
    have hb := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hh (-e)) hξ (by linarith only [hτ] : -τ ≤ 0)
    have heq : (h^(-e))^(-τ) = h^(e*τ) := by
      rw [← Real.rpow_mul hh.le]
      congr 1
      ring
    exact hb.trans_eq heq

#print axioms generatedProductSumLaw_flatness_of_uniformEnergy
end Kakeya4.Hard.MultiplicativeConvolution
