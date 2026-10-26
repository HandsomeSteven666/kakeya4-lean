import Kakeya4.Hard.RestrictedTriple.DiscreteInput
import Kakeya4.Hard.RestrictedTriple.Exclusion

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- A finite model's actual local expansion transports to the original image.
The exponent slack pays both the factor 16 and the interval enlargement by 13.
This transports a supplied expansion branch; it does not prove the dichotomy. -/
theorem longIntervalExpansion_of_approximation {H Q : Set Triple} {p ε ε₀ η θ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hη : 0 ≤ η) (hε : ε ≤ 1) (hεgap : ε₀ < ε)
    (hθ : θ < η*(ε-ε₀)) (hpay : 16*13^(1-ε) ≤ p^(-θ))
    (happrox : ∀ y ∈ dotDifferenceImage Q, ∃ x ∈ dotDifferenceImage H, |y-x| ≤ 6*p)
    (hexpand : LongIntervalExpansion p ε₀ η Q) : LongIntervalExpansion p ε η H := by
  obtain ⟨s,a,b,hs,hab,hwidth,hlower⟩ := hexpand
  have hspos : 0 < s := hp.trans_le hs
  have hR : p^(-η) ≤ (b-a)/s := (le_div_iff₀ hspos).mpr hwidth
  have hone : 1 ≤ (b-a)/s :=
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp hp1.le (by linarith)).trans hR
  have hL : s ≤ b-a := by have hh := (le_div_iff₀ hspos).mp hone; simpa using hh
  have hRpos : 0 < (b-a)/s := lt_of_lt_of_le zero_lt_one hone
  have hnum : b+6*p-(a-6*p) ≤ 13*(b-a) := by linarith
  have hratio : (b+6*p-(a-6*p))/s ≤ 13*((b-a)/s) := by
    calc
      _ ≤ (13*(b-a))/s := (div_le_div_iff_of_pos_right hspos).mpr hnum
      _ = _ := by ring
  have hnewpos : 0 ≤ (b+6*p-(a-6*p))/s := div_nonneg (by linarith) hspos.le
  have hrpow : ((b+6*p-(a-6*p))/s)^(1-ε) ≤ 13^(1-ε)*((b-a)/s)^(1-ε) := by
    have hh := Real.rpow_le_rpow hnewpos hratio (by linarith : 0 ≤ 1-ε)
    rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 13) hRpos.le] at hh
  have hstrict : (16*13^(1-ε))*((b-a)/s)^(1-ε) < ((b-a)/s)^(1-ε₀) := by
    apply dimension_gap hp hp1 (by linarith) _ hpay hR
    convert hθ using 1 <;> ring
  have hbudget : 16*((b+6*p-(a-6*p))/s)^(1-ε) ≤ ((b-a)/s)^(1-ε₀) := by
    calc
      _ ≤ 16*(13^(1-ε)*((b-a)/s)^(1-ε)) := mul_le_mul_of_nonneg_left hrpow (by norm_num)
      _ = (16*13^(1-ε))*((b-a)/s)^(1-ε) := by ring
      _ ≤ _ := hstrict.le
  have hlocal := intervalCover_local_le_sixteen_mul_of_approximation hspos.le
    (show 0 ≤ 6*p by positivity) (show 6*p ≤ 6*s by linarith) happrox (a := a) (b := b)
  have hbound : ENNReal.ofReal (16*((b+6*p-(a-6*p))/s)^(1-ε)) ≤
      16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H) :=
    (ENNReal.ofReal_le_ofReal hbudget).trans (hlower.trans hlocal)
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16)] at hbound
  norm_num only [ENNReal.ofReal_ofNat] at hbound
  refine ⟨s,a-6*p,b+6*p,hs,by linarith,by linarith,?_⟩
  exact (ENNReal.mul_le_mul_iff_right (a := (16:ℝ≥0∞)) (by norm_num) (by norm_num)).mp hbound

/-- Uniform small-scale transport: no caller-supplied payment certificate.
The threshold depends only on the exponents and precedes p and both actual triple sets. -/
theorem exists_uniform_expansion_transport {η ε ε₀ : ℝ}
    (hη : 0 < η) (hε : ε ≤ 1) (hgap : ε₀ < ε) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∀ H Q : Set Triple,
        (∀ y ∈ dotDifferenceImage Q, ∃ x ∈ dotDifferenceImage H, |y-x| ≤ 6*p) →
        LongIntervalExpansion p ε₀ η Q → LongIntervalExpansion p ε η H := by
  have hθ : 0 < η*(ε-ε₀)/2 := by positivity
  obtain ⟨p₀, hp₀, hp₀1, hpay⟩ := exists_constant_power_payment
    (16*13^(1-ε)) (by positivity) hθ
  refine ⟨p₀, hp₀, hp₀1, ?_⟩
  intro p hp hpp H Q happ hexpand
  apply longIntervalExpansion_of_approximation hp (hpp.trans_lt hp₀1) hη.le hε hgap
    (show η*(ε-ε₀)/2 < η*(ε-ε₀) by linarith) (hpay p hp hpp) happ hexpand

end Kakeya4.Hard.RestrictedTriple
