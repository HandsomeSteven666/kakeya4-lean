import Kakeya4.Hard.RestrictedTriple.VariableExpansion

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem endpoint_factor_upper {p η a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haup : a ≤ 3/(4*p^(6*η))) (hbup : b ≤ 3/(4*p^(6*η))) :
    a*b ≤ p^(-12*η) := by
  have hr : 0 < p^(6*η) := Real.rpow_pos_of_pos hp _
  have hpow : (p^(6*η))^2 = p^(12*η) := by
    rw [← Real.rpow_natCast (p^(6*η)) 2,← Real.rpow_mul hp.le]
    congr 1
    norm_num
    ring
  calc
    _ ≤ (3/(4*p^(6*η)))*(3/(4*p^(6*η))) := by gcongr
    _ = (9/16)/(p^(6*η))^2 := by ring
    _ ≤ 1/(p^(6*η))^2 := (div_le_div_iff_of_pos_right (sq_pos_of_pos hr)).mpr (by norm_num)
    _ = _ := by
      have he : -12*η = -(12*η) := by ring
      rw [hpow,he,Real.rpow_neg hp.le,one_div]

theorem longIntervalExpansion_of_local_transport {H Q : Set Triple} {p ε ε₀ η θ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hη : 0 ≤ η) (hε : ε ≤ 1) (hεgap : ε₀ < ε)
    (hθ : θ < η*(ε-ε₀)) (hpay : 16*13^(1-ε) ≤ p^(-θ))
    (hlocal : ∀ s a b : ℝ, p ≤ s →
      intervalCover s (Icc a b ∩ dotDifferenceImage Q) ≤
        16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H))
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
  have hbound : ENNReal.ofReal (16*((b+6*p-(a-6*p))/s)^(1-ε)) ≤
      16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H) :=
    (ENNReal.ofReal_le_ofReal hbudget).trans (hlower.trans (hlocal s a b hs))
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16)] at hbound
  norm_num only [ENNReal.ofReal_ofNat] at hbound
  refine ⟨s,a-6*p,b+6*p,hs,by linarith,by linarith,?_⟩
  exact (ENNReal.mul_le_mul_iff_right (a := (16:ℝ≥0∞)) (by norm_num) (by norm_num)).mp hbound

/-- Complete expansion-branch adapter for the actual standard normalization and original H.
All payments are produced before p, sigma and the three arbitrary triple sets are chosen. -/
theorem exists_uniform_normalized_expansion_transport {η ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∀ σ : ℝ, 0 < σ → σ ≤ p^(-12*η) → ∀ H Q P : Set Triple,
        dotDifferenceImage P = (fun x : ℝ ↦ σ*x) '' dotDifferenceImage Q →
        (∀ s a b : ℝ, p ≤ s → intervalCover s (Icc a b ∩ dotDifferenceImage Q) ≤
          16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H)) →
        LongIntervalExpansion (p/8) (ε/4) (44*η) P → LongIntervalExpansion p ε η H := by
  obtain ⟨p₁,hp₁,hp₁1,hpay₁⟩ := exists_constant_power_payment 9 (by norm_num) hη
  have hθ : 0 < η*ε/4 := by positivity
  obtain ⟨p₂,hp₂,_hp₂1,hpay₂⟩ := exists_constant_power_payment
    (16*13^(1-ε)) (by positivity) hθ
  refine ⟨min p₁ p₂,lt_min hp₁ hp₂,(min_le_left _ _).trans_lt hp₁1,?_⟩
  intro p hp hpp σ hσ hσup H Q P himage hlocal hexpand
  have hpp₁ := hpp.trans (min_le_left p₁ p₂)
  have hpp₂ := hpp.trans (min_le_right p₁ p₂)
  have hp1 : p < 1 := hpp₁.trans_lt hp₁1
  have hraw : LongIntervalExpansion p (ε/2) η Q :=
    longIntervalExpansion_of_variable_factor hp hp1.le hη.le hσ hσup (hpay₁ p hp hpp₁)
      (by linarith) (by linarith) (by linarith) himage hexpand
  exact longIntervalExpansion_of_local_transport hp hp1 hη.le hε1 (by linarith)
    (by nlinarith : η*ε/4 < η*(ε-ε/2)) (hpay₂ p hp hpp₂) hlocal hraw

end Kakeya4.Hard.RestrictedTriple
