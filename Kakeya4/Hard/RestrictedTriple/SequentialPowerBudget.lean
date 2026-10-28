import Kakeya4.Hard.RestrictedTriple.SequentialTwoEnds

set_option autoImplicit false
noncomputable section

namespace Kakeya4.Hard.RestrictedTriple

theorem width_rpow_lower {p w ζ : ℝ} (hp : 0 < p) (hw : p/2 ≤ w)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) : p^ζ/2 ≤ w^ζ := by
  have hwp : 0 < w := lt_of_lt_of_le (by positivity : 0 < p/2) hw
  have htwo : (2:ℝ)^ζ ≤ 2 := by
    calc
      _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hζ1
      _ = _ := Real.rpow_one _
  have hh : p^ζ ≤ (2*w)^ζ := Real.rpow_le_rpow hp.le (by linarith) hζ
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hwp.le] at hh
  have hmul := mul_le_mul_of_nonneg_right htwo (Real.rpow_pos_of_pos hwp ζ).le
  linarith

theorem square_rpow_forty_four {p η : ℝ} (hp : 0 < p) : (p^(44*η))^2 = p^(88*η) := by
  rw [← Real.rpow_natCast (p^(44*η)) 2,← Real.rpow_mul hp.le]
  congr 1
  norm_num
  ring

theorem sequential_denominator_lower {p η ζ w₁ w₂ : ℝ} (hp : 0 < p)
    (hw₁ : p/2 ≤ w₁) (hw₂ : p/2 ≤ w₂) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    p^(88*η+2*ζ)/4 ≤ (p^(44*η))^2*w₁^ζ*w₂^ζ := by
  have h1 := width_rpow_lower hp hw₁ hζ hζ1
  have h2 := width_rpow_lower hp hw₂ hζ hζ1
  have hw₁p : 0 < w₁ := lt_of_lt_of_le (by positivity : 0 < p/2) hw₁
  have hw₂p : 0 < w₂ := lt_of_lt_of_le (by positivity : 0 < p/2) hw₂
  have heq : (p^(44*η))^2*(p^ζ/2)*(p^ζ/2) = p^(88*η+2*ζ)/4 := by
    calc
      _ = (p^(88*η)*(p^ζ*p^ζ))/4 := by rw [square_rpow_forty_four hp]; ring
      _ = p^(88*η+(ζ+ζ))/4 := by rw [← Real.rpow_add hp,← Real.rpow_add hp]
      _ = _ := by congr 2; ring
  rw [← heq]
  gcongr

theorem sequential_mass_power_payment {p η ζ w₁ w₂ : ℝ} (hp : 0 < p)
    (hpay : 256 ≤ p^(-η)) (hw₁ : p/2 ≤ w₁) (hw₂ : p/2 ≤ w₂) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    p^(89*η+2*ζ) ≤ (p^(44*η))^2*w₁^ζ*w₂^ζ/64 := by
  have hden := sequential_denominator_lower (η := η) hp hw₁ hw₂ hζ hζ1
  have hpaid : 256*p^(89*η+2*ζ) ≤ p^(88*η+2*ζ) := by
    calc
      _ ≤ p^(-η)*p^(89*η+2*ζ) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
      _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring
  linarith

theorem sequential_density_power_payment {p η : ℝ} (hp : 0 < p) (hpay : 256 ≤ p^(-η)) :
    p^(45*η) ≤ p^(44*η)/256 := by
  have hpaid : 256*p^(45*η) ≤ p^(44*η) := by
    calc
      _ ≤ p^(-η)*p^(45*η) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
      _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring
  linarith

theorem sequential_Frostman_power_payment {p η ζ w₁ w₂ : ℝ} (hp : 0 < p)
    (hpay : 256 ≤ p^(-η)) (hw₁ : p/2 ≤ w₁) (hw₂ : p/2 ≤ w₂) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    64*p^(-44*η)/((p^(44*η))^2*w₁^ζ*w₂^ζ) ≤ p^(-133*η-2*ζ) := by
  have hden := sequential_denominator_lower (η := η) hp hw₁ hw₂ hζ hζ1
  calc
    _ ≤ 64*p^(-44*η)/(p^(88*η+2*ζ)/4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 256*p^(-132*η-2*ζ) := by
      calc
        _ = 256*(p^(-44*η)/p^(88*η+2*ζ)) := by ring
        _ = 256*p^((-44*η)-(88*η+2*ζ)) := by rw [← Real.rpow_sub hp]
        _ = _ := by
          rw [show (-44*η)-(88*η+2*ζ) = -132*η-2*ζ by ring]
    _ ≤ p^(-η)*p^(-132*η-2*ζ) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
    _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring

theorem sequential_strip_power_payment {p η : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hη : 0 ≤ η)
    (hpay : 256 ≤ p^(-η)) : 128/(p^(44*η))^2 ≤ p^(-89*η) ∧ 64/p^(44*η) ≤ p^(-89*η) := by
  have hpay128 : 128 ≤ p^(-η) := by linarith
  have hpay64 : 64 ≤ p^(-η) := by linarith
  have hneg (a : ℝ) : p^(-a*η) = (p^(a*η))⁻¹ := by
    rw [show -a*η = -(a*η) by ring,Real.rpow_neg hp.le]
  constructor
  · calc
      _ = 128*p^(-88*η) := by rw [square_rpow_forty_four hp,hneg 88]; ring
      _ ≤ p^(-η)*p^(-88*η) := mul_le_mul_of_nonneg_right hpay128 (Real.rpow_pos_of_pos hp _).le
      _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring
  · calc
      _ = 64*p^(-44*η) := by rw [hneg 44]; ring
      _ ≤ p^(-η)*p^(-44*η) := mul_le_mul_of_nonneg_right hpay64 (Real.rpow_pos_of_pos hp _).le
      _ = p^(-45*η) := by rw [← Real.rpow_add hp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by linarith)

end Kakeya4.Hard.RestrictedTriple
