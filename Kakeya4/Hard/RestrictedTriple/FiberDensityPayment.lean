import Kakeya4.Hard.RestrictedTriple.TripartiteRefinement

set_option autoImplicit false
noncomputable section

namespace Kakeya4.Hard.RestrictedTriple

theorem fiber_density_power_lower {p η : ℝ} (hp : 0 < p) (hpay : 2048 ≤ p^(-η))
    (F G : Finset Plane) (H : Finset Triple) (hFne : F.Nonempty) (hGne : G.Nonempty)
    (hF : (F.card : ℝ) ≤ 4*p^(-η)/p) (hG : (G.card : ℝ) ≤ 4*p^(-η)/p)
    (hH : p^(2*η-3)/2 ≤ (H.card : ℝ)) :
    p^(6*η) ≤ ((1/2:ℝ)*(H.card : ℝ))/(8*((F.card : ℝ)*G.card^2)) := by
  have hFpos : (0:ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hFne
  have hGpos : (0:ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hGne
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 8*((F.card : ℝ)*G.card^2))).mpr
  have hprod : (p^(-η))^3*p^(6*η)/p^3 = p^(3*η-3) := by
    have hpow : (p^(-η))^3 = p^((-η)*3) := by
      rw [← Real.rpow_natCast (p^(-η)) 3,← Real.rpow_mul hp.le]
      norm_num
    rw [hpow,← Real.rpow_add hp,← Real.rpow_sub_natCast hp.ne']
    congr 1
    ring
  have hpaid : 2048*p^(3*η-3) ≤ p^(2*η-3) := by
    calc
      _ ≤ p^(-η)*p^(3*η-3) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
      _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring
  have hupper : p^(6*η)*(8*((F.card : ℝ)*G.card^2)) ≤ 512*p^(3*η-3) := by
    calc
      _ ≤ p^(6*η)*(8*((4*p^(-η)/p)*(4*p^(-η)/p)^2)) := by gcongr
      _ = 512*((p^(-η))^3*p^(6*η)/p^3) := by ring
      _ = _ := by rw [hprod]
  linarith

end Kakeya4.Hard.RestrictedTriple
