import Kakeya4.Hard.RestrictedTriple.GeometricPruning

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem geometric_pruning_power_budget {p η : ℝ} (hp : 0 < p) (hpay : 128 ≤ p^(-η)) :
    128*(p^(-η))^3*p^(6*η)/p^3 ≤ p^(2*η-3) := by
  have hCpow : (p^(-η))^3 = p^(-3*η) := by
    calc
      _ = (p^(-η))^(3:ℝ) := (Real.rpow_natCast _ 3).symm
      _ = p^((-η)*3) := (Real.rpow_mul hp.le _ _).symm
      _ = _ := by congr 1; ring
  have hprod : (p^(-η))^3*p^(6*η)/p^3 = p^(3*η-3) := by
    rw [hCpow,← Real.rpow_add hp,← Real.rpow_sub_natCast hp.ne']
    congr 1
    ring
  calc
    _ = 128*((p^(-η))^3*p^(6*η)/p^3) := by ring
    _ = 128*p^(3*η-3) := by rw [hprod]
    _ ≤ p^(-η)*p^(3*η-3) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
    _ = p^(2*η-3) := by rw [← Real.rpow_add hp]; congr 1; ring

/-- A single threshold selected before all graphs pays the geometric deleted-edge budget. -/
theorem exists_uniform_geometric_budget {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/6) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      p ≤ p^(6*η) ∧ 128 ≤ p^(-η) ∧ 128*(p^(-η))^3*p^(6*η)/p^3 ≤ p^(2*η-3) := by
  obtain ⟨p₀,hp₀,hp₀1,hpay⟩ := exists_constant_power_payment 128 (by norm_num) hη
  refine ⟨p₀,hp₀,hp₀1,?_⟩
  intro p hp hpp
  have hp1 : p ≤ 1 := (hpp.trans_lt hp₀1).le
  refine ⟨?_,hpay p hp hpp,geometric_pruning_power_budget hp (hpay p hp hpp)⟩
  have hh := Real.rpow_le_rpow_of_exponent_ge hp hp1 (show 6*η ≤ 1 by linarith)
  simpa only [Real.rpow_one] using hh

theorem retained_half_of_power_budget {A B : Set Plane} {p η : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hr : p ≤ p^(6*η)) (hpay : 128 ≤ p^(-η))
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare)
    (hADa : ADUpperBound p (p^(-η)) A) (hADb : ADUpperBound p (p^(-η)) B)
    (F G : Finset Plane) (H : Finset Triple)
    (hFA : (F : Set Plane) ⊆ A) (hGB : (G : Set Plane) ⊆ B)
    (hFsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)))
    (hGsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)))
    (hsupport : ∀ t ∈ H, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G)
    (hlarge : p^(2*η-3) ≤ (H.card : ℝ)) :
    p^(2*η-3)/2 ≤ (separatedTriples (p^(6*η)) H).card ∧
      (separatedTriples (p^(6*η)) H).Nonempty := by
  have hb := (geometric_pruning_power_budget hp hpay).trans hlarge
  have hh := half_card_le_separatedTriples hp hp1 (Real.rpow_pos_of_pos hp _).le hr
    hA hB hADa hADb F G H hFA hGB hFsep hGsep hsupport hb
  have hret : p^(2*η-3)/2 ≤ (separatedTriples (p^(6*η)) H).card := by linarith
  refine ⟨hret,?_⟩
  apply Finset.card_pos.mp
  exact Nat.cast_pos.mp ((show (0:ℝ) < p^(2*η-3)/2 by positivity).trans_le hret)

end Kakeya4.Hard.RestrictedTriple
