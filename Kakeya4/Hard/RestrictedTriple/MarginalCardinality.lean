import Kakeya4.Hard.RestrictedTriple.DensePrunedInput

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Kakeya4.Hard.RestrictedTriple

theorem tripartite_card_le_product (F G : Finset Plane) (Q : Finset Triple)
    (hsupport : ∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G) :
    (Q.card : ℝ) ≤ (F.card : ℝ)*G.card^2 := by
  classical
  have hsub : Q ⊆ F ×ˢ (G ×ˢ G) := by
    intro t ht
    obtain ⟨hF,hG1,hG2⟩ := hsupport t ht
    exact Finset.mem_product.mpr ⟨hF,Finset.mem_product.mpr ⟨hG1,hG2⟩⟩
  have hh := Finset.card_le_card hsub
  simp only [Finset.card_product] at hh
  rw [pow_two]
  exact_mod_cast hh

/-- The retained edge count forces both original marginal cardinalities to be large.
No separate lower-regularity assumption is supplied. -/
theorem marginal_card_lower_of_edges {p η : ℝ} (hp : 0 < p)
    (F G : Finset Plane) (Q : Finset Triple)
    (hsupport : ∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G)
    (hF : (F.card : ℝ) ≤ 4*p^(-η)/p) (hG : (G.card : ℝ) ≤ 4*p^(-η)/p)
    (hmass : p^(2*η-3)/4 ≤ (Q.card : ℝ)) :
    p^(4*η-1)/64 ≤ (F.card : ℝ) ∧ p^(4*η-1)/64 ≤ (G.card : ℝ) := by
  let L := 4*p^(-η)/p
  have hL : 0 < L := by dsimp [L]; positivity
  have hraw := tripartite_card_le_product F G Q hsupport
  have hUF : (F.card : ℝ)*G.card^2 ≤ (F.card : ℝ)*L^2 := by gcongr
  have hUG : (F.card : ℝ)*G.card^2 ≤ (G.card : ℝ)*L^2 := by
    calc
      _ = ((F.card : ℝ)*G.card)*G.card := by ring
      _ ≤ (L*G.card)*L := by gcongr
      _ = _ := by ring
  have hpower : p^(4*η-1)*(p^(-η))^2/p^2 = p^(2*η-3) := by
    rw [← Real.rpow_natCast (p^(-η)) 2,← Real.rpow_mul hp.le,← Real.rpow_add hp,
      ← Real.rpow_sub_natCast hp.ne']
    congr 1
    ring
  have hidentity : (p^(4*η-1)/64)*L^2 = p^(2*η-3)/4 := by
    calc
      _ = (p^(4*η-1)*(p^(-η))^2/p^2)/4 := by dsimp [L]; ring
      _ = _ := by rw [hpower]
  constructor
  · have hh : (p^(4*η-1)/64)*L^2 ≤ (F.card : ℝ)*L^2 := by
      rw [hidentity]
      exact hmass.trans (hraw.trans hUF)
    exact le_of_mul_le_mul_right hh (sq_pos_of_pos hL)
  · have hh : (p^(4*η-1)/64)*L^2 ≤ (G.card : ℝ)*L^2 := by
      rw [hidentity]
      exact hmass.trans (hraw.trans hUG)
    exact le_of_mul_le_mul_right hh (sq_pos_of_pos hL)

end Kakeya4.Hard.RestrictedTriple
