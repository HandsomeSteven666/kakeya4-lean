import Kakeya4.Hard.RestrictedTriple.NormalizedInput

/-! Removing the origin and endpoint diagonal from the actual restricted graph.
The deleted-edge bounds use original local counts; no uniform-density hypothesis
or complete Cartesian replacement is introduced. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal BigOperators

namespace Kakeya4.Hard.RestrictedTriple

def separatedTriples (r : ℝ) (H : Finset Triple) : Finset Triple := by
  classical
  exact H.filter (fun t ↦ r < ‖t.1‖ ∧ r < dist t.2.1 t.2.2)

theorem separatedTriples_subset (r : ℝ) (H : Finset Triple) : separatedTriples r H ⊆ H := by
  classical
  exact Finset.filter_subset _ _

theorem mem_separatedTriples {r : ℝ} {H : Finset Triple} {t : Triple} :
    t ∈ separatedTriples r H ↔ t ∈ H ∧ r < ‖t.1‖ ∧ r < dist t.2.1 t.2.2 := by
  classical
  simp [separatedTriples]

/-- Exact incidence counting before any analytic upper bounds are substituted. -/
theorem card_le_separatedTriples_add_deleted (r : ℝ) (F G : Finset Plane) (H : Finset Triple)
    (hsupport : ∀ t ∈ H, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G) :
    H.card ≤ (separatedTriples r H).card +
      (F.filter (fun a ↦ ‖a‖ ≤ r)).card*G.card^2 +
      F.card*(∑ b ∈ G, (G.filter (fun c ↦ dist b c ≤ r)).card) := by
  classical
  let badA := H.filter (fun t ↦ ‖t.1‖ ≤ r)
  let badD := H.filter (fun t ↦ dist t.2.1 t.2.2 ≤ r)
  let pairs := (G ×ˢ G).filter (fun t ↦ dist t.1 t.2 ≤ r)
  have hcover : H ⊆ (separatedTriples r H ∪ badA) ∪ badD := by
    intro t ht
    by_cases ha : r < ‖t.1‖
    · by_cases hd : r < dist t.2.1 t.2.2
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((mem_separatedTriples).mpr ⟨ht,ha,hd⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,le_of_not_gt hd⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,le_of_not_gt ha⟩))
  have hbadA : badA ⊆ (F.filter (fun a ↦ ‖a‖ ≤ r)) ×ˢ (G ×ˢ G) := by
    intro t ht
    obtain ⟨htH,htA⟩ := Finset.mem_filter.mp ht
    obtain ⟨hF,hG1,hG2⟩ := hsupport t htH
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hF,htA⟩,Finset.mem_product.mpr ⟨hG1,hG2⟩⟩
  have hbadD : badD ⊆ F ×ˢ pairs := by
    intro t ht
    obtain ⟨htH,htD⟩ := Finset.mem_filter.mp ht
    obtain ⟨hF,hG1,hG2⟩ := hsupport t htH
    exact Finset.mem_product.mpr ⟨hF,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hG1,hG2⟩,htD⟩⟩
  have hpairs : pairs.card = ∑ b ∈ G, (G.filter (fun c ↦ dist b c ≤ r)).card := by
    simp only [pairs,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
  have hAcard := Finset.card_le_card hbadA
  have hDcard := Finset.card_le_card hbadD
  simp only [Finset.card_product] at hAcard hDcard
  rw [hpairs] at hDcard
  have hsum : H.card ≤ (separatedTriples r H).card+badA.card+badD.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  calc
    _ ≤ (separatedTriples r H).card+badA.card+badD.card := hsum
    _ ≤ (separatedTriples r H).card+
        ((F.filter (fun a ↦ ‖a‖ ≤ r)).card*(G.card*G.card))+
        F.card*(∑ b ∈ G, (G.filter (fun c ↦ dist b c ≤ r)).card) := by omega
    _ = _ := by ring

theorem card_le_separatedTriples_of_local_counts (r : ℝ) (F G : Finset Plane) (H : Finset Triple)
    (hsupport : ∀ t ∈ H, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (horigin : ((F.filter (fun a ↦ ‖a‖ ≤ r)).card : ℝ) ≤ M₀)
    (hlocal : ∀ b ∈ G, ((G.filter (fun c ↦ dist b c ≤ r)).card : ℝ) ≤ M₁) :
    (H.card : ℝ) ≤ (separatedTriples r H).card +
      M₀*(G.card : ℝ)^2+(F.card : ℝ)*G.card*M₁ := by
  classical
  have hraw := card_le_separatedTriples_add_deleted r F G H hsupport
  have hcast : (H.card : ℝ) ≤ (separatedTriples r H).card+
      (F.filter (fun a ↦ ‖a‖ ≤ r)).card*(G.card : ℝ)^2+
      (F.card : ℝ)*(∑ b ∈ G, ((G.filter (fun c ↦ dist b c ≤ r)).card : ℝ)) := by
    exact_mod_cast hraw
  have hsum : (∑ b ∈ G, ((G.filter (fun c ↦ dist b c ≤ r)).card : ℝ)) ≤ (G.card : ℝ)*M₁ := by
    calc
      _ ≤ ∑ _b ∈ G, M₁ := Finset.sum_le_sum hlocal
      _ = _ := by simp
  calc
    _ ≤ _ := hcast
    _ ≤ (separatedTriples r H).card+M₀*(G.card : ℝ)^2+
        (F.card : ℝ)*((G.card : ℝ)*M₁) := by gcongr
    _ = _ := by ring

theorem finset_closedBall_count_real (P : Finset Plane) (z : Plane) (r : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hcount : (((P : Set Plane) ∩ closedBall z r).encard : ℝ≥0∞) ≤ ENNReal.ofReal M) :
    ((P.filter (fun y ↦ dist z y ≤ r)).card : ℝ) ≤ M := by
  classical
  have heq : ((P.filter (fun y ↦ dist z y ≤ r) : Finset Plane) : Set Plane) =
      (P : Set Plane) ∩ closedBall z r := by
    ext x
    simp [dist_comm]
  rw [← heq,Set.encard_coe_eq_coe_finsetCard] at hcount
  apply (ENNReal.ofReal_le_ofReal_iff hM).mp
  simpa only [ENNReal.ofReal_natCast,ENat.toENNReal_coe] using hcount

/-- Substitute the original upper-AD local bounds into the exact deleted-edge estimate. -/
theorem card_le_separatedTriples_of_AD {A B : Set Plane} {p C r : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C) (hr : p ≤ r)
    (hADa : ADUpperBound p C A) (hADb : ADUpperBound p C B)
    (F G : Finset Plane) (H : Finset Triple)
    (hFA : (F : Set Plane) ⊆ A) (hGB : (G : Set Plane) ⊆ B)
    (hFsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)))
    (hGsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)))
    (hsupport : ∀ t ∈ H, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G) :
    (H.card : ℝ) ≤ (separatedTriples r H).card+
      (2*C*r/p)*((G.card : ℝ)^2+(F.card : ℝ)*G.card) := by
  classical
  have hrpos : 0 < r := hp.trans_le hr
  have hM : 0 ≤ 2*C*r/p := by positivity
  have horigin : ((F.filter (fun a ↦ ‖a‖ ≤ r)).card : ℝ) ≤ 2*C*r/p := by
    have hh := finset_closedBall_count_real F 0 r hM
      (closedBall_local_count_of_ADUpperBound hp hADa hFA hFsep 0 hr)
    simpa only [dist_zero_left] using hh
  have hlocal : ∀ b ∈ G, ((G.filter (fun c ↦ dist b c ≤ r)).card : ℝ) ≤ 2*C*r/p := by
    intro b _hb
    exact finset_closedBall_count_real G b r hM
      (closedBall_local_count_of_ADUpperBound hp hADb hGB hGsep b hr)
  have hh := card_le_separatedTriples_of_local_counts r F G H hsupport hM hM horigin hlocal
  convert hh using 1 <;> ring

theorem finset_card_le_of_AD_unitSquare {A : Set Plane} {p C : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hC : 0 ≤ C) (hA : A ⊆ unitSquare)
    (hAD : ADUpperBound p C A) (F : Finset Plane) (hFA : (F : Set Plane) ⊆ A)
    (hsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane))) :
    (F.card : ℝ) ≤ 4*C/p := by
  classical
  have hfull : F.filter (fun y ↦ dist (0 : Plane) y ≤ 2) = F := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    simpa only [dist_zero_left] using unitSquare_norm_le_two (hA (hFA hx))
  have hh := finset_closedBall_count_real F 0 2 (show 0 ≤ 2*C*2/p by positivity)
    (closedBall_local_count_of_ADUpperBound hp hAD hFA hsep 0 (show p ≤ 2 by linarith))
  rw [hfull] at hh
  convert hh using 1 <;> ring

/-- Absolute deleted-edge budget from original AD bounds and unit-square support. -/
theorem card_le_separatedTriples_of_AD_unitSquare {A B : Set Plane} {p C r : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hC : 0 ≤ C) (hr : p ≤ r)
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare)
    (hADa : ADUpperBound p C A) (hADb : ADUpperBound p C B)
    (F G : Finset Plane) (H : Finset Triple)
    (hFA : (F : Set Plane) ⊆ A) (hGB : (G : Set Plane) ⊆ B)
    (hFsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)))
    (hGsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)))
    (hsupport : ∀ t ∈ H, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G) :
    (H.card : ℝ) ≤ (separatedTriples r H).card+64*C^3*r/p^3 := by
  have hrpos : 0 < r := hp.trans_le hr
  have hF := finset_card_le_of_AD_unitSquare hp hp1 hC hA hADa F hFA hFsep
  have hG := finset_card_le_of_AD_unitSquare hp hp1 hC hB hADb G hGB hGsep
  have hh := card_le_separatedTriples_of_AD hp hC hr hADa hADb F G H hFA hGB hFsep hGsep hsupport
  calc
    _ ≤ (separatedTriples r H).card+(2*C*r/p)*((G.card : ℝ)^2+(F.card : ℝ)*G.card) := hh
    _ ≤ (separatedTriples r H).card+(2*C*r/p)*((4*C/p)^2+(4*C/p)*(4*C/p)) := by gcongr
    _ = _ := by ring

theorem half_card_le_separatedTriples {A B : Set Plane} {p C r : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hC : 0 ≤ C) (hr : p ≤ r)
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare)
    (hADa : ADUpperBound p C A) (hADb : ADUpperBound p C B)
    (F G : Finset Plane) (H : Finset Triple)
    (hFA : (F : Set Plane) ⊆ A) (hGB : (G : Set Plane) ⊆ B)
    (hFsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)))
    (hGsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)))
    (hsupport : ∀ t ∈ H, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G)
    (hbudget : 128*C^3*r/p^3 ≤ (H.card : ℝ)) :
    (H.card : ℝ)/2 ≤ (separatedTriples r H).card := by
  have hh := card_le_separatedTriples_of_AD_unitSquare hp hp1 hC hr hA hB hADa hADb
    F G H hFA hGB hFsep hGsep hsupport
  have heq : 128*C^3*r/p^3 = 2*(64*C^3*r/p^3) := by ring
  rw [heq] at hbudget
  linarith only [hh,hbudget]

end Kakeya4.Hard.RestrictedTriple
