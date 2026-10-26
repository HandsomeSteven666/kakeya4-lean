import Kakeya4.Hard.RestrictedTriple.ThreeClassRefinement

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Kakeya4.Hard.RestrictedTriple

theorem three_class_card_le_product (F G₁ G₂ : Finset Plane) (Q : Finset Triple)
    (hsupport : ∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G₁ ∧ t.2.2 ∈ G₂) :
    (Q.card : ℝ) ≤ (F.card : ℝ)*G₁.card*G₂.card := by
  classical
  have hsub : Q ⊆ F ×ˢ (G₁ ×ˢ G₂) := by
    intro t ht
    obtain ⟨hF,hG₁,hG₂⟩ := hsupport t ht
    exact Finset.mem_product.mpr ⟨hF,Finset.mem_product.mpr ⟨hG₁,hG₂⟩⟩
  have h := Finset.card_le_card hsub
  simp only [Finset.card_product] at h
  exact_mod_cast (by simpa [mul_assoc] using h)

theorem active_class_card_product (Q : Finset Triple) :
    (Q.card : ℝ) ≤ ∏ j : Fin 3, ((activeTripleClasses Q j).card : ℝ) := by
  classical
  have hs : ∀ t ∈ Q, t.1 ∈ Q.image Prod.fst ∧
      t.2.1 ∈ Q.image (fun u ↦ u.2.1) ∧ t.2.2 ∈ Q.image (fun u ↦ u.2.2) := by
    intro t ht
    exact ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩,
      Finset.mem_image.mpr ⟨t,ht,rfl⟩,Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩
  simpa [activeTripleClasses,threeClasses,Fin.prod_univ_three,mul_assoc] using
    three_class_card_le_product _ _ _ Q hs

theorem active_class_card_pos {Q : Finset Triple} (hQ : Q.Nonempty) (j : Fin 3) :
    (0 : ℝ) < (activeTripleClasses Q j).card := by
  obtain ⟨t,ht⟩ := hQ
  have hmem := activeTripleClasses_support Q
    (tripleVertexMap t) (Finset.mem_image.mpr ⟨t,ht,rfl⟩) j
  exact_mod_cast Finset.card_pos.mpr (show (activeTripleClasses Q j).Nonempty from ⟨_,hmem⟩)

/-- Every marginal is forced large by the same retained edge graph. -/
theorem selected_marginal_lower {p η : ℝ} (hp : 0 < p) (Q : Finset Triple)
    (hu : ∀ j, ((activeTripleClasses Q j).card : ℝ) ≤ 4*p^(-η)/p)
    (hmass : p^(39*η-3)/8 ≤ (Q.card : ℝ)) :
    ∀ j, p^(41*η-1)/128 ≤ ((activeTripleClasses Q j).card : ℝ) := by
  let L : ℝ := 4*p^(-η)/p
  have hL : 0 < L := by dsimp [L]; positivity
  have hproduct := active_class_card_product Q
  have hi : (p^(41*η-1)/128)*L^2 = p^(39*η-3)/8 := by
    have hpow : p^(41*η-1)*(p^(-η))^2/p^2 = p^(39*η-3) := by
      rw [← Real.rpow_natCast (p^(-η)) 2,← Real.rpow_mul hp.le,← Real.rpow_add hp,
        ← Real.rpow_sub_natCast hp.ne']
      congr 1
      ring
    calc
      _ = (p^(41*η-1)*(p^(-η))^2/p^2)/8 := by dsimp [L]; ring
      _ = _ := by rw [hpow]
  intro j
  suffices hh : (p^(41*η-1)/128)*L^2 ≤ ((activeTripleClasses Q j).card : ℝ)*L^2 by
    exact le_of_mul_le_mul_right hh (sq_pos_of_pos hL)
  rw [hi]
  refine hmass.trans (hproduct.trans ?_)
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  have hn (i : Fin 3) : (0:ℝ) ≤ (activeTripleClasses Q i).card := Nat.cast_nonneg _
  rw [Fin.prod_univ_three]
  fin_cases j
  · calc
      _ ≤ ((activeTripleClasses Q 0).card : ℝ)*L*L := by gcongr
      _ = _ := by simp [activeTripleClasses,threeClasses]; ring
  · calc
      _ ≤ L*((activeTripleClasses Q 1).card : ℝ)*L := by gcongr
      _ = _ := by simp [activeTripleClasses,threeClasses]; ring
  · calc
      _ ≤ L*L*((activeTripleClasses Q 2).card : ℝ) := by gcongr
      _ = _ := by simp [activeTripleClasses,threeClasses]; ring

theorem selected_density_power_lower {p η : ℝ} (hp : 0 < p) (hpay : 4096 ≤ p^(-η))
    (Q : Finset Triple) (hne : Q.Nonempty)
    (hu : ∀ j, ((activeTripleClasses Q j).card : ℝ) ≤ 4*p^(-η)/p)
    (hmass : p^(39*η-3)/4 ≤ (Q.card : ℝ)) :
    p^(43*η) ≤ ((1/2:ℝ)*(Q.card : ℝ))/(8*(∏ j : Fin 3, ((activeTripleClasses Q j).card : ℝ))) := by
  have hpos : 0 < ∏ j : Fin 3, ((activeTripleClasses Q j).card : ℝ) :=
    Finset.prod_pos (fun j _ ↦ active_class_card_pos hne j)
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 8*(∏ j : Fin 3, ((activeTripleClasses Q j).card : ℝ)))).mpr
  have hprod : (p^(-η))^3*p^(43*η)/p^3 = p^(40*η-3) := by
    rw [← Real.rpow_natCast (p^(-η)) 3,← Real.rpow_mul hp.le,← Real.rpow_add hp,
      ← Real.rpow_sub_natCast hp.ne']
    congr 1
    ring
  have hpaid : 4096*p^(40*η-3) ≤ p^(39*η-3) := by
    calc
      _ ≤ p^(-η)*p^(40*η-3) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
      _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring
  have hupper : p^(43*η)*(8*(∏ j : Fin 3, ((activeTripleClasses Q j).card : ℝ))) ≤ 512*p^(40*η-3) := by
    calc
      _ ≤ p^(43*η)*(8*((4*p^(-η)/p)^3)) := by
        gcongr
        calc
          _ ≤ ∏ _j : Fin 3, (4*p^(-η)/p) := Finset.prod_le_prod₀
            (fun j _ ↦ Nat.cast_nonneg _) (fun j _ ↦ hu j)
          _ = _ := by simp [div_pow]
      _ = 512*((p^(-η))^3*p^(43*η)/p^3) := by ring
      _ = _ := by rw [hprod]
  linarith

/-- Actual post-selection cleaning with paid density on its own active projections. -/
theorem exists_selected_dense_graph {p η : ℝ} (hp : 0 < p) (hpay : 4096 ≤ p^(-η))
    (H : Finset Triple) (hne : H.Nonempty)
    (hu : ∀ j, ((activeTripleClasses H j).card : ℝ) ≤ 4*p^(-η)/p)
    (hmass : p^(39*η-3)/4 ≤ (H.card : ℝ)) :
    ∃ Q : Finset Triple, Q ⊆ H ∧ Q.Nonempty ∧ p^(39*η-3)/8 ≤ (Q.card : ℝ) ∧
      (∀ j, p^(41*η-1)/128 ≤ ((activeTripleClasses Q j).card : ℝ)) ∧
      coordinateDensity (p^(43*η)) (activeTripleClasses Q) (Q.image tripleVertexMap) := by
  obtain ⟨Q,hQH,hQne,hret,hdense⟩ := exists_active_class_refinement H hne
    (ε := 1/2) (by norm_num) (by norm_num)
  have hmassQ : p^(39*η-3)/8 ≤ (Q.card : ℝ) := by linarith
  have huQ : ∀ j, ((activeTripleClasses Q j).card : ℝ) ≤ 4*p^(-η)/p := by
    intro j
    have hh : ((activeTripleClasses Q j).card : ℝ) ≤ (activeTripleClasses H j).card := by
      exact_mod_cast Finset.card_le_card (activeTripleClasses_mono hQH j)
    exact hh.trans (hu j)
  refine ⟨Q,hQH,hQne,hmassQ,selected_marginal_lower hp Q huQ hmassQ,?_⟩
  exact coordinateDensity_mono (selected_density_power_lower hp hpay H hne hu hmass) hdense

end Kakeya4.Hard.RestrictedTriple
