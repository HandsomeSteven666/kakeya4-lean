import Kakeya4.Hard.RestrictedTriple.DirectionRelation

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal BigOperators Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem pair_card_le_product (F G : Finset Plane) (X : Finset (Plane × Plane))
    (hsup : ∀ v ∈ X, v.1 ∈ F ∧ v.2 ∈ G) : (X.card : ℝ) ≤ (F.card : ℝ)*(G.card : ℝ) := by
  have hsub : X ⊆ F ×ˢ G := fun v hv ↦ Finset.mem_product.mpr (hsup v hv)
  have hh := Finset.card_le_card hsub
  rw [Finset.card_product] at hh
  exact_mod_cast hh

/-- Genuine two-sided pair cleaning with explicit degree and marginal losses. -/
theorem exists_bipartite_degree_cleaning {c : ℝ} (hc : 0 < c)
    (F G : Finset Plane) (hFne : F.Nonempty) (hGne : G.Nonempty) (X : Finset (Plane × Plane))
    (hsup : ∀ v ∈ X, v.1 ∈ F ∧ v.2 ∈ G)
    (hmass : c*(F.card : ℝ)*(G.card : ℝ) ≤ X.card) :
    ∃ T : Finset (Plane × Plane), T ⊆ X ∧ T.Nonempty ∧ (X.card : ℝ)/2 ≤ T.card ∧
      (c/2)*(F.card : ℝ) ≤ ((T.image Prod.fst).card : ℝ) ∧
      (c/2)*(G.card : ℝ) ≤ ((T.image Prod.snd).card : ℝ) ∧
      (∀ v ∈ T, (c/4)*(G.card : ℝ) ≤ ((T.filter (fun u ↦ u.1 = v.1)).card : ℝ)) ∧
      (∀ v ∈ T, (c/4)*(F.card : ℝ) ≤ ((T.filter (fun u ↦ u.2 = v.2)).card : ℝ)) := by
  let f : Bool → (Plane × Plane) → Plane := fun i v ↦ if i then v.1 else v.2
  let w : Bool → ℝ := fun i ↦ if i then c*(G.card : ℝ)/4 else c*(F.card : ℝ)/4
  have hF : (0:ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hFne
  have hG : (0:ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hGne
  have hXF : ((X.image Prod.fst).card : ℝ) ≤ F.card := by
    exact_mod_cast Finset.card_le_card (show X.image Prod.fst ⊆ F from by
      intro a ha; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha; exact (hsup v hv).1)
  have hXG : ((X.image Prod.snd).card : ℝ) ≤ G.card := by
    exact_mod_cast Finset.card_le_card (show X.image Prod.snd ⊆ G from by
      intro a ha; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha; exact (hsup v hv).2)
  have hw : ∀ i ∈ (Finset.univ : Finset Bool), 0 ≤ w i := by
    intro i hi
    cases i <;> simp only [w,Bool.false_eq_true,↓reduceIte] <;> positivity
  have hbudget : (∑ i ∈ (Finset.univ : Finset Bool), w i*((X.image (f i)).card : ℝ)) ≤
      (1/2)*(X.card : ℝ) := by
    calc
      _ = (c*(F.card : ℝ)/4)*((X.image Prod.snd).card : ℝ)+
          (c*(G.card : ℝ)/4)*((X.image Prod.fst).card : ℝ) := by simp [f,w,add_comm]
      _ ≤ (c*(F.card : ℝ)/4)*(G.card : ℝ)+(c*(G.card : ℝ)/4)*(F.card : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hXG (by positivity))
          (mul_le_mul_of_nonneg_left hXF (by positivity))
      _ ≤ _ := by nlinarith [hmass]
  obtain ⟨T,hTX,hret,hdegrees⟩ := exists_simultaneous_fiber_cleaning_of_budget
    (Finset.univ : Finset Bool) f w X hw hbudget
  have hXpos : (0:ℝ) < X.card := (by positivity : 0 < c*(F.card : ℝ)*(G.card : ℝ)).trans_le hmass
  have hTpos : (0:ℝ) < T.card := by nlinarith [hret]
  have hTne : T.Nonempty := Finset.card_pos.mp (by exact_mod_cast hTpos)
  have hTmass : (c/2)*(F.card : ℝ)*(G.card : ℝ) ≤ T.card := by nlinarith [hret]
  have hTF := pair_card_le_product (T.image Prod.fst) G T (by
    intro v hv; exact ⟨Finset.mem_image.mpr ⟨v,hv,rfl⟩,(hsup v (hTX hv)).2⟩)
  have hTG := pair_card_le_product F (T.image Prod.snd) T (by
    intro v hv; exact ⟨(hsup v (hTX hv)).1,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩)
  have hfirst : (c/2)*(F.card : ℝ) ≤ ((T.image Prod.fst).card : ℝ) := by
    exact le_of_mul_le_mul_right (hTmass.trans hTF) hG
  have hsecond : (c/2)*(G.card : ℝ) ≤ ((T.image Prod.snd).card : ℝ) := by
    have hh : ((c/2)*(G.card : ℝ))*(F.card : ℝ) ≤
        ((T.image Prod.snd).card : ℝ)*(F.card : ℝ) := by nlinarith [hTmass.trans hTG]
    exact le_of_mul_le_mul_right hh hF
  refine ⟨T,hTX,hTne,(by nlinarith [hret]),hfirst,hsecond,?_,?_⟩
  · intro v hv
    have hh := hdegrees true (by simp) v hv
    simpa only [f,w,↓reduceIte,div_mul_eq_mul_div] using hh
  · intro v hv
    have hh := hdegrees false (by simp) v hv
    simpa only [f,w,Bool.false_eq_true,↓reduceIte,div_mul_eq_mul_div] using hh

/-- Actual selected-direction witnesses followed by genuine pair cleaning. -/
theorem exists_cleaned_direction_relation {c : ℝ} (hc : 0 < c)
    (Q : Finset Triple) (q : Triple) (hq : q ∈ Q) (Ω : Finset Plane) (hΩ : Ω.Nonempty)
    (f : Plane → Plane) (hsrc : (Ω : Set Plane) ⊆ f '' (fixedOuterFiber Q q : Set Plane))
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    ∃ b : Plane → Plane, ∃ T : Finset (Plane × Plane),
      (∀ θ ∈ Ω, b θ ∈ fixedOuterFiber Q q ∧ f (b θ) = θ) ∧ Set.InjOn b (Ω : Set Plane) ∧
      T ⊆ occupiedDirectionRelation Q q.2.2 Ω b ∧ T.Nonempty ∧
      (c/2)*((activeTripleClasses Q 0).card : ℝ)*(Ω.card : ℝ) ≤ T.card ∧
      (c/2)*((activeTripleClasses Q 0).card : ℝ) ≤ ((T.image Prod.fst).card : ℝ) ∧
      (c/2)*(Ω.card : ℝ) ≤ ((T.image Prod.snd).card : ℝ) ∧
      (∀ v ∈ T, (v.1,b v.2,q.2.2) ∈ Q) ∧
      (∀ v ∈ T, (c/4)*(Ω.card : ℝ) ≤ ((T.filter (fun u ↦ u.1 = v.1)).card : ℝ)) ∧
      (∀ v ∈ T, (c/4)*((activeTripleClasses Q 0).card : ℝ) ≤ ((T.filter (fun u ↦ u.2 = v.2)).card : ℝ)) := by
  obtain ⟨b,hb,hinj,hmass,_hfib⟩ := exists_actual_direction_relation Q q Ω f hsrc hdense
  let X := occupiedDirectionRelation Q q.2.2 Ω b
  have hF : (activeTripleClasses Q 0).Nonempty := ⟨q.1,Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
  obtain ⟨T,hTX,hTne,hret,hfirst,hsecond,hdeg₁,hdeg₂⟩ := exists_bipartite_degree_cleaning hc
    (activeTripleClasses Q 0) Ω hF hΩ X
    (fun v hv ↦ ⟨(occupiedDirectionRelation_support Q q.2.2 Ω b v hv).1,
      (occupiedDirectionRelation_support Q q.2.2 Ω b v hv).2.1⟩) hmass
  refine ⟨b,T,hb,hinj,hTX,hTne,(by nlinarith [hmass]),hfirst,hsecond,?_,hdeg₁,hdeg₂⟩
  exact fun v hv ↦ (occupiedDirectionRelation_support Q q.2.2 Ω b v (hTX hv)).2.2

end Kakeya4.Hard.RestrictedTriple
