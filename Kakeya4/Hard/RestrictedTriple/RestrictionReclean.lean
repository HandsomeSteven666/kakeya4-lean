import Kakeya4.Hard.RestrictedTriple.TwoEndsGraph

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem three_marginal_lower_of_product {d : ℝ} (F G₁ G₂ : Finset Plane) (U : Finset Triple)
    (hF : (0:ℝ) < F.card) (hG₁ : (0:ℝ) < G₁.card) (hG₂ : (0:ℝ) < G₂.card)
    (hsup : ∀ t ∈ U, t.1 ∈ F ∧ t.2.1 ∈ G₁ ∧ t.2.2 ∈ G₂)
    (hmass : d*((F.card : ℝ)*G₁.card*G₂.card) ≤ U.card) :
    ∀ j, d*((threeClasses F G₁ G₂ j).card : ℝ) ≤ ((activeTripleClasses U j).card : ℝ) := by
  classical
  intro j
  fin_cases j
  · change d*(F.card : ℝ) ≤ ((activeTripleClasses U 0).card : ℝ)
    have hu := three_class_card_le_product (activeTripleClasses U 0) G₁ G₂ U (by
      intro t ht
      exact ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩,(hsup t ht).2⟩)
    have hh : (d*(F.card : ℝ))*((G₁.card : ℝ)*G₂.card) ≤
        ((activeTripleClasses U 0).card : ℝ)*((G₁.card : ℝ)*G₂.card) := by nlinarith
    exact le_of_mul_le_mul_right hh (mul_pos hG₁ hG₂)
  · change d*(G₁.card : ℝ) ≤ ((activeTripleClasses U 1).card : ℝ)
    have hu := three_class_card_le_product F (activeTripleClasses U 1) G₂ U (by
      intro t ht
      exact ⟨(hsup t ht).1,Finset.mem_image.mpr ⟨t,ht,rfl⟩,(hsup t ht).2.2⟩)
    have hh : (d*(G₁.card : ℝ))*((F.card : ℝ)*G₂.card) ≤
        ((activeTripleClasses U 1).card : ℝ)*((F.card : ℝ)*G₂.card) := by nlinarith
    exact le_of_mul_le_mul_right hh (mul_pos hF hG₂)
  · change d*(G₂.card : ℝ) ≤ ((activeTripleClasses U 2).card : ℝ)
    have hu := three_class_card_le_product F G₁ (activeTripleClasses U 2) U (by
      intro t ht
      exact ⟨(hsup t ht).1,(hsup t ht).2.1,Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩)
    have hh : (d*(G₂.card : ℝ))*((F.card : ℝ)*G₁.card) ≤
        ((activeTripleClasses U 2).card : ℝ)*((F.card : ℝ)*G₁.card) := by nlinarith
    exact le_of_mul_le_mul_right hh (mul_pos hF hG₁)

theorem restrictFirstEndpoint_card_product {c : ℝ} (Q : Finset Triple) (P : Finset Plane)
    (hP : P ⊆ activeTripleClasses Q 1)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    c*(((activeTripleClasses Q 0).card : ℝ)*P.card*(activeTripleClasses Q 2).card) ≤
      ((restrictFirstEndpoint Q P).card : ℝ) := by
  classical
  have hactive : (Q.image tripleVertexMap).image (fun x ↦ x (1:Fin 3)) = activeTripleClasses Q 1 := by
    simp only [Finset.image_image]
    rfl
  have hP' : P ⊆ (Q.image tripleVertexMap).image (fun x ↦ x (1:Fin 3)) := by rwa [hactive]
  have hh := restrictCoordinate_card_lower hdense (1:Fin 3) P hP'
  rw [← restrictFirstEndpoint_coordinate_image,Finset.card_image_of_injective _ tripleVertexMap_injective] at hh
  have hcomp : ({(1:Fin 3)} : Finset (Fin 3))ᶜ = {0,2} := by
    ext j
    fin_cases j <;> simp
  simpa [hcomp,mul_assoc,mul_left_comm,mul_comm] using hh

/-- Reclean a genuine endpoint restriction. Edge density c/16 and marginal fractions c/2
are conclusions, obtained from the original fiber lower bounds and half-retention. -/
theorem exists_recleaned_endpoint_restriction {c : ℝ} (hc : 0 < c)
    (Q : Finset Triple) (hne : Q.Nonempty) (P : Finset Plane) (hPne : P.Nonempty)
    (hP : P ⊆ activeTripleClasses Q 1)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    ∃ U : Finset Triple, U ⊆ restrictFirstEndpoint Q P ∧ U.Nonempty ∧
      ((restrictFirstEndpoint Q P).card : ℝ)/2 ≤ U.card ∧
      coordinateDensity (c/16) (activeTripleClasses U) (U.image tripleVertexMap) ∧
      (∀ j, (c/2)*((threeClasses (activeTripleClasses Q 0) P (activeTripleClasses Q 2) j).card : ℝ) ≤
        ((activeTripleClasses U j).card : ℝ)) ∧
      (∀ j, activeTripleClasses U j ⊆ threeClasses (activeTripleClasses Q 0) P (activeTripleClasses Q 2) j) := by
  classical
  let F := activeTripleClasses Q 0
  let G := activeTripleClasses Q 2
  let T := restrictFirstEndpoint Q P
  have hF : (0:ℝ) < F.card := active_class_card_pos hne 0
  have hG : (0:ℝ) < G.card := active_class_card_pos hne 2
  have hPP : (0:ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hPne
  have hprod : (0:ℝ) < (F.card : ℝ)*P.card*G.card := by positivity
  have hTmass : c*((F.card : ℝ)*P.card*G.card) ≤ (T.card : ℝ) :=
    restrictFirstEndpoint_card_product Q P hP hdense
  have hTne : T.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos hc hprod).trans_le hTmass
  have hsupT : ∀ t ∈ T, t.1 ∈ F ∧ t.2.1 ∈ P ∧ t.2.2 ∈ G := by
    intro t ht
    obtain ⟨htQ,htP⟩ := Finset.mem_filter.mp ht
    exact ⟨Finset.mem_image.mpr ⟨t,htQ,rfl⟩,htP,Finset.mem_image.mpr ⟨t,htQ,rfl⟩⟩
  obtain ⟨U,hUT,hUne,hret,hden⟩ := exists_three_class_refinement F P G T hTne hsupT
    (ε := 1/2) (by norm_num) (by norm_num)
  have hhalf : (T.card : ℝ)/2 ≤ U.card := by linarith
  have hcoef : c/16 ≤ ((1/2:ℝ)*(T.card : ℝ))/(8*((F.card : ℝ)*P.card*G.card)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 8) hprod)).mpr
    nlinarith
  have hsupU : ∀ t ∈ U, t.1 ∈ F ∧ t.2.1 ∈ P ∧ t.2.2 ∈ G := fun t ht ↦ hsupT t (hUT ht)
  have hsub : ∀ j, activeTripleClasses U j ⊆ threeClasses F P G j := by
    intro j
    fin_cases j <;> intro x hx <;> obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    · exact (hsupU t ht).1
    · exact (hsupU t ht).2.1
    · exact (hsupU t ht).2.2
  have hnew : coordinateDensity (c/16) (activeTripleClasses U) (U.image tripleVertexMap) :=
    coordinateDensity_shrink_classes (by positivity) hsub (activeTripleClasses_support U)
      (coordinateDensity_mono hcoef hden)
  have hUmass : (c/2)*((F.card : ℝ)*P.card*G.card) ≤ U.card := by nlinarith
  exact ⟨U,hUT,hUne,hhalf,hnew,three_marginal_lower_of_product F P G U hF hPP hG hsupU hUmass,hsub⟩

end Kakeya4.Hard.RestrictedTriple
