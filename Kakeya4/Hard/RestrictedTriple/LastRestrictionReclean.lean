import Kakeya4.Hard.RestrictedTriple.LastEndpoint

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem restrictLastEndpoint_card_product {c : ℝ} (Q : Finset Triple) (P : Finset Plane)
    (hP : P ⊆ activeTripleClasses Q 2)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    c*(((activeTripleClasses Q 0).card : ℝ)*(activeTripleClasses Q 1).card*P.card) ≤
      ((restrictLastEndpoint Q P).card : ℝ) := by
  classical
  have hactive : (Q.image tripleVertexMap).image (fun x ↦ x (2:Fin 3)) = activeTripleClasses Q 2 := by
    simp only [Finset.image_image]
    rfl
  have hP' : P ⊆ (Q.image tripleVertexMap).image (fun x ↦ x (2:Fin 3)) := by rwa [hactive]
  have hh := restrictCoordinate_card_lower hdense (2:Fin 3) P hP'
  rw [← restrictLastEndpoint_coordinate_image,Finset.card_image_of_injective _ tripleVertexMap_injective] at hh
  have hcomp : ({(2:Fin 3)} : Finset (Fin 3))ᶜ = {0,1} := by
    ext j
    fin_cases j <;> simp
  simpa [hcomp,mul_assoc,mul_left_comm,mul_comm] using hh

/-- Reclean a genuine endpoint restriction. Edge density c/16 and marginal fractions c/2
are conclusions, obtained from the original fiber lower bounds and half-retention. -/
theorem exists_recleaned_last_endpoint_restriction {c : ℝ} (hc : 0 < c)
    (Q : Finset Triple) (hne : Q.Nonempty) (P : Finset Plane) (hPne : P.Nonempty)
    (hP : P ⊆ activeTripleClasses Q 2)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    ∃ U : Finset Triple, U ⊆ restrictLastEndpoint Q P ∧ U.Nonempty ∧
      ((restrictLastEndpoint Q P).card : ℝ)/2 ≤ U.card ∧
      coordinateDensity (c/16) (activeTripleClasses U) (U.image tripleVertexMap) ∧
      (∀ j, (c/2)*((threeClasses (activeTripleClasses Q 0) (activeTripleClasses Q 1) P j).card : ℝ) ≤
        ((activeTripleClasses U j).card : ℝ)) ∧
      (∀ j, activeTripleClasses U j ⊆ threeClasses (activeTripleClasses Q 0) (activeTripleClasses Q 1) P j) := by
  classical
  let F := activeTripleClasses Q 0
  let G := activeTripleClasses Q 1
  let T := restrictLastEndpoint Q P
  have hF : (0:ℝ) < F.card := active_class_card_pos hne 0
  have hG : (0:ℝ) < G.card := active_class_card_pos hne 1
  have hPP : (0:ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hPne
  have hprod : (0:ℝ) < (F.card : ℝ)*G.card*P.card := by positivity
  have hTmass : c*((F.card : ℝ)*G.card*P.card) ≤ (T.card : ℝ) :=
    restrictLastEndpoint_card_product Q P hP hdense
  have hTne : T.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos hc hprod).trans_le hTmass
  have hsupT : ∀ t ∈ T, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ P := by
    intro t ht
    obtain ⟨htQ,htP⟩ := Finset.mem_filter.mp ht
    exact ⟨Finset.mem_image.mpr ⟨t,htQ,rfl⟩,Finset.mem_image.mpr ⟨t,htQ,rfl⟩,htP⟩
  obtain ⟨U,hUT,hUne,hret,hden⟩ := exists_three_class_refinement F G P T hTne hsupT
    (ε := 1/2) (by norm_num) (by norm_num)
  have hhalf : (T.card : ℝ)/2 ≤ U.card := by linarith
  have hcoef : c/16 ≤ ((1/2:ℝ)*(T.card : ℝ))/(8*((F.card : ℝ)*G.card*P.card)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 8) hprod)).mpr
    nlinarith
  have hsupU : ∀ t ∈ U, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ P := fun t ht ↦ hsupT t (hUT ht)
  have hsub : ∀ j, activeTripleClasses U j ⊆ threeClasses F G P j := by
    intro j
    fin_cases j <;> intro x hx <;> obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    · exact (hsupU t ht).1
    · exact (hsupU t ht).2.1
    · exact (hsupU t ht).2.2
  have hnew : coordinateDensity (c/16) (activeTripleClasses U) (U.image tripleVertexMap) :=
    coordinateDensity_shrink_classes (by positivity) hsub (activeTripleClasses_support U)
      (coordinateDensity_mono hcoef hden)
  have hUmass : (c/2)*((F.card : ℝ)*G.card*P.card) ≤ U.card := by nlinarith
  exact ⟨U,hUT,hUne,hhalf,hnew,three_marginal_lower_of_product F G P U hF hG hPP hsupU hUmass,hsub⟩

end Kakeya4.Hard.RestrictedTriple
