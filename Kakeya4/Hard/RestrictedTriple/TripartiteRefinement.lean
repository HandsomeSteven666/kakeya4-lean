import Kakeya4.Hard.RestrictedTriple.CoordinateRefinement

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Kakeya4.Hard.RestrictedTriple

def tripleVertexMap (t : Triple) : Fin 3 → Plane := ![t.1,t.2.1,t.2.2]
def tripleClasses (F G : Finset Plane) : Fin 3 → Finset Plane := ![F,G,G]

theorem tripleVertexMap_injective : Function.Injective tripleVertexMap := by
  intro t u h
  apply Prod.ext
  · simpa [tripleVertexMap] using congrFun h 0
  · apply Prod.ext
    · simpa [tripleVertexMap] using congrFun h 1
    · simpa [tripleVertexMap] using congrFun h 2

/-- Actual tripartite refinement, preserving the original edges and every coordinate-subset fiber. -/
theorem exists_tripartite_refinement (F G : Finset Plane) (H : Finset Triple)
    (hne : H.Nonempty) (hsupport : ∀ t ∈ H, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ Q : Finset Triple, Q ⊆ H ∧ Q.Nonempty ∧ (1-ε)*(H.card : ℝ) ≤ Q.card ∧
      coordinateDensity ((ε*(H.card : ℝ))/(8*((F.card : ℝ)*G.card^2)))
        (tripleClasses F G) (Q.image tripleVertexMap) := by
  classical
  obtain ⟨t,ht⟩ := hne
  obtain ⟨htF,htG,_htG2⟩ := hsupport t ht
  have hclasses : ∀ j, (tripleClasses F G j).Nonempty := by
    intro j
    fin_cases j
    · exact ⟨t.1,htF⟩
    · exact ⟨t.2.1,htG⟩
    · exact ⟨t.2.1,htG⟩
  have hsup : ∀ x ∈ H.image tripleVertexMap, ∀ j, x j ∈ tripleClasses F G j := by
    intro x hx j
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hF,hG1,hG2⟩ := hsupport u hu
    fin_cases j
    · exact hF
    · exact hG1
    · exact hG2
  obtain ⟨T,hTH,hcard,hdensity⟩ := exists_coordinate_refinement (tripleClasses F G) hclasses
    (H.image tripleVertexMap) hsup hε
  let Q := H.filter (fun u ↦ tripleVertexMap u ∈ T)
  have hQH : Q ⊆ H := Finset.filter_subset _ _
  have himage : Q.image tripleVertexMap = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hu).2
    · intro hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (hTH hx)
      exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hx⟩,rfl⟩
  have hQcard : Q.card = T.card := by
    rw [← himage,Finset.card_image_of_injective _ tripleVertexMap_injective]
  have hHcard : (H.image tripleVertexMap).card = H.card :=
    Finset.card_image_of_injective _ tripleVertexMap_injective
  have hret : (1-ε)*(H.card : ℝ) ≤ Q.card := by rwa [hHcard,← hQcard] at hcard
  have hden : (∏ j : Fin 3, ((tripleClasses F G j).card : ℝ)) = (F.card : ℝ)*G.card^2 := by
    simp [tripleClasses,Fin.prod_univ_three,pow_two,mul_assoc]
  refine ⟨Q,hQH,?_,hret,?_⟩
  · apply Finset.card_pos.mp
    exact Nat.cast_pos.mp ((mul_pos (sub_pos.mpr hε1)
      (by exact_mod_cast Finset.card_pos.mpr (show H.Nonempty from ⟨t,ht⟩))).trans_le hret)
  · rw [himage]
    simpa only [hHcard,hden,Fintype.card_fin,show (2:ℝ)^3 = 8 by norm_num] using hdensity

end Kakeya4.Hard.RestrictedTriple
