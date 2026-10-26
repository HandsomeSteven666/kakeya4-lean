import Kakeya4.Hard.RestrictedTriple.StandardInput

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Kakeya4.Hard.RestrictedTriple

def threeClasses (F G₁ G₂ : Finset Plane) : Fin 3 → Finset Plane := ![F,G₁,G₂]

def activeTripleClasses (Q : Finset Triple) : Fin 3 → Finset Plane :=
  threeClasses (Q.image Prod.fst) (Q.image (fun t ↦ t.2.1)) (Q.image (fun t ↦ t.2.2))

theorem activeTripleClasses_support (Q : Finset Triple) :
    ∀ x ∈ Q.image tripleVertexMap, ∀ j, x j ∈ activeTripleClasses Q j := by
  classical
  intro x hx j
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
  fin_cases j <;> simp only [activeTripleClasses,threeClasses,tripleVertexMap,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one] <;> exact Finset.mem_image.mpr ⟨t,ht,rfl⟩

theorem activeTripleClasses_mono {Q T : Finset Triple} (h : T ⊆ Q) :
    ∀ j, activeTripleClasses T j ⊆ activeTripleClasses Q j := by
  classical
  intro j
  fin_cases j <;> exact Finset.image_subset_image h

/-- Shrinking vertex classes is valid only when they still support the same edge set. -/
theorem coordinateDensity_shrink_classes {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] {c : ℝ} (hc : 0 ≤ c)
    {A B : ι → Finset α} {H : Finset (ι → α)}
    (hBA : ∀ j, B j ⊆ A j) (hsupport : ∀ x ∈ H, ∀ j, x j ∈ B j)
    (h : coordinateDensity c A H) : coordinateDensity c B H := by
  refine ⟨hsupport,?_⟩
  intro x hx I
  refine (mul_le_mul_of_nonneg_left ?_ hc).trans (h.2 x hx I)
  apply Finset.prod_le_prod₀
  · intro j hj
    exact Nat.cast_nonneg _
  · intro j hj
    exact_mod_cast Finset.card_le_card (hBA j)

/-- Actual tripartite refinement, preserving the original edges and every coordinate-subset fiber. -/
theorem exists_three_class_refinement (F G₁ G₂ : Finset Plane) (H : Finset Triple)
    (hne : H.Nonempty) (hsupport : ∀ t ∈ H, t.1 ∈ F ∧ t.2.1 ∈ G₁ ∧ t.2.2 ∈ G₂)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ Q : Finset Triple, Q ⊆ H ∧ Q.Nonempty ∧ (1-ε)*(H.card : ℝ) ≤ Q.card ∧
      coordinateDensity ((ε*(H.card : ℝ))/(8*((F.card : ℝ)*G₁.card*G₂.card)))
        (threeClasses F G₁ G₂) (Q.image tripleVertexMap) := by
  classical
  obtain ⟨t,ht⟩ := hne
  obtain ⟨htF,htG,htG2⟩ := hsupport t ht
  have hclasses : ∀ j, (threeClasses F G₁ G₂ j).Nonempty := by
    intro j
    fin_cases j
    · exact ⟨t.1,htF⟩
    · exact ⟨t.2.1,htG⟩
    · exact ⟨t.2.2,htG2⟩
  have hsup : ∀ x ∈ H.image tripleVertexMap, ∀ j, x j ∈ threeClasses F G₁ G₂ j := by
    intro x hx j
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hF,hG1,hG2⟩ := hsupport u hu
    fin_cases j
    · exact hF
    · exact hG1
    · exact hG2
  obtain ⟨T,hTH,hcard,hdensity⟩ := exists_coordinate_refinement (threeClasses F G₁ G₂) hclasses
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
  have hden : (∏ j : Fin 3, ((threeClasses F G₁ G₂ j).card : ℝ)) = (F.card : ℝ)*G₁.card*G₂.card := by
    simp [threeClasses,Fin.prod_univ_three,pow_two,mul_assoc]
  refine ⟨Q,hQH,?_,hret,?_⟩
  · apply Finset.card_pos.mp
    exact Nat.cast_pos.mp ((mul_pos (sub_pos.mpr hε1)
      (by exact_mod_cast Finset.card_pos.mpr (show H.Nonempty from ⟨t,ht⟩))).trans_le hret)
  · rw [himage]
    simpa only [hHcard,hden,Fintype.card_fin,show (2:ℝ)^3 = 8 by norm_num] using hdensity


/-- Reclean the actual three projections and report density on the retained projections. -/
theorem exists_active_class_refinement (H : Finset Triple) (hne : H.Nonempty)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ Q : Finset Triple, Q ⊆ H ∧ Q.Nonempty ∧ (1-ε)*(H.card : ℝ) ≤ Q.card ∧
      coordinateDensity ((ε*(H.card : ℝ))/(8*(∏ j : Fin 3, ((activeTripleClasses H j).card : ℝ))))
        (activeTripleClasses Q) (Q.image tripleVertexMap) := by
  classical
  have hsup : ∀ t ∈ H, t.1 ∈ H.image Prod.fst ∧
      t.2.1 ∈ H.image (fun u ↦ u.2.1) ∧ t.2.2 ∈ H.image (fun u ↦ u.2.2) := by
    intro t ht
    exact ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩,
      Finset.mem_image.mpr ⟨t,ht,rfl⟩,Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩
  obtain ⟨Q,hQH,hQne,hret,hden⟩ := exists_three_class_refinement
    (H.image Prod.fst) (H.image (fun t ↦ t.2.1)) (H.image (fun t ↦ t.2.2)) H hne hsup hε hε1
  refine ⟨Q,hQH,hQne,hret,?_⟩
  have hc : 0 ≤ (ε*(H.card : ℝ))/(8*(∏ j : Fin 3, ((activeTripleClasses H j).card : ℝ))) := by
    positivity
  apply coordinateDensity_shrink_classes hc (activeTripleClasses_mono hQH) (activeTripleClasses_support Q)
  simpa [activeTripleClasses,threeClasses,Fin.prod_univ_three,mul_assoc] using hden

theorem standardTripleGeometry_mono {Q T : Finset Triple} (h : T ⊆ Q)
    (hg : standardTripleGeometry Q) : standardTripleGeometry T := by
  exact ⟨fun t ht ↦ hg.1 t (h ht),fun t ht u hu ↦ hg.2 t (h ht) u (h hu)⟩

theorem tripleSeparated_mono {p : ℝ} {Q T : Finset Triple} (h : T ⊆ Q)
    (hs : tripleSeparated p Q) : tripleSeparated p T := by
  exact fun t ht u hu ↦ hs t (h ht) u (h hu)

end Kakeya4.Hard.RestrictedTriple
