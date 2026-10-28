import Kakeya4.Hard.RestrictedTriple.OrthogonalStripAlternative

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem LongIntervalExpansion.mono {p ε η : ℝ} {T Q : Set Triple}
    (h : LongIntervalExpansion p ε η T) (hTQ : T ⊆ Q) : LongIntervalExpansion p ε η Q := by
  obtain ⟨s,l,u,hs,hlu,hwidth,hlower⟩ := h
  exact ⟨s,l,u,hs,hlu,hwidth,hlower.trans (intervalCover_mono
    (inter_subset_inter_right _ (Set.image_mono hTQ)))⟩

/-- Produce a sequentially selected actual graph, then enforce the first orthogonal
localization step unless the original finite graph already expands. -/
theorem exists_uniform_sequential_orthogonal_input {α η ζ ε ηₑ : ℝ}
    (hα : 0 < α) (hη : 0 < η) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hε : 0 ≤ ε) (hηₑ : ηₑ ≤ α) (hgap : 0 < α*ε-2*(133*η+2*ζ)) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∀ Q : Finset Triple, Q.Nonempty →
        standardTripleGeometry Q → tripleSeparated p Q →
        coordinateDensity (p^(44*η)) (activeTripleClasses Q) (Q.image tripleVertexMap) →
        (∀ j, finiteFrostman p (p^(-44*η)) (activeTripleClasses Q j)) →
        LongIntervalExpansion p ε ηₑ (Q : Set Triple) ∨
        ∃ w₁ w₂ : ℝ, (p/2 ≤ w₁ ∧ w₁ ≤ 1) ∧ (p/2 ≤ w₂ ∧ w₂ ≤ 1) ∧
          ∃ L₁ L₂ : AffineLine, ∃ T : Finset Triple,
            T ⊆ Q ∧ T.Nonempty ∧ standardTripleGeometry T ∧ tripleSeparated p T ∧
            (∀ x ∈ activeTripleClasses T 1, x ∈ lineNeighborhood w₁ L₁) ∧
            (∀ x ∈ activeTripleClasses T 2, x ∈ lineNeighborhood w₂ L₂) ∧
            p^(133*η+2*ζ)*(Q.card : ℝ) ≤ (T.card : ℝ) ∧
            coordinateDensity (p^(133*η+2*ζ)) (activeTripleClasses T) (T.image tripleVertexMap) ∧
            (∀ j, finiteFrostman p (p^(-(133*η+2*ζ))) (activeTripleClasses T j)) ∧
            (∀ r : ℝ, p ≤ r → ∀ L : AffineLine,
              (((activeTripleClasses T 1).filter (fun x ↦ x ∈ lineNeighborhood r L)).card : ℝ) ≤
                p^(-(133*η+2*ζ))*(r/w₁)^ζ*((activeTripleClasses T 1).card : ℝ)) ∧
            (∀ r : ℝ, p ≤ r → ∀ L : AffineLine,
              (((activeTripleClasses T 2).filter (fun x ↦ x ∈ lineNeighborhood r L)).card : ℝ) ≤
                p^(-(133*η+2*ζ))*(r/w₂)^ζ*((activeTripleClasses T 2).card : ℝ)) ∧
            (∀ x ∈ activeTripleClasses T 0,
              x ∈ lineNeighborhood (p^(-α)*w₁) (orthogonalOriginLine L₁)) := by
  obtain ⟨p₁,hp₁,hp₁one,hseq⟩ := exists_uniform_sequential_two_ends hη
  obtain ⟨p₂,hp₂,_hp₂one,halt⟩ :=
    exists_uniform_strip_expansion_or_orthogonal_localization hα hε hηₑ hgap
  refine ⟨min p₁ p₂,lt_min hp₁ hp₂,(min_le_left _ _).trans_lt hp₁one,?_⟩
  intro p hp hpp Q hne hgeom hsep hdense hF
  obtain ⟨w₁,w₂,hw₁,hw₂,L₁,L₂,T,hTQ,hTne,hgeomT,hsepT,hstrip₁,hstrip₂,hmass,hden,hFT,hnc₁,hnc₂⟩ :=
    hseq p hp (hpp.trans (min_le_left _ _)) ζ hζ hζ1 Q hne hgeom hsep hdense hF
  have hw₁pos : 0 < w₁ := lt_of_lt_of_le (by positivity : 0 < p/2) hw₁.1
  have hcut : p ≤ 2*w₁ := by linarith [hw₁.1]
  rcases halt p hp (hpp.trans (min_le_right _ _)) w₁ L₁ T hw₁pos hcut hgeomT hden (hFT 1) hstrip₁ with hexpand | hlocal
  · exact Or.inl (hexpand.mono hTQ)
  · exact Or.inr ⟨w₁,w₂,hw₁,hw₂,L₁,L₂,T,hTQ,hTne,hgeomT,hsepT,hstrip₁,hstrip₂,
      hmass,hden,hFT,hnc₁,hnc₂,hlocal⟩

end Kakeya4.Hard.RestrictedTriple
