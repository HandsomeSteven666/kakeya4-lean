import Kakeya4.Hard.RestrictedTriple.LastTwoEndsCleanGraph

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Classical

namespace Kakeya4.Hard.RestrictedTriple

/-- Sequential, not independent, selection of both endpoint strips in the actual graph.
The first strip bound is repriced using the proved first-marginal retention in the second step. -/
theorem exists_sequential_two_ends_graph {p ζ c K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hc : 0 < c) (hK : 0 ≤ K)
    (Q : Finset Triple) (hne : Q.Nonempty) (hgeom : standardTripleGeometry Q)
    (hsep : tripleSeparated p Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : ∀ j, finiteFrostman p K (activeTripleClasses Q j)) :
    ∃ w₁ w₂ : ℝ, (p/2 ≤ w₁ ∧ w₁ ≤ 1) ∧ (p/2 ≤ w₂ ∧ w₂ ≤ 1) ∧
      ∃ L₁ L₂ : AffineLine, ∃ T : Finset Triple,
        T ⊆ Q ∧ T.Nonempty ∧ standardTripleGeometry T ∧ tripleSeparated p T ∧
        (∀ x ∈ activeTripleClasses T 1, x ∈ lineNeighborhood w₁ L₁) ∧
        (∀ x ∈ activeTripleClasses T 2, x ∈ lineNeighborhood w₂ L₂) ∧
        (c^2*w₁^ζ*w₂^ζ/64)*(Q.card : ℝ) ≤ (T.card : ℝ) ∧
        coordinateDensity (c/256) (activeTripleClasses T) (T.image tripleVertexMap) ∧
        (∀ j, finiteFrostman p (64*K/(c^2*w₁^ζ*w₂^ζ)) (activeTripleClasses T j)) ∧
        (∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
          (((activeTripleClasses T 1).filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤
            (128/c^2)*(r/w₁)^ζ*((activeTripleClasses T 1).card : ℝ)) ∧
        (∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
          (((activeTripleClasses T 2).filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤
            (64/c)*(r/w₂)^ζ*((activeTripleClasses T 2).card : ℝ)) := by
  classical
  obtain ⟨w₁,hpw₁,hw₁1,L₁,U,hUQ,hUne,hgeomU,hsepU,hstripU,hmassU,hdenU,hFU,hnonconcU⟩ :=
    exists_two_ends_clean_graph hp hp1 hζ hζ1 hc hK Q hne hgeom hsep hdense hF
  have hw₁ : 0 < w₁ := lt_of_lt_of_le (by positivity : 0 < p/2) hpw₁
  have hw₁pow : 0 < w₁^ζ := Real.rpow_pos_of_pos hw₁ _
  have hK₁ : 0 ≤ 2*K/(c*w₁^ζ) := by positivity
  obtain ⟨w₂,hpw₂,hw₂1,L₂,T,hTU,hTne,hgeomT,hsepT,hstripT,hmassT,hdenT,hfirst,hFT,hnonconcT⟩ :=
    exists_last_two_ends_clean_graph hp hp1 hζ hζ1 (show 0 < c/16 by positivity) hK₁
      U hUne hgeomU hsepU hdenU hFU
  have hw₂ : 0 < w₂ := lt_of_lt_of_le (by positivity : 0 < p/2) hpw₂
  have hw₂pow : 0 < w₂^ζ := Real.rpow_pos_of_pos hw₂ _
  have hdenEq : (c/16)/16 = c/256 := by ring
  rw [hdenEq] at hdenT
  have hKEq : 2*(2*K/(c*w₁^ζ))/((c/16)*w₂^ζ) = 64*K/(c^2*w₁^ζ*w₂^ζ) := by
    field_simp
    <;> ring
  rw [hKEq] at hFT
  have hCEq : (4:ℝ)/(c/16) = 64/c := by field_simp; ring
  rw [hCEq] at hnonconcT
  have hC₁ : (4/c)/(c/16/2) = 128/c^2 := by field_simp; ring
  have hfirstNonconc := strip_nonconcentration_of_retained_fraction hp hw₁
    (show 0 ≤ 4/c by positivity) (show 0 < c/16/2 by positivity)
    (activeTripleClasses U 1) (activeTripleClasses T 1) (activeTripleClasses_mono hTU 1) hfirst hnonconcU
  rw [hC₁] at hfirstNonconc
  have hmass : (c^2*w₁^ζ*w₂^ζ/64)*(Q.card : ℝ) ≤ (T.card : ℝ) := by
    have hh := (mul_le_mul_of_nonneg_left hmassU
      (show 0 ≤ (c/16)*w₂^ζ/2 by positivity)).trans hmassT
    convert hh using 1 <;> ring
  refine ⟨w₁,w₂,⟨hpw₁,hw₁1⟩,⟨hpw₂,hw₂1⟩,L₁,L₂,T,hTU.trans hUQ,hTne,hgeomT,hsepT,
    ?_,hstripT,hmass,hdenT,hFT,hfirstNonconc,hnonconcT⟩
  intro x hx
  exact hstripU x (activeTripleClasses_mono hTU 1 hx)

end Kakeya4.Hard.RestrictedTriple
