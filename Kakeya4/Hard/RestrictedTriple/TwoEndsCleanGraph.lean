import Kakeya4.Hard.RestrictedTriple.RestrictionReclean

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem strip_nonconcentration_of_retained_fraction {p w ζ C θ : ℝ}
    (hp : 0 < p) (hw : 0 < w) (hC : 0 ≤ C) (hθ : 0 < θ)
    (E P : Finset Plane) (hPE : P ⊆ E) (hmass : θ*(E.card : ℝ) ≤ P.card)
    (h : ∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
      ((E.filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤ C*(r/w)^ζ*(E.card : ℝ)) :
    ∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
      ((P.filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤ (C/θ)*(r/w)^ζ*(P.card : ℝ) := by
  have hcard : (E.card : ℝ) ≤ (P.card : ℝ)/θ := (le_div_iff₀ hθ).mpr (by nlinarith)
  intro r hpr M
  have hr : 0 < r := hp.trans_le hpr
  have hcount : ((P.filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤
      (E.filter (fun x ↦ x ∈ lineNeighborhood r M)).card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hPE)
  calc
    _ ≤ _ := hcount
    _ ≤ C*(r/w)^ζ*(E.card : ℝ) := h r hpr M
    _ ≤ C*(r/w)^ζ*((P.card : ℝ)/θ) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = _ := by ring

/-- Actual two-ends graph after restriction and recleaning, with all statistical losses paid.
All three marginals retain normalized Frostman; the selected endpoint retains its strip bound. -/
theorem exists_two_ends_clean_graph {p ζ c K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hc : 0 < c) (hK : 0 ≤ K)
    (Q : Finset Triple) (hne : Q.Nonempty) (hgeom : standardTripleGeometry Q)
    (hsep : tripleSeparated p Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : ∀ j, finiteFrostman p K (activeTripleClasses Q j)) :
    ∃ w : ℝ, p/2 ≤ w ∧ w ≤ 1 ∧ ∃ L : AffineLine, ∃ U : Finset Triple,
      U ⊆ Q ∧ U.Nonempty ∧ standardTripleGeometry U ∧ tripleSeparated p U ∧
      (∀ x ∈ activeTripleClasses U 1, x ∈ lineNeighborhood w L) ∧
      (c*w^ζ/2)*(Q.card : ℝ) ≤ (U.card : ℝ) ∧
      coordinateDensity (c/16) (activeTripleClasses U) (U.image tripleVertexMap) ∧
      (∀ j, finiteFrostman p (2*K/(c*w^ζ)) (activeTripleClasses U j)) ∧
      ∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
        (((activeTripleClasses U 1).filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤
          (4/c)*(r/w)^ζ*((activeTripleClasses U 1).card : ℝ) := by
  classical
  have hEne : (activeTripleClasses Q 1).Nonempty := by
    obtain ⟨t,ht⟩ := hne
    exact ⟨t.2.1,Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩
  have hunit : ∀ x ∈ activeTripleClasses Q 1, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    exact (hgeom.1 t ht).2.2.1
  obtain ⟨w,hpw,hw1,L,P,hP,hPne,hmass,hfrost,hnonconc⟩ :=
    exists_two_ends_frostman_strip hp hp1 hζ hζ1 hK (activeTripleClasses Q 1) hEne hunit (hF 1)
  have hw : 0 < w := lt_of_lt_of_le (by positivity : 0 < p/2) hpw
  have hwpow : 0 < w^ζ := Real.rpow_pos_of_pos hw _
  have hwpow1 : w^ζ ≤ 1 := Real.rpow_le_one hw.le hw1 hζ
  have hPE : P ⊆ activeTripleClasses Q 1 := by rw [hP]; exact Finset.filter_subset _ _
  obtain ⟨U,hUT,hUne,hret,hden,hmarg,hsub⟩ := exists_recleaned_endpoint_restriction hc Q hne P hPne hPE hdense
  have hUQ : U ⊆ Q := hUT.trans (restrictFirstEndpoint_subset Q P)
  let B := threeClasses (activeTripleClasses Q 0) P (activeTripleClasses Q 2)
  have hKle : K ≤ K/w^ζ := (le_div_iff₀ hwpow).mpr (by nlinarith)
  have hBF : ∀ j, finiteFrostman p (K/w^ζ) (B j) := by
    intro j
    fin_cases j
    · exact finiteFrostman_mono hp.le hKle (hF 0)
    · exact hfrost
    · exact finiteFrostman_mono hp.le hKle (hF 2)
  have hUF : ∀ j, finiteFrostman p (2*K/(c*w^ζ)) (activeTripleClasses U j) := by
    intro j
    have hh := finiteFrostman_of_retained_fraction hp.le (show 0 ≤ K/w^ζ by positivity)
      (show 0 < c/2 by positivity) (B j) (activeTripleClasses U j) (hsub j) (hmarg j) (hBF j)
    have heq : (K/w^ζ)/(c/2) = 2*K/(c*w^ζ) := by field_simp
    rwa [heq] at hh
  have hmassU : (c*w^ζ/2)*(Q.card : ℝ) ≤ (U.card : ℝ) := by
    have hh := restrictFirstEndpoint_retains_fraction hc.le hwpow.le Q P hPE hmass hdense
    nlinarith
  have hnonconcU := strip_nonconcentration_of_retained_fraction hp hw (by norm_num : (0:ℝ) ≤ 2)
    (show 0 < c/2 by positivity) P (activeTripleClasses U 1) (hsub 1) (hmarg 1) hnonconc
  have heq : (2:ℝ)/(c/2) = 4/c := by field_simp; ring
  rw [heq] at hnonconcU
  refine ⟨w,hpw,hw1,L,U,hUQ,hUne,standardTripleGeometry_mono hUQ hgeom,
    tripleSeparated_mono hUQ hsep,?_,hmassU,hden,hUF,hnonconcU⟩
  intro x hx
  have hxP := hsub 1 hx
  rw [hP] at hxP
  exact (Finset.mem_filter.mp hxP).2

end Kakeya4.Hard.RestrictedTriple
