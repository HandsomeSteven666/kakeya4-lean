import Kakeya4.Hard.RestrictedTriple.LastRestrictionReclean

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem exists_last_two_ends_clean_graph {p ζ c K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hc : 0 < c) (hK : 0 ≤ K)
    (Q : Finset Triple) (hne : Q.Nonempty) (hgeom : standardTripleGeometry Q)
    (hsep : tripleSeparated p Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : ∀ j, finiteFrostman p K (activeTripleClasses Q j)) :
    ∃ w : ℝ, p/2 ≤ w ∧ w ≤ 1 ∧ ∃ L : AffineLine, ∃ U : Finset Triple,
      U ⊆ Q ∧ U.Nonempty ∧ standardTripleGeometry U ∧ tripleSeparated p U ∧
      (∀ x ∈ activeTripleClasses U 2, x ∈ lineNeighborhood w L) ∧
      (c*w^ζ/2)*(Q.card : ℝ) ≤ (U.card : ℝ) ∧
      coordinateDensity (c/16) (activeTripleClasses U) (U.image tripleVertexMap) ∧
      (c/2)*((activeTripleClasses Q 1).card : ℝ) ≤ ((activeTripleClasses U 1).card : ℝ) ∧
      (∀ j, finiteFrostman p (2*K/(c*w^ζ)) (activeTripleClasses U j)) ∧
      ∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
        (((activeTripleClasses U 2).filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤
          (4/c)*(r/w)^ζ*((activeTripleClasses U 2).card : ℝ) := by
  classical
  have hEne : (activeTripleClasses Q 2).Nonempty := by
    obtain ⟨t,ht⟩ := hne
    exact ⟨t.2.2,Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩
  have hunit : ∀ x ∈ activeTripleClasses Q 2, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    exact (hgeom.1 t ht).2.2.2
  obtain ⟨w,hpw,hw1,L,P,hP,hPne,hmass,hfrost,hnonconc⟩ :=
    exists_two_ends_frostman_strip hp hp1 hζ hζ1 hK (activeTripleClasses Q 2) hEne hunit (hF 2)
  have hw : 0 < w := lt_of_lt_of_le (by positivity : 0 < p/2) hpw
  have hwpow : 0 < w^ζ := Real.rpow_pos_of_pos hw _
  have hwpow1 : w^ζ ≤ 1 := Real.rpow_le_one hw.le hw1 hζ
  have hPE : P ⊆ activeTripleClasses Q 2 := by rw [hP]; exact Finset.filter_subset _ _
  obtain ⟨U,hUT,hUne,hret,hden,hmarg,hsub⟩ := exists_recleaned_last_endpoint_restriction hc Q hne P hPne hPE hdense
  have hUQ : U ⊆ Q := hUT.trans (restrictLastEndpoint_subset Q P)
  let B := threeClasses (activeTripleClasses Q 0) (activeTripleClasses Q 1) P
  have hKle : K ≤ K/w^ζ := (le_div_iff₀ hwpow).mpr (by nlinarith)
  have hBF : ∀ j, finiteFrostman p (K/w^ζ) (B j) := by
    intro j
    fin_cases j
    · exact finiteFrostman_mono hp.le hKle (hF 0)
    · exact finiteFrostman_mono hp.le hKle (hF 1)
    · exact hfrost
  have hUF : ∀ j, finiteFrostman p (2*K/(c*w^ζ)) (activeTripleClasses U j) := by
    intro j
    have hh := finiteFrostman_of_retained_fraction hp.le (show 0 ≤ K/w^ζ by positivity)
      (show 0 < c/2 by positivity) (B j) (activeTripleClasses U j) (hsub j) (hmarg j) (hBF j)
    have heq : (K/w^ζ)/(c/2) = 2*K/(c*w^ζ) := by field_simp
    rwa [heq] at hh
  have hmassU : (c*w^ζ/2)*(Q.card : ℝ) ≤ (U.card : ℝ) := by
    have hh := restrictLastEndpoint_retains_fraction hc.le hwpow.le Q P hPE hmass hdense
    nlinarith
  have hnonconcU := strip_nonconcentration_of_retained_fraction hp hw (by norm_num : (0:ℝ) ≤ 2)
    (show 0 < c/2 by positivity) P (activeTripleClasses U 2) (hsub 2) (hmarg 2) hnonconc
  have heq : (2:ℝ)/(c/2) = 4/c := by field_simp; ring
  rw [heq] at hnonconcU
  refine ⟨w,hpw,hw1,L,U,hUQ,hUne,standardTripleGeometry_mono hUQ hgeom,
    tripleSeparated_mono hUQ hsep,?_,hmassU,hden,hmarg 1,hUF,hnonconcU⟩
  intro x hx
  have hxP := hsub 2 hx
  rw [hP] at hxP
  exact (Finset.mem_filter.mp hxP).2

end Kakeya4.Hard.RestrictedTriple
