import Kakeya4.Hard.RestrictedTriple.CoordinateRestriction

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Classical

namespace Kakeya4.Hard.RestrictedTriple

def restrictFirstEndpoint (Q : Finset Triple) (P : Finset Plane) : Finset Triple :=
  Q.filter (fun t ↦ t.2.1 ∈ P)

theorem restrictFirstEndpoint_subset (Q : Finset Triple) (P : Finset Plane) :
    restrictFirstEndpoint Q P ⊆ Q := Finset.filter_subset _ _

theorem restrictFirstEndpoint_projection (Q : Finset Triple) (P : Finset Plane)
    (hP : P ⊆ activeTripleClasses Q 1) : activeTripleClasses (restrictFirstEndpoint Q P) 1 = P := by
  classical
  change (restrictFirstEndpoint Q P).image (fun t ↦ t.2.1) = P
  ext x
  constructor
  · intro hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp ht).2
  · intro hx
    obtain ⟨t,ht,hxEq⟩ := Finset.mem_image.mp (hP hx)
    refine Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,?_⟩,hxEq⟩
    rwa [hxEq]

theorem restrictFirstEndpoint_coordinate_image (Q : Finset Triple) (P : Finset Plane) :
    (restrictFirstEndpoint Q P).image tripleVertexMap =
      restrictCoordinate (Q.image tripleVertexMap) (1:Fin 3) P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨htQ,htP⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,htQ,rfl⟩,htP⟩
  · intro hx
    obtain ⟨hxQ,hxP⟩ := Finset.mem_filter.mp hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hxQ
    exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,hxP⟩,rfl⟩

theorem restrictFirstEndpoint_retains_fraction {c θ : ℝ} (hc : 0 ≤ c) (hθ : 0 ≤ θ)
    (Q : Finset Triple) (P : Finset Plane) (hP : P ⊆ activeTripleClasses Q 1)
    (hmass : θ*((activeTripleClasses Q 1).card : ℝ) ≤ P.card)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    c*θ*(Q.card : ℝ) ≤ ((restrictFirstEndpoint Q P).card : ℝ) := by
  classical
  have hactive : (Q.image tripleVertexMap).image (fun x ↦ x (1:Fin 3)) = activeTripleClasses Q 1 := by
    simp only [Finset.image_image]
    rfl
  have hP' : P ⊆ (Q.image tripleVertexMap).image (fun x ↦ x (1:Fin 3)) := by rwa [hactive]
  have hh := restrictCoordinate_retains_fraction hc hθ hdense (1:Fin 3) P hP' hmass
  rw [← restrictFirstEndpoint_coordinate_image,
    Finset.card_image_of_injective _ tripleVertexMap_injective,
    Finset.card_image_of_injective _ tripleVertexMap_injective] at hh
  exact hh

/-- The selected endpoint strip is restricted back to actual original graph edges.
All selected vertices are retained, the graph is nonempty, and fiber density pays the edge loss.
No unchanged density is claimed for this new graph. -/
theorem exists_two_ends_graph {p ζ c K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hc : 0 < c) (hK : 0 ≤ K)
    (Q : Finset Triple) (hne : Q.Nonempty) (hgeom : standardTripleGeometry Q)
    (hsep : tripleSeparated p Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : finiteFrostman p K (activeTripleClasses Q 1)) :
    ∃ w : ℝ, p/2 ≤ w ∧ w ≤ 1 ∧ ∃ L : AffineLine, ∃ T : Finset Triple,
      T ⊆ Q ∧ T.Nonempty ∧ standardTripleGeometry T ∧ tripleSeparated p T ∧
      activeTripleClasses T 1 = (activeTripleClasses Q 1).filter (fun x ↦ x ∈ lineNeighborhood w L) ∧
      c*w^ζ*(Q.card : ℝ) ≤ (T.card : ℝ) ∧
      finiteFrostman p (K/w^ζ) (activeTripleClasses T 1) ∧
      ∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
        (((activeTripleClasses T 1).filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤
          2*(r/w)^ζ*((activeTripleClasses T 1).card : ℝ) := by
  classical
  have hEne : (activeTripleClasses Q 1).Nonempty := by
    obtain ⟨t,ht⟩ := hne
    exact ⟨t.2.1,Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩
  have hunit : ∀ x ∈ activeTripleClasses Q 1, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    exact (hgeom.1 t ht).2.2.1
  obtain ⟨w,hpw,hw1,L,P,hP,hPne,hmass,hfrost,hnonconc⟩ :=
    exists_two_ends_frostman_strip hp hp1 hζ hζ1 hK (activeTripleClasses Q 1) hEne hunit hF
  have hPE : P ⊆ activeTripleClasses Q 1 := by rw [hP]; exact Finset.filter_subset _ _
  let T := restrictFirstEndpoint Q P
  have hTQ : T ⊆ Q := restrictFirstEndpoint_subset Q P
  have hproj : activeTripleClasses T 1 = P := restrictFirstEndpoint_projection Q P hPE
  have hTne : T.Nonempty := by
    obtain ⟨x,hx⟩ := hPne
    obtain ⟨t,ht,_⟩ := Finset.mem_image.mp (show x ∈ activeTripleClasses T 1 by rwa [hproj])
    exact ⟨t,ht⟩
  refine ⟨w,hpw,hw1,L,T,hTQ,hTne,standardTripleGeometry_mono hTQ hgeom,
    tripleSeparated_mono hTQ hsep,?_,?_,?_,?_⟩
  · rw [hproj,hP]
  · exact restrictFirstEndpoint_retains_fraction hc.le (Real.rpow_nonneg (by linarith) _) Q P hPE hmass hdense
  · rwa [hproj]
  · rwa [hproj]

end Kakeya4.Hard.RestrictedTriple
