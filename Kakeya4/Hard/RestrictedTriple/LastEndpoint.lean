import Kakeya4.Hard.RestrictedTriple.TwoEndsCleanGraph

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators Classical

namespace Kakeya4.Hard.RestrictedTriple

def restrictLastEndpoint (Q : Finset Triple) (P : Finset Plane) : Finset Triple :=
  Q.filter (fun t ↦ t.2.2 ∈ P)

theorem restrictLastEndpoint_subset (Q : Finset Triple) (P : Finset Plane) :
    restrictLastEndpoint Q P ⊆ Q := Finset.filter_subset _ _

theorem restrictLastEndpoint_projection (Q : Finset Triple) (P : Finset Plane)
    (hP : P ⊆ activeTripleClasses Q 2) : activeTripleClasses (restrictLastEndpoint Q P) 2 = P := by
  classical
  change (restrictLastEndpoint Q P).image (fun t ↦ t.2.2) = P
  ext x
  constructor
  · intro hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp ht).2
  · intro hx
    obtain ⟨t,ht,hxEq⟩ := Finset.mem_image.mp (hP hx)
    refine Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,?_⟩,hxEq⟩
    rwa [hxEq]

theorem restrictLastEndpoint_coordinate_image (Q : Finset Triple) (P : Finset Plane) :
    (restrictLastEndpoint Q P).image tripleVertexMap =
      restrictCoordinate (Q.image tripleVertexMap) (2:Fin 3) P := by
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

theorem restrictLastEndpoint_retains_fraction {c θ : ℝ} (hc : 0 ≤ c) (hθ : 0 ≤ θ)
    (Q : Finset Triple) (P : Finset Plane) (hP : P ⊆ activeTripleClasses Q 2)
    (hmass : θ*((activeTripleClasses Q 2).card : ℝ) ≤ P.card)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    c*θ*(Q.card : ℝ) ≤ ((restrictLastEndpoint Q P).card : ℝ) := by
  classical
  have hactive : (Q.image tripleVertexMap).image (fun x ↦ x (2:Fin 3)) = activeTripleClasses Q 2 := by
    simp only [Finset.image_image]
    rfl
  have hP' : P ⊆ (Q.image tripleVertexMap).image (fun x ↦ x (2:Fin 3)) := by rwa [hactive]
  have hh := restrictCoordinate_retains_fraction hc hθ hdense (2:Fin 3) P hP' hmass
  rw [← restrictLastEndpoint_coordinate_image,
    Finset.card_image_of_injective _ tripleVertexMap_injective,
    Finset.card_image_of_injective _ tripleVertexMap_injective] at hh
  exact hh


end Kakeya4.Hard.RestrictedTriple
