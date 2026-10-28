import Kakeya4.Hard.RestrictedTriple.StripProjectionWindow

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal BigOperators Classical

namespace Kakeya4.Hard.RestrictedTriple

def fixedOuterFiber (Q : Finset Triple) (q : Triple) : Finset Plane :=
  (Q.filter (fun t ↦ t.1 = q.1 ∧ t.2.2 = q.2.2)).image (fun t ↦ t.2.1)

theorem fixedOuterFiber_subset (Q : Finset Triple) (q : Triple) :
    fixedOuterFiber Q q ⊆ activeTripleClasses Q 1 := by
  intro x hx
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨t,(Finset.mem_filter.mp ht).1,rfl⟩

theorem fixedOuterFiber_mass {c : ℝ} (Q : Finset Triple) (q : Triple) (hq : q ∈ Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    c*((activeTripleClasses Q 1).card : ℝ) ≤ ((fixedOuterFiber Q q).card : ℝ) := by
  classical
  let I : Finset (Fin 3) := {0,2}
  let R := Q.filter (fun t ↦ t.1 = q.1 ∧ t.2.2 = q.2.2)
  have hinj : Set.InjOn (fun t : Triple ↦ t.2.1) (R : Set Triple) := by
    intro t ht u hu hmid
    obtain ⟨_htQ,htfirst,htlast⟩ := Finset.mem_filter.mp ht
    obtain ⟨_huQ,hufirst,hulast⟩ := Finset.mem_filter.mp hu
    exact Prod.ext (htfirst.trans hufirst.symm) (Prod.ext hmid (htlast.trans hulast.symm))
  have hcard : (fixedOuterFiber Q q).card = R.card := Finset.card_image_of_injOn hinj
  have hfilter : (Q.image tripleVertexMap).filter (fun x ↦ ∀ j ∈ I, x j = tripleVertexMap q j) =
      R.image tripleVertexMap := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ,hxI⟩ := Finset.mem_filter.mp hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hxQ
      refine Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,?_,?_⟩,rfl⟩
      · exact hxI 0 (by simp [I])
      · exact hxI 2 (by simp [I])
    · intro hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨htQ,htfirst,htlast⟩ := Finset.mem_filter.mp ht
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,htQ,rfl⟩,?_⟩
      intro j hj
      have hj' : j = 0 ∨ j = 2 := by simpa [I] using hj
      rcases hj' with rfl | rfl
      · exact htfirst
      · exact htlast
  have hcomp : Iᶜ = {(1:Fin 3)} := by
    ext j
    fin_cases j <;> simp [I]
  have hh := hdense.2 (tripleVertexMap q) (Finset.mem_image.mpr ⟨q,hq,rfl⟩) I
  have hh' : c*((activeTripleClasses Q 1).card : ℝ) ≤ ((R.image tripleVertexMap).card : ℝ) := by
    convert hh using 1
    · simp [hcomp]
    · apply congrArg (fun S : Finset (Fin 3 → Plane) ↦ (S.card : ℝ))
      ext x
      simpa only [Finset.mem_filter] using (Finset.ext_iff.mp hfilter x).symm
  rw [Finset.card_image_of_injective _ tripleVertexMap_injective,← hcard] at hh'
  exact hh'

theorem fixedOuterFiber_dot_image_subset (Q : Finset Triple) (q : Triple) :
    ((fun x : Plane ↦ inner ℝ q.1 (x-q.2.2)) '' (fixedOuterFiber Q q : Set Plane)) ⊆
      dotDifferenceImage (Q : Set Triple) := by
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨t,ht,hmid⟩ := Finset.mem_image.mp hx
  obtain ⟨htQ,htfirst,htlast⟩ := Finset.mem_filter.mp ht
  refine ⟨t,htQ,?_⟩
  change inner ℝ t.1 (t.2.1-t.2.2) = inner ℝ q.1 (x-q.2.2)
  rw [htfirst,htlast,hmid]

/-- Actual restricted-triple image growth from an occupied fiber.
The density lower bound is derived from I={0,2}, and the image stays inside the original Q. -/
theorem occupied_fiber_strip_projection_window {p t c K : ℝ} (hp : 0 < p) (ht : 0 < t)
    (hpt : p ≤ 2*t) (hK : 0 < K) (L : AffineLine) (Q : Finset Triple) (q : Triple) (hq : q ∈ Q)
    (hgeom : standardTripleGeometry Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : finiteFrostman p K (activeTripleClasses Q 1))
    (hstrip : ∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood t L)
    (hA : 0 < |inner ℝ q.1 L.direction|) (hAt : 2*t ≤ |inner ℝ q.1 L.direction|) :
    ∃ l u : ℝ, l ≤ u ∧ u-l = 6*|inner ℝ q.1 L.direction| ∧
      ENNReal.ofReal (c*|inner ℝ q.1 L.direction|/(8*K*t)) ≤
        intervalCover (2*t) (Icc l u ∩ dotDifferenceImage (Q : Set Triple)) := by
  let E := fixedOuterFiber Q q
  have hEne : E.Nonempty := ⟨q.2.1,Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,rfl,rfl⟩,rfl⟩⟩
  have hGne : (activeTripleClasses Q 1).Nonempty := ⟨q.2.1,Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
  have hEG : E ⊆ activeTripleClasses Q 1 := fixedOuterFiber_subset Q q
  have hunit : ∀ x ∈ E, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (hEG hx)
    exact (hgeom.1 v hv).2.2.1
  obtain ⟨l,u,hlu,hlen,_hsub,hlower⟩ := strip_fiber_projection_window hp ht hpt hK L q.1 q.2.2
    (hgeom.1 q hq).2.1 hA hAt (activeTripleClasses Q 1) E hGne hEne hEG
    (fixedOuterFiber_mass Q q hq hdense) hF (fun x hx ↦ hstrip x (hEG hx)) hunit
  exact ⟨l,u,hlu,hlen,hlower.trans (intervalCover_mono
    (inter_subset_inter_right _ (fixedOuterFiber_dot_image_subset Q q)))⟩

end Kakeya4.Hard.RestrictedTriple
