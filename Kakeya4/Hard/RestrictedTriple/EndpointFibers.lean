import Kakeya4.Hard.RestrictedTriple.RescaledAngularInput

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal Classical

namespace Kakeya4.Hard.RestrictedTriple

def fixedEndpointFiber (Q : Finset Triple) (b₁ b₂ : Plane) : Finset Plane :=
  (Q.filter (fun t ↦ t.2.1 = b₁ ∧ t.2.2 = b₂)).image Prod.fst

theorem mem_fixedEndpointFiber (Q : Finset Triple) (a b₁ b₂ : Plane) :
    a ∈ fixedEndpointFiber Q b₁ b₂ ↔ (a,b₁,b₂) ∈ Q := by
  constructor
  · intro ha
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨htQ,ht₁,ht₂⟩ := Finset.mem_filter.mp ht
    have hid : (t.1,b₁,b₂) = t := by rw [← ht₁,← ht₂]
    rwa [hid]
  · intro ht
    exact Finset.mem_image.mpr ⟨(a,b₁,b₂),Finset.mem_filter.mpr ⟨ht,rfl,rfl⟩,rfl⟩

theorem fixedEndpointFiber_subset (Q : Finset Triple) (b₁ b₂ : Plane) :
    fixedEndpointFiber Q b₁ b₂ ⊆ activeTripleClasses Q 0 := by
  intro a ha
  exact Finset.mem_image.mpr ⟨(a,b₁,b₂),(mem_fixedEndpointFiber Q a b₁ b₂).mp ha,rfl⟩

theorem mem_fixedOuterFiber (Q : Finset Triple) (q : Triple) (x : Plane) :
    x ∈ fixedOuterFiber Q q ↔ (q.1,x,q.2.2) ∈ Q := by
  constructor
  · intro hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨htQ,ht₁,ht₂⟩ := Finset.mem_filter.mp ht
    have hid : (q.1,t.2.1,q.2.2) = t := by rw [← ht₁,← ht₂]
    rwa [hid]
  · intro ht
    exact Finset.mem_image.mpr ⟨(q.1,x,q.2.2),Finset.mem_filter.mpr ⟨ht,rfl,rfl⟩,rfl⟩

/-- Every occupied endpoint pair supports a large actual first-coordinate fiber. -/
theorem fixedEndpointFiber_mass {c : ℝ} (Q : Finset Triple) (q : Triple) (hq : q ∈ Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    c*((activeTripleClasses Q 0).card : ℝ) ≤ ((fixedEndpointFiber Q q.2.1 q.2.2).card : ℝ) := by
  let I : Finset (Fin 3) := {1,2}
  let R := Q.filter (fun t ↦ t.2.1 = q.2.1 ∧ t.2.2 = q.2.2)
  have hinj : Set.InjOn (Prod.fst : Triple → Plane) (R : Set Triple) := by
    intro t ht u hu hfirst
    obtain ⟨_htQ,ht₁,ht₂⟩ := Finset.mem_filter.mp ht
    obtain ⟨_huQ,hu₁,hu₂⟩ := Finset.mem_filter.mp hu
    exact Prod.ext hfirst (Prod.ext (ht₁.trans hu₁.symm) (ht₂.trans hu₂.symm))
  have hcard : (fixedEndpointFiber Q q.2.1 q.2.2).card = R.card := Finset.card_image_of_injOn hinj
  have hfilter : (Q.image tripleVertexMap).filter (fun x ↦ ∀ j ∈ I, x j = tripleVertexMap q j) =
      R.image tripleVertexMap := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ,hxI⟩ := Finset.mem_filter.mp hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hxQ
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr
        ⟨ht,hxI 1 (by simp [I]),hxI 2 (by simp [I])⟩,rfl⟩
    · intro hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨htQ,ht₁,ht₂⟩ := Finset.mem_filter.mp ht
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,htQ,rfl⟩,?_⟩
      intro j hj
      have hj' : j = 1 ∨ j = 2 := by simpa [I] using hj
      rcases hj' with rfl | rfl
      · exact ht₁
      · exact ht₂
  have hcomp : Iᶜ = {(0:Fin 3)} := by ext j; fin_cases j <;> simp [I]
  have hh := hdense.2 (tripleVertexMap q) (Finset.mem_image.mpr ⟨q,hq,rfl⟩) I
  have hh' : c*((activeTripleClasses Q 0).card : ℝ) ≤ ((R.image tripleVertexMap).card : ℝ) := by
    convert hh using 1
    · simp [hcomp]
    · apply congrArg (fun S : Finset (Fin 3 → Plane) ↦ (S.card : ℝ))
      ext x
      simpa only [Finset.mem_filter] using (Finset.ext_iff.mp hfilter x).symm
  rw [Finset.card_image_of_injective _ tripleVertexMap_injective,← hcard] at hh'
  exact hh'

end Kakeya4.Hard.RestrictedTriple
