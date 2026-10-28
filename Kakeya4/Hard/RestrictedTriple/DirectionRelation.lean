import Kakeya4.Hard.RestrictedTriple.EndpointFibers

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal BigOperators Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem exists_injective_direction_representatives (E Ω : Finset Plane) (f : Plane → Plane)
    (hsrc : (Ω : Set Plane) ⊆ f '' (E : Set Plane)) :
    ∃ b : Plane → Plane, (∀ θ ∈ Ω, b θ ∈ E ∧ f (b θ) = θ) ∧ Set.InjOn b (Ω : Set Plane) := by
  have hall : ∀ θ : Plane, ∃ x : Plane, θ ∈ Ω → x ∈ E ∧ f x = θ := by
    intro θ
    by_cases hθ : θ ∈ Ω
    · obtain ⟨x,hx,hfx⟩ := hsrc hθ
      exact ⟨x,fun _ ↦ ⟨hx,hfx⟩⟩
    · exact ⟨0,fun hh ↦ (hθ hh).elim⟩
  choose b hb using hall
  refine ⟨b,hb,?_⟩
  intro θ hθ φ hφ heq
  rw [← (hb θ hθ).2,← (hb φ hφ).2,heq]

def occupiedDirectionRelation (Q : Finset Triple) (b₂ : Plane) (Ω : Finset Plane)
    (b : Plane → Plane) : Finset (Plane × Plane) :=
  ((activeTripleClasses Q 0) ×ˢ Ω).filter (fun v ↦ (v.1,b v.2,b₂) ∈ Q)

theorem occupiedDirectionRelation_support (Q : Finset Triple) (b₂ : Plane) (Ω : Finset Plane)
    (b : Plane → Plane) (v : Plane × Plane) (hv : v ∈ occupiedDirectionRelation Q b₂ Ω b) :
    v.1 ∈ activeTripleClasses Q 0 ∧ v.2 ∈ Ω ∧ (v.1,b v.2,b₂) ∈ Q := by
  obtain ⟨hvprod,hvQ⟩ := Finset.mem_filter.mp hv
  exact ⟨(Finset.mem_product.mp hvprod).1,(Finset.mem_product.mp hvprod).2,hvQ⟩

theorem occupiedDirectionRelation_fiber_mass {c : ℝ} (Q : Finset Triple) (q : Triple)
    (Ω : Finset Plane) (b : Plane → Plane) (θ : Plane) (hθ : θ ∈ Ω)
    (hrep : b θ ∈ fixedOuterFiber Q q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    c*((activeTripleClasses Q 0).card : ℝ) ≤
      (((occupiedDirectionRelation Q q.2.2 Ω b).filter (fun v ↦ v.2 = θ)).card : ℝ) := by
  let X := occupiedDirectionRelation Q q.2.2 Ω b
  let R := X.filter (fun v ↦ v.2 = θ)
  have hrepr := (mem_fixedOuterFiber Q q (b θ)).mp hrep
  have hmass := fixedEndpointFiber_mass Q (q.1,b θ,q.2.2) hrepr hdense
  have hinj : Set.InjOn (Prod.fst : Plane × Plane → Plane) (R : Set (Plane × Plane)) := by
    intro x hx y hy hxy
    exact Prod.ext hxy ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  have himage : R.image Prod.fst = fixedEndpointFiber Q (b θ) q.2.2 := by
    ext a
    constructor
    · intro ha
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hvX,hvθ⟩ := Finset.mem_filter.mp hv
      have hsup := occupiedDirectionRelation_support Q q.2.2 Ω b v hvX
      apply (mem_fixedEndpointFiber Q _ _ _).mpr
      simpa only [hvθ] using hsup.2.2
    · intro ha
      have haQ := (mem_fixedEndpointFiber Q _ _ _).mp ha
      have haF := fixedEndpointFiber_subset Q (b θ) q.2.2 ha
      refine Finset.mem_image.mpr ⟨(a,θ),Finset.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haF,hθ⟩,haQ⟩
  have hcard := Finset.card_image_of_injOn hinj
  rw [himage] at hcard
  exact hmass.trans_eq (by exact_mod_cast hcard)

theorem occupiedDirectionRelation_mass {c : ℝ} (Q : Finset Triple) (q : Triple)
    (Ω : Finset Plane) (b : Plane → Plane) (hrep : ∀ θ ∈ Ω, b θ ∈ fixedOuterFiber Q q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    c*((activeTripleClasses Q 0).card : ℝ)*(Ω.card : ℝ) ≤
      ((occupiedDirectionRelation Q q.2.2 Ω b).card : ℝ) := by
  let X := occupiedDirectionRelation Q q.2.2 Ω b
  have hcount : X.card = ∑ θ ∈ Ω, (X.filter (fun v ↦ v.2 = θ)).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
      (fun v hv ↦ (occupiedDirectionRelation_support Q q.2.2 Ω b v hv).2.1)
  have hcountReal : (X.card : ℝ) = ∑ θ ∈ Ω, ((X.filter (fun v ↦ v.2 = θ)).card : ℝ) := by
    exact_mod_cast hcount
  calc
    _ = ∑ _θ ∈ Ω, c*((activeTripleClasses Q 0).card : ℝ) := by simp [mul_comm]
    _ ≤ ∑ θ ∈ Ω, ((X.filter (fun v ↦ v.2 = θ)).card : ℝ) :=
      Finset.sum_le_sum (fun θ hθ ↦ occupiedDirectionRelation_fiber_mass Q q Ω b θ hθ (hrep θ hθ) hdense)
    _ = _ := hcountReal.symm

/-- Each selected direction gets an actual endpoint witness and a genuinely dense pair relation. -/
theorem exists_actual_direction_relation {c : ℝ} (Q : Finset Triple) (q : Triple)
    (Ω : Finset Plane) (f : Plane → Plane)
    (hsrc : (Ω : Set Plane) ⊆ f '' (fixedOuterFiber Q q : Set Plane))
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    ∃ b : Plane → Plane, (∀ θ ∈ Ω, b θ ∈ fixedOuterFiber Q q ∧ f (b θ) = θ) ∧
      Set.InjOn b (Ω : Set Plane) ∧
      c*((activeTripleClasses Q 0).card : ℝ)*(Ω.card : ℝ) ≤ ((occupiedDirectionRelation Q q.2.2 Ω b).card : ℝ) ∧
      ∀ θ ∈ Ω, c*((activeTripleClasses Q 0).card : ℝ) ≤
        (((occupiedDirectionRelation Q q.2.2 Ω b).filter (fun v ↦ v.2 = θ)).card : ℝ) := by
  obtain ⟨b,hb,hinj⟩ := exists_injective_direction_representatives (fixedOuterFiber Q q) Ω f hsrc
  exact ⟨b,hb,hinj,occupiedDirectionRelation_mass Q q Ω b (fun θ hθ ↦ (hb θ hθ).1) hdense,
    fun θ hθ ↦ occupiedDirectionRelation_fiber_mass Q q Ω b θ hθ (hb θ hθ).1 hdense⟩

end Kakeya4.Hard.RestrictedTriple
