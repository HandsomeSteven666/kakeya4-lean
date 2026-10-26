import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Set.Card

/-!
# Isolated regular preimages and connected components

The semialgebraic argument bounds connected components of full fibers. Local inversion
makes every regular preimage isolated in that fiber. The lemmas here justify the intervening
cardinality comparison, without assuming a semialgebraic component bound itself.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace Kakeya4.Hard

variable {X : Type*} [TopologicalSpace X] [T1Space X]

/-- Isolated points are distinct connected components in a T₁ space. -/
theorem injOn_connectedComponents_of_isolated (R : Set X)
    (hR : ∀ x ∈ R, IsOpen ({x} : Set X)) :
    InjOn (ConnectedComponents.mk : X → ConnectedComponents X) R := by
  intro x hx y _hy hxy
  have hcl : IsClopen ({x} : Set X) := ⟨isClosed_singleton, hR x hx⟩
  have hy : y ∈ connectedComponent x := ConnectedComponents.coe_eq_coe'.mp hxy.symm
  exact (hcl.connectedComponent_subset (by simp) hy).symm

/-- The number of isolated points cannot exceed the number of connected components. -/
theorem encard_isolated_le_components (R : Set X)
    (hR : ∀ x ∈ R, IsOpen ({x} : Set X)) :
    R.encard ≤ ENat.card (ConnectedComponents X) := by
  calc
    R.encard ≤ (univ : Set (ConnectedComponents X)).encard :=
      Set.encard_le_encard_of_injOn (fun _ _ => mem_univ _)
        (injOn_connectedComponents_of_isolated R hR)
    _ = ENat.card (ConnectedComponents X) := encard_univ _

omit [T1Space X] in
/-- A locally injective point of a fiber is isolated in the topology of the full fiber. -/
theorem isOpen_singleton_in_fiber {Y : Type*} (f : X → Y) (S : Set X) (y : Y)
    (x : {z ∈ S | f z = y})
    (hlocal : ∃ U : Set X, IsOpen U ∧ (x : X) ∈ U ∧ InjOn f (S ∩ U)) :
    IsOpen ({x} : Set {z ∈ S | f z = y}) := by
  obtain ⟨U, hU, hxU, hinj⟩ := hlocal
  have heq : (Subtype.val ⁻¹' U : Set {z ∈ S | f z = y}) = {x} := by
    ext z
    constructor
    · intro hz
      apply Subtype.ext
      exact hinj ⟨z.property.1, hz⟩ ⟨x.property.1, hxU⟩
        (z.property.2.trans x.property.2.symm)
    · rintro rfl
      exact hxU
  rw [← heq]
  exact hU.preimage continuous_subtype_val

/-- The exact bridge from a component bound on the full fiber to a bound on its
regular preimages. The regular predicate is arbitrary; local inversion supplies `hlocal`. -/
theorem encard_regular_fiber_le_components {Y : Type*} (f : X → Y) (S : Set X)
    (regular : X → Prop) (y : Y)
    (hlocal : ∀ x ∈ S, regular x →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f (S ∩ U)) :
    {x ∈ S | regular x ∧ f x = y}.encard ≤
      ENat.card (ConnectedComponents {x ∈ S | f x = y}) := by
  let F := {x ∈ S | f x = y}
  let R : Set X := {x ∈ S | regular x ∧ f x = y}
  let R' : Set F := {x | regular x}
  let e : R ≃ R' :=
    { toFun := fun x => ⟨⟨x.val, x.property.1, x.property.2.2⟩, x.property.2.1⟩
      invFun := fun x => ⟨x.val.val, x.val.property.1, x.property, x.val.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    R.encard = R'.encard := ENat.card_congr e
    _ ≤ ENat.card (ConnectedComponents F) := encard_isolated_le_components R' (by
      intro x hx
      exact isOpen_singleton_in_fiber f S y x (hlocal x x.property.1 hx))

/-- Uniform component bounds imply the uniform regular-fiber bound needed by the
analytic selector-volume theorem. -/
theorem encard_regular_fiber_le_of_components_bound {Y : Type*} (f : X → Y) (S : Set X)
    (regular : X → Prop) (N : ℕ)
    (hlocal : ∀ x ∈ S, regular x →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f (S ∩ U))
    (hcomponents : ∀ y, ENat.card (ConnectedComponents {x ∈ S | f x = y}) ≤ N) :
    ∀ y, {x ∈ S | regular x ∧ f x = y}.encard ≤ N := by
  intro y
  exact (encard_regular_fiber_le_components f S regular y hlocal).trans (hcomponents y)

end Kakeya4.Hard
