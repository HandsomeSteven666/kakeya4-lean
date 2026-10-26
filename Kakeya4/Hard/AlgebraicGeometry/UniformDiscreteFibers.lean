import Kakeya4.Hard.AlgebraicGeometry.DiscreteProjection
import Kakeya4.Hard.AlgebraicGeometry.UniformLineFibers

/-! A uniform cardinal bound for discrete fibers of one fixed semialgebraic family. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology Classical BigOperators
open OAI.Release061 OAI.Release061.SignElimination

namespace Kakeya4.Hard

/-- The bound precedes every parameter value. All numerical coefficients may be
included in `c`; only the fixed polynomial sign formula controls the bound. -/
theorem uniform_discrete_fiber_bound {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} {S : Set (X × (κ → ℝ))}
    (hS : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) S) :
    ∃ N : ℕ, ∀ x,
      (∀ v, (x,v) ∈ S → ∃ U : Set (κ → ℝ), IsOpen U ∧ v ∈ U ∧
        ∀ w, (x,w) ∈ S → w ∈ U → w = v) →
      {v | (x,v) ∈ S}.encard ≤ N := by
  have hproj (j : κ) : PolynomialSignSet
      (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | ∃ v, (z.1,v) ∈ S ∧ v j = z.2} := by
    let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
    have hs := hS.coordinate_preimage
      (fun z : (X × ℝ) × (κ → ℝ) => (z.1.1,z.2))
      (Sum.elim (fun i => Sum.inl (some i)) Sum.inr)
      (d := fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (d z.1) z.2)
      (by intro z i; cases i <;> rfl)
    have he : PolynomialSignSet
        (fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (d z.1) z.2)
        {z | z.2 j = z.1.2} := by
      convert PolynomialSignSet.zero
        (c := fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (d z.1) z.2)
        (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inl none)) using 1
      ext z
      simp [d, sub_eq_zero]
    exact polynomialSignSet_projection_finite (hs.inter he)
  choose N hN using fun j => uniform_line_fiber_bound (hproj j)
  refine ⟨∏ j, N j, fun x hdiscrete => ?_⟩
  have hxS : PolynomialSignSet id {v | (x,v) ∈ S} := by
    exact hS.polynomial_preimage (fun v => (x,v))
      (Sum.elim (fun i => MvPolynomial.C (c x i)) MvPolynomial.X)
      (by intro v i; cases i <;> simp)
  have hex (j : κ) : ∃ F : Finset ℝ, F.card ≤ N j ∧
      {t : ℝ | ∃ v, (x,v) ∈ S ∧ v j = t} ⊆ F := by
    exact hN j x
      (discrete_semialgebraic_scalar_projection_empty_interior hxS hdiscrete j)
  choose F hcard hcover using hex
  calc
    {v | (x,v) ∈ S}.encard ≤ (Set.pi univ (fun j => (F j : Set ℝ))).encard := by
      apply Set.encard_mono
      intro v hv j _
      exact hcover j ⟨v,hv,rfl⟩
    _ = ∏ j, (F j : Set ℝ).encard := Set.encard_pi_eq_prod_encard
    _ ≤ ∏ j, (N j : ℕ∞) := Finset.prod_le_prod (fun j _ => by
      simpa only [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] using hcard j)
    _ = (∏ j, N j : ℕ) := by simp

end Kakeya4.Hard
