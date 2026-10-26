import Kakeya4.Hard.AlgebraicGeometry.RegularFiberBound

/-! Joint semialgebraicity of selected-line fibers, including chart parameters,
time, and target among the parameters to be bounded uniformly. -/

noncomputable section
open Set
open scoped Classical
open OAI.Release061 OAI.Release061.SignElimination

namespace Kakeya4.Hard

/-- The selected intercept graph yields the full slope fiber relation. -/
theorem polynomialSignSet_slope_fiber_family {P ι : Type*} {n : ℕ}
    {c : P → ι → ℝ} (b₀ : P → (Fin n → ℝ) → (Fin n → ℝ))
    (S : P → Set (Fin n → ℝ))
    (hgraph : PolynomialSignSet
      (fun z : (P × (Fin n → ℝ)) × (Fin n → ℝ) =>
        Sum.elim (Sum.elim (c z.1.1) z.1.2) z.2)
      {z | z.1.2 ∈ S z.1.1 ∧ z.2 = b₀ z.1.1 z.1.2}) :
    PolynomialSignSet
      (fun z : (P × (ℝ × (Fin n → ℝ))) × (Fin n → ℝ) =>
        Sum.elim (Sum.elim (c z.1.1) (fun o => Option.elim o z.1.2.1 z.1.2.2)) z.2)
      {z | z.2 ∈ S z.1.1 ∧ slopeMap (b₀ z.1.1) z.1.2.1 z.2 = z.1.2.2} := by
  let d := fun z : P × (ℝ × (Fin n → ℝ)) =>
    Sum.elim (c z.1) (fun o => Option.elim o z.2.1 z.2.2)
  let e := fun z : (P × (ℝ × (Fin n → ℝ))) × (Fin n → ℝ) => Sum.elim (d z.1) z.2
  let a := fun z : ((P × (ℝ × (Fin n → ℝ))) × (Fin n → ℝ)) × (Fin n → ℝ) =>
    Sum.elim (e z.1) z.2
  have hg : PolynomialSignSet a
      {z | z.1.2 ∈ S z.1.1.1 ∧ z.2 = b₀ z.1.1.1 z.1.2} :=
    hgraph.coordinate_preimage
      (fun z : ((P × (ℝ × (Fin n → ℝ))) × (Fin n → ℝ)) × (Fin n → ℝ) =>
        ((z.1.1.1,z.1.2),z.2))
      (Sum.elim (Sum.elim (fun i => Sum.inl (Sum.inl (Sum.inl i)))
        (fun j => Sum.inl (Sum.inr j))) Sum.inr)
      (by intro z i; cases i with | inl i => cases i <;> rfl | inr i => rfl)
  have he : PolynomialSignSet a
      {z | ∀ j, z.2 j + z.1.1.2.1 * z.1.2 j = z.1.1.2.2 j} := by
    apply PolynomialSignSet.forall_finite
    intro j
    convert PolynomialSignSet.zero (c := a)
      (MvPolynomial.X (Sum.inr j) +
        MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr none))) *
          MvPolynomial.X (Sum.inl (Sum.inr j)) -
        MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (some j))))) using 1
    ext z
    simp [a,e,d,sub_eq_zero]
  have hp := polynomialSignSet_projection_finite (hg.inter he)
  convert hp using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨hs,hm⟩
    refine ⟨b₀ z.1.1 z.2,⟨hs,rfl⟩,?_⟩
    intro j
    exact congrFun hm j
  · rintro ⟨v,⟨hs,rfl⟩,hm⟩
    exact ⟨hs,funext hm⟩

/-- One bound works simultaneously for chart coefficients, all times, and all targets. -/
theorem uniform_regular_slope_fiber_family_bound {P ι : Type*} {n : ℕ}
    {c : P → ι → ℝ} (b₀ : P → (Fin n → ℝ) → (Fin n → ℝ))
    (S : P → Set (Fin n → ℝ))
    (hgraph : PolynomialSignSet
      (fun z : (P × (Fin n → ℝ)) × (Fin n → ℝ) =>
        Sum.elim (Sum.elim (c z.1.1) z.1.2) z.2)
      {z | z.1.2 ∈ S z.1.1 ∧ z.2 = b₀ z.1.1 z.1.2}) :
    ∃ N : ℕ, ∀ p t y,
      {s | s ∈ S p ∧ ContDiffAt ℝ 1 (slopeMap (b₀ p) t) s ∧
        (fderiv ℝ (slopeMap (b₀ p) t) s).det ≠ 0 ∧ slopeMap (b₀ p) t s = y}.encard ≤ N := by
  obtain ⟨N,hN⟩ := uniform_regular_fiber_bound
    (c := fun z : P × (ℝ × (Fin n → ℝ)) =>
      Sum.elim (c z.1) (fun o => Option.elim o z.2.1 z.2.2))
    (fun z => slopeMap (b₀ z.1) z.2.1) (fun z => S z.1) (fun z => z.2.2)
    (polynomialSignSet_slope_fiber_family b₀ S hgraph)
  exact ⟨N,fun p t y => hN (p,t,y)⟩

end Kakeya4.Hard
