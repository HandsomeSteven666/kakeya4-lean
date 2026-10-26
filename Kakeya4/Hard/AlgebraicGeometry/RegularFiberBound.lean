import Kakeya4.Hard.AlgebraicGeometry.IsolatedFibers
import Kakeya4.Hard.Analysis.RegularSlopeFibers

/-! Parameter-uniform regular-preimage bounds from semialgebraic full fibers. -/

noncomputable section
open Set
open OAI.Release061

namespace Kakeya4.Hard

/-- The full fiber relation is semialgebraic; no semialgebraicity of derivatives
or a component-count premise is needed. The same N works for every parameter. -/
theorem uniform_regular_fiber_bound {X ι : Type*} {n : ℕ}
    {c : X → ι → ℝ} (f : X → (Fin n → ℝ) → (Fin n → ℝ))
    (D : X → Set (Fin n → ℝ)) (y : X → (Fin n → ℝ))
    (hS : PolynomialSignSet
      (fun z : X × (Fin n → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ D z.1 ∧ f z.1 z.2 = y z.1}) :
    ∃ N : ℕ, ∀ x,
      {v | v ∈ D x ∧ ContDiffAt ℝ 1 (f x) v ∧
        (fderiv ℝ (f x) v).det ≠ 0 ∧ f x v = y x}.encard ≤ N := by
  let S := {z : X × (Fin n → ℝ) | z.2 ∈ D z.1 ∧ f z.1 z.2 = y z.1}
  obtain ⟨N,hN⟩ := uniform_locally_isolated_fiber_bound hS
  refine ⟨N,fun x => hN x _ ?_⟩
  intro v hv
  refine ⟨⟨hv.1,hv.2.2.2⟩,?_⟩
  obtain ⟨U,hU,hvU,hinj⟩ := exists_open_injOn_of_regular_derivative
    (f x) (fderiv ℝ (f x) v) v hv.2.1
    (hv.2.1.differentiableAt one_ne_zero).hasFDerivAt hv.2.2.1
  exact ⟨U,hU,hvU,fun w hw hwU => hinj hwU hvU (hw.2.trans hv.2.2.2.symm)⟩

end Kakeya4.Hard
