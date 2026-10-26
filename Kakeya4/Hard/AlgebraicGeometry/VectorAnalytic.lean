import Kakeya4.Hard.AlgebraicGeometry.Imported.SemialgebraicAnalytic
import Kakeya4.Hard.AlgebraicGeometry.Imported.VectorGraphCoordinate
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetChoice2

/-! Analytic regularity and definable selection for finite-dimensional real graphs. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology Classical BigOperators
open OAI.Release061 OAI.Release061.SignElimination

namespace Kakeya4.Hard

/-- A semialgebraic vector graph is analytic away from one nonzero polynomial. -/
theorem vector_graph_analytic_off_polynomial {n : ℕ} {κ : Type*} [Fintype κ]
    {B : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → κ → ℝ}
    (hf : PolynomialSignSet
      (fun z : (Fin n → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      {z | z.1 ∈ B ∧ z.2 = f z.1}) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ x ∈ B, MvPolynomial.eval x D ≠ 0 → AnalyticAt ℝ f x := by
  have hi (i : κ) : ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ x ∈ B, MvPolynomial.eval x D ≠ 0 → AnalyticAt ℝ (fun x => f x i) x := by
    have hp := polynomialSignSet_vector_graph_coordinate (c := id) (S := B) (f := f) hf i
    have hs := hp.coordinate_preimage
      (fun x : Option (Fin n) → ℝ => ((fun j => x (some j)),x none))
      id (d := id) (by intro x j; cases j <;> rfl)
    exact semialgebraic_function_analytic_off_polynomial B (fun x => f x i) hs
  choose D hD ha using hi
  refine ⟨∏ i, D i, Finset.prod_ne_zero_iff.mpr (fun i _ => hD i), ?_⟩
  intro x hx hprod
  apply analyticAt_pi_iff.mpr
  intro i
  apply ha i x hx
  intro hz
  apply hprod
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

/-- Select from every nonempty fiber of a semialgebraic relation, with analytic
regularity outside one algebraic exceptional set in the parameter domain. -/
theorem semialgebraic_analytic_selector {n : ℕ} {κ : Type*} [Fintype κ]
    {A : Set ((Fin n → ℝ) × (κ → ℝ))}
    (hA : PolynomialSignSet
      (fun z : (Fin n → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2) A) :
    ∃ f : (Fin n → ℝ) → κ → ℝ, ∃ D : MvPolynomial (Fin n) ℝ,
      D ≠ 0 ∧
      (∀ x, (∃ y, (x,y) ∈ A) → (x,f x) ∈ A) ∧
      PolynomialSignSet
        (fun z : (Fin n → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
        {z | (∃ y, (z.1,y) ∈ A) ∧ z.2 = f z.1} ∧
      ∀ x, (∃ y, (x,y) ∈ A) → MvPolynomial.eval x D ≠ 0 → AnalyticAt ℝ f x := by
  obtain ⟨f,hf,hgraph⟩ := polynomialSignSet_choice_finite (c := id) hA
  obtain ⟨D,hD,ha⟩ := vector_graph_analytic_off_polynomial
    (B := {x | ∃ y, (x,y) ∈ A}) (f := f) hgraph
  exact ⟨f,D,hD,hf,hgraph,ha⟩

end Kakeya4.Hard
