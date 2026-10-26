import Kakeya4.Hard.AlgebraicGeometry.SlopeFiberFamily

/-! One jointly definable selector, with full-measure analytic loci in every
individual parameter slice and a common regular-fiber bound for all slices. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical
open OAI.Release061 OAI.Release061.SignElimination

namespace Kakeya4.Hard

theorem vector_graph_full_measure_analytic_locus {n : ℕ}
    {S : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → (Fin n → ℝ)}
    (hS : PolynomialSignSet id S)
    (hgraph : PolynomialSignSet
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Sum.elim z.1 z.2)
      {z | z.1 ∈ S ∧ z.2 = f z.1}) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ U ⊆ S ∧
      volume (S \ U) = 0 ∧ AnalyticOnNhd ℝ f U := by
  obtain ⟨D,hD,ha⟩ := vector_graph_analytic_off_polynomial hgraph
  let U := interior S ∩ {x | MvPolynomial.eval x D ≠ 0}
  refine ⟨U,isOpen_interior.inter
    ((MvPolynomial.continuous_eval D).isOpen_preimage _ isOpen_ne),
    fun x hx => interior_subset hx.1, ?_, fun x hx => ha x (interior_subset hx.1) hx.2⟩
  apply measure_mono_null (t := (S \ interior S) ∪ {x | MvPolynomial.eval x D = 0}) _
    (measure_union_null (semialgebraic_sdiff_interior_volume hS)
      (real_polynomial_zero_volume D hD))
  intro x hx
  by_cases hi : x ∈ interior S
  · right
    by_contra hn
    exact hx.2 ⟨hi,hn⟩
  · exact Or.inl ⟨hx.1,hi⟩

/-- Specializing the numerical parameters leaves a semialgebraic graph. -/
theorem polynomialSignSet_graph_parameter_slice {P ι : Type*} {n : ℕ}
    {c : P → ι → ℝ} {b₀ : P → (Fin n → ℝ) → (Fin n → ℝ)}
    {S : P → Set (Fin n → ℝ)}
    (hgraph : PolynomialSignSet
      (fun z : (P × (Fin n → ℝ)) × (Fin n → ℝ) =>
        Sum.elim (Sum.elim (c z.1.1) z.1.2) z.2)
      {z | z.1.2 ∈ S z.1.1 ∧ z.2 = b₀ z.1.1 z.1.2}) (p : P) :
    PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Sum.elim z.1 z.2)
      {z | z.1 ∈ S p ∧ z.2 = b₀ p z.1} := by
  exact hgraph.polynomial_preimage
    (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ((p,z.1),z.2))
    (Sum.elim (Sum.elim (fun i => MvPolynomial.C (c p i))
      (fun j => MvPolynomial.X (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr j)))
    (by intro z i; cases i with | inl i => cases i <;> simp | inr i => simp)

/-- A common selector graph is used for both the slice regularity and the
uniform count. No joint exceptional polynomial is assumed nonzero on a slice. -/
theorem semialgebraic_selector_family {P ι : Type*} {n : ℕ}
    {c : P → ι → ℝ} {A : Set ((P × (Fin n → ℝ)) × (Fin n → ℝ))}
    (hA : PolynomialSignSet
      (fun z : (P × (Fin n → ℝ)) × (Fin n → ℝ) =>
        Sum.elim (Sum.elim (c z.1.1) z.1.2) z.2) A) :
    ∃ b₀ : P → (Fin n → ℝ) → (Fin n → ℝ), ∃ N : ℕ,
      (∀ p s, (∃ v, ((p,s),v) ∈ A) → ((p,s),b₀ p s) ∈ A) ∧
      PolynomialSignSet
        (fun z : (P × (Fin n → ℝ)) × (Fin n → ℝ) =>
          Sum.elim (Sum.elim (c z.1.1) z.1.2) z.2)
        {z | (∃ v, ((z.1.1,z.1.2),v) ∈ A) ∧ z.2 = b₀ z.1.1 z.1.2} ∧
      (∀ p, ∃ U : Set (Fin n → ℝ), IsOpen U ∧
        U ⊆ {s | ∃ v, ((p,s),v) ∈ A} ∧
        volume ({s | ∃ v, ((p,s),v) ∈ A} \ U) = 0 ∧ AnalyticOnNhd ℝ (b₀ p) U) ∧
      ∀ p t y,
        {s | (∃ v, ((p,s),v) ∈ A) ∧ ContDiffAt ℝ 1 (slopeMap (b₀ p) t) s ∧
          (fderiv ℝ (slopeMap (b₀ p) t) s).det ≠ 0 ∧ slopeMap (b₀ p) t s = y}.encard ≤ N := by
  obtain ⟨f,hf,hgraph⟩ := polynomialSignSet_choice_finite
    (c := fun z : P × (Fin n → ℝ) => Sum.elim (c z.1) z.2) hA
  let b₀ := fun p s => f (p,s)
  let S := fun p => {s | ∃ v, ((p,s),v) ∈ A}
  have hg : PolynomialSignSet
      (fun z : (P × (Fin n → ℝ)) × (Fin n → ℝ) =>
        Sum.elim (Sum.elim (c z.1.1) z.1.2) z.2)
      {z | z.1.2 ∈ S z.1.1 ∧ z.2 = b₀ z.1.1 z.1.2} := hgraph
  obtain ⟨N,hN⟩ := uniform_regular_slope_fiber_family_bound b₀ S hg
  refine ⟨b₀,N,fun p s hs => hf (p,s) hs,hg,fun p => ?_,hN⟩
  have hs := polynomialSignSet_graph_parameter_slice hg p
  have hSp : PolynomialSignSet id (S p) := by
    have hh := polynomialSignSet_projection_finite (c := id) hs
    convert hh using 1
    ext s
    simp only [mem_ofPred_eq]
    exact ⟨fun h => ⟨b₀ p s,h,rfl⟩, fun ⟨_,h,_⟩ => h⟩
  exact vector_graph_full_measure_analytic_locus hSp hs

end Kakeya4.Hard
