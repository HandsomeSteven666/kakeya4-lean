import Kakeya4.Hard.AlgebraicGeometry.Imported.AnalyticZeroNull
import Kakeya4.Hard.AlgebraicGeometry.VectorAnalytic

/-! Polynomial exceptional sets and full-measure analytic selector domains. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical
open OAI.Release061

namespace Kakeya4.Hard

/-- The exceptional hypersurface of a nonzero real polynomial is null. -/
theorem real_polynomial_zero_volume {n : ℕ} (D : MvPolynomial (Fin n) ℝ)
    (hD : D ≠ 0) : volume {x : Fin n → ℝ | MvPolynomial.eval x D = 0} = 0 := by
  have hex : ∃ x : Fin n → ℝ, MvPolynomial.eval x D ≠ 0 := by
    by_contra! hz
    apply hD
    apply MvPolynomial.funext
    intro x
    simpa using hz x
  obtain ⟨x,hx⟩ := hex
  simpa only [mem_univ, true_and] using analytic_zero_null volume isOpen_univ
    isPreconnected_univ (AnalyticOnNhd.eval_mvPolynomial D) (mem_univ x) hx

/-- A semialgebraic vector graph on an open domain has an open analytic locus
whose complement in that domain has measure zero. -/
theorem vector_graph_open_analytic_locus {n : ℕ} {κ : Type*} [Fintype κ]
    {B : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → κ → ℝ} (hB : IsOpen B)
    (hf : PolynomialSignSet
      (fun z : (Fin n → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      {z | z.1 ∈ B ∧ z.2 = f z.1}) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ U ⊆ B ∧
      volume (B \ U) = 0 ∧ AnalyticOnNhd ℝ f U := by
  obtain ⟨D,hD,ha⟩ := vector_graph_analytic_off_polynomial hf
  let U := B ∩ {x | MvPolynomial.eval x D ≠ 0}
  refine ⟨U, hB.inter ((MvPolynomial.continuous_eval D).isOpen_preimage _ isOpen_ne),
    inter_subset_left, ?_, fun x hx => ha x hx.1 hx.2⟩
  apply measure_mono_null (t := {x | MvPolynomial.eval x D = 0}) _
    (real_polynomial_zero_volume D hD)
  intro x hx
  by_contra hn
  exact hx.2 ⟨hx.1,hn⟩

/-- The non-interior part of a semialgebraic set is null, including sets that
are not measurable in advance. -/
theorem semialgebraic_sdiff_interior_volume {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : PolynomialSignSet id S) : volume (S \ interior S) = 0 := by
  obtain ⟨P,hP,hfront⟩ := hS.frontier_polynomial continuous_id
  apply measure_mono_null (t := {x | MvPolynomial.eval x P = 0}) _
    (real_polynomial_zero_volume P hP)
  intro x hx
  exact hfront x ⟨subset_closure hx.1,hx.2⟩

/-- Definable selection is analytic on an open subset covering almost every
point of the projection, even when the original projection is not open. -/
theorem semialgebraic_selector_open_full_measure {n : ℕ} {κ : Type*} [Fintype κ]
    {A : Set ((Fin n → ℝ) × (κ → ℝ))}
    (hA : PolynomialSignSet
      (fun z : (Fin n → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2) A) :
    ∃ f : (Fin n → ℝ) → κ → ℝ, ∃ U : Set (Fin n → ℝ),
      IsOpen U ∧ U ⊆ {x | ∃ y, (x,y) ∈ A} ∧
      volume ({x | ∃ y, (x,y) ∈ A} \ U) = 0 ∧ AnalyticOnNhd ℝ f U ∧
      (∀ x, (∃ y, (x,y) ∈ A) → (x,f x) ∈ A) ∧
      PolynomialSignSet
        (fun z : (Fin n → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
        {z | (∃ y, (z.1,y) ∈ A) ∧ z.2 = f z.1} := by
  obtain ⟨f,D,hD,hf,hgraph,ha⟩ := semialgebraic_analytic_selector hA
  let S := {x | ∃ y, (x,y) ∈ A}
  have hS : PolynomialSignSet id S :=
    OAI.Release061.SignElimination.polynomialSignSet_projection_finite (c := id) hA
  let U := interior S ∩ {x | MvPolynomial.eval x D ≠ 0}
  refine ⟨f,U,isOpen_interior.inter
    ((MvPolynomial.continuous_eval D).isOpen_preimage _ isOpen_ne),
    fun x hx => interior_subset hx.1, ?_,
    fun x hx => ha x (show x ∈ S from interior_subset hx.1) hx.2, hf,hgraph⟩
  apply measure_mono_null (t := (S \ interior S) ∪ {x | MvPolynomial.eval x D = 0}) _
    (measure_union_null (semialgebraic_sdiff_interior_volume hS)
      (real_polynomial_zero_volume D hD))
  intro x hx
  by_cases hi : x ∈ interior S
  · right
    by_contra hn
    exact hx.2 ⟨hi,hn⟩
  · exact Or.inl ⟨hx.1,hi⟩

end Kakeya4.Hard
