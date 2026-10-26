import Kakeya4.Hard.AlgebraicGeometry.Imported.AlgebraicGraphPolynomial
import Kakeya4.Hard.AlgebraicGeometry.Imported.RegularSimpleSheet
import Kakeya4.Hard.AlgebraicGeometry.Imported.SeparableSpecialization

/-!
SPDX-License-Identifier: Apache-2.0
Extracted unchanged from OpenAI math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/Analysis/SymmetricDomains/GenericAlgebraicRamificationUniform.lean.
Changes: retain only the scalar analytic-off-polynomial theorem and its imports.
-/

noncomputable section
namespace OAI.Release061
open Polynomial Set Filter Topology
open scoped nonZeroDivisors

theorem semialgebraic_function_analytic_off_polynomial {n : ℕ}
    (B : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin n) → ℝ |
        (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ a ∈ B, MvPolynomial.eval a D ≠ 0 → AnalyticAt ℝ f a := by
  obtain ⟨p,hp,hpr⟩ := semialgebraic_graph_polynomial B f hgraph
  let P := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  have hP : P ≠ 0 := (MvPolynomial.optionEquivLeft ℝ (Fin n)).injective.ne hp
  obtain ⟨q,hq,hqs,D₀,hD₀,hqe⟩ :=
    squarefree_relation_off_denominator (K := FractionRing (MvPolynomial (Fin n) ℝ)) P hP
  have hres : q.resultant q.derivative ≠ 0 :=
    resultant_derivative_ne_zero_of_generic_separable q hqs
  obtain ⟨D₁,hD₁,hreg⟩ := hgraph.regular_on_simple_sheet q
  refine ⟨D₀*D₁*q.leadingCoeff*(q.resultant q.derivative),
    mul_ne_zero (mul_ne_zero (mul_ne_zero hD₀ hD₁)
      (Polynomial.leadingCoeff_ne_zero.mpr hq)) hres,?_⟩
  intro a ha hD
  have hD₀a : MvPolynomial.eval a D₀ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,zero_mul]
  have hD₁a : MvPolynomial.eval a D₁ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hl : MvPolynomial.eval a q.leadingCoeff ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hd : MvPolynomial.eval a (q.resultant q.derivative) ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero]
  have hpr' : P.eval₂ (MvPolynomial.eval a) (f a) = 0 := by
    simpa only [MvPolynomial.optionEquivLeft_elim_eval,eval_map,P] using hpr a ha
  have hqr : q.eval₂ (MvPolynomial.eval a) (f a) = 0 :=
    (hqe (MvPolynomial.eval a) hD₀a (f a)).mp hpr'
  have hsep := separable_map_of_leading_resultant_ne_zero q (MvPolynomial.eval a) hl hd
  have hder : q.derivative.eval₂ (MvPolynomial.eval a) (f a) ≠ 0 := by
    have hh := Polynomial.Separable.eval₂_derivative_ne_zero (RingHom.id ℝ) hsep
      (x := f a) (by simpa only [Polynomial.eval₂_id,Polynomial.eval_map] using hqr)
    simpa only [Polynomial.eval₂_id,Polynomial.derivative_map,Polynomial.eval_map] using hh
  obtain ⟨g,hga,hgf,hgr,_⟩ := real_polynomial_analytic_root q a (f a) hqr hder
  have hder' : q.derivative.eval₂ (MvPolynomial.eval a) (g a) ≠ 0 := by
    simpa only [hgf] using hder
  rcases hreg g a hga.continuousAt hgr hder' hD₁a with hyes | hno
  · have he : g =ᶠ[𝓝 a] f := by
      filter_upwards [hyes] with y hy
      exact hy.2
    exact hga.congr he
  · have hn := hno.self_of_nhds
    exact (hn ⟨ha,hgf⟩).elim


end OAI.Release061

