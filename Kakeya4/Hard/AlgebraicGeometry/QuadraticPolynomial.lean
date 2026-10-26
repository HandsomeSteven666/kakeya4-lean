import Kakeya4.Hard.AlgebraicGeometry.EligibleFormula
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialLineDegree

/-! Genuine quadratic multivariate polynomials behind the eligibility formula. -/

noncomputable section
open Set Polynomial
open scoped Classical BigOperators

namespace Kakeya4.Hard.EligibleFormula

def exponent (a : QuadraticExponent) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a.val i : ℕ))

def quadraticPolynomial (p : Parameters) : MvPolynomial (Fin 4) ℝ :=
  ∑ a : QuadraticExponent, MvPolynomial.monomial (exponent a) (p (.quadratic a))

theorem quadraticPolynomial_totalDegree (p : Parameters) :
    (quadraticPolynomial p).totalDegree ≤ 2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  change (exponent a).sum (fun _ n => n) ≤ 2
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  simpa [exponent] using a.property

def lineCoordinates (b s : Point) (t : ℝ) : Fin 4 → ℝ :=
  Fin.cases t (fun j => b j + t * s j)

def linePolynomials (b s : Point) : Fin 4 → ℝ[X] :=
  Fin.cases X (fun j => C (b j) + X * C (s j))

theorem linePolynomials_degree (b s : Point) (i : Fin 4) :
    (linePolynomials b s i).natDegree ≤ 1 := by
  cases i using Fin.cases with
  | zero => simp [linePolynomials]
  | succ j =>
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · have h : (X * C (s j) : ℝ[X]).natDegree ≤
          (X : ℝ[X]).natDegree + (C (s j) : ℝ[X]).natDegree := Polynomial.natDegree_mul_le
      simpa using h

theorem derivative_on_line_degree (p : Parameters) (b s : Point) :
    ((MvPolynomial.pderiv 3 (quadraticPolynomial p)).eval₂ C (linePolynomials b s)).natDegree ≤ 1 := by
  apply (OAI.Nagata.W02.natDegree_eval₂_le_totalDegree _ _ (linePolynomials_degree b s)).trans
  by_cases hd : MvPolynomial.pderiv 3 (quadraticPolynomial p) = 0
  · simp [hd]
  · have hh := OAI.QuarticPowerFree.pderiv_totalDegree_lt 3 (quadraticPolynomial p) hd
    have hp := quadraticPolynomial_totalDegree p
    omega

theorem eval_spacetime (p : Parameters) (b s : Point) (t : ℝ) (i : Fin 4) :
    MvPolynomial.eval (timedCoordinates (((p,s),b),t)) (spacetime i) =
      lineCoordinates b s t i := by
  cases i using Fin.cases <;>
    simp [spacetime, spatial, intercept, slope, time, timedCoordinates, coordinates, lineCoordinates]

theorem eval_test_eq (p : Parameters) (b s : Point) (t : ℝ) :
    MvPolynomial.eval (timedCoordinates (((p,s),b),t)) test =
      MvPolynomial.eval (lineCoordinates b s t) (quadraticPolynomial p) := by
  simp only [test, quadraticPolynomial, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finsupp.prod_fintype _ _ (by intro; simp)]
  simp only [map_mul, map_prod, map_pow, parameter, MvPolynomial.eval_X,
    timedCoordinates, coordinates, Option.elim_some, Sum.elim_inl]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_spacetime]
  simp [exponent]

theorem eval_derivativeW_eq (p : Parameters) (b s : Point) (t : ℝ) :
    MvPolynomial.eval (timedCoordinates (((p,s),b),t)) derivativeW =
      MvPolynomial.eval (lineCoordinates b s t)
        (MvPolynomial.pderiv 3 (quadraticPolynomial p)) := by
  simp only [derivativeW, quadraticPolynomial, map_sum, MvPolynomial.pderiv_monomial,
    MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finsupp.prod_fintype _ _ (by intro; simp)]
  simp only [map_mul, map_prod, map_pow, MvPolynomial.eval_C, parameter,
    MvPolynomial.eval_X, timedCoordinates, coordinates, Option.elim_some, Sum.elim_inl]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_spacetime]
  simp [exponent, Finsupp.single_apply, eq_comm]

theorem eval_line_restriction (Q : MvPolynomial (Fin 4) ℝ) (b s : Point) (t : ℝ) :
    Polynomial.eval t (Q.eval₂ C (linePolynomials b s)) =
      MvPolynomial.eval (lineCoordinates b s t) Q := by
  change (Polynomial.evalRingHom t) (Q.eval₂ C (linePolynomials b s)) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom t).comp C = RingHom.id ℝ := by ext; simp
  rw [hc]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp [linePolynomials, lineCoordinates]
  | succ j =>
    change Polynomial.eval t (C (b j) + X * C (s j)) = b j + t * s j
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- The actual derivative test is one fixed affine function of time for each line. -/
theorem derivativeW_affine (p : Parameters) (b s : Point) :
    ∃ u v : ℝ, ∀ t : ℝ,
      MvPolynomial.eval (timedCoordinates (((p,s),b),t)) derivativeW = u*t+v := by
  let Q := (MvPolynomial.pderiv 3 (quadraticPolynomial p)).eval₂ C (linePolynomials b s)
  have hd : Q.natDegree ≤ 1 := derivative_on_line_degree p b s
  refine ⟨Q.coeff 1,Q.coeff 0,fun t => ?_⟩
  rw [eval_derivativeW_eq, ← eval_line_restriction]
  have he := OAI.Release061.SignElimination.eval_eq_sum_range_of_natDegree_le Q 1 hd t
  simpa [Finset.sum_range_succ, mul_comm, add_comm, Q] using he

end Kakeya4.Hard.EligibleFormula
