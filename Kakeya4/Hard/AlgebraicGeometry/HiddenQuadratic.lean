import Kakeya4.Hard.AlgebraicGeometry.AllowedRegion
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialCoordinateRay

/-! The actual spatial test is quadratic in w, and its polynomial derivative is P_w. -/

noncomputable section
open Set Polynomial
open scoped Classical BigOperators
open OAI.StrongThinTree.MSS

namespace Kakeya4.Hard.EligibleFormula

def hiddenBase (t : ℝ) (y : Fin 2 → ℝ) : Fin 4 → ℝ := Fin.cases t (Fin.snoc y 0)
def hiddenPolynomial (p : Parameters) (t : ℝ) (y : Fin 2 → ℝ) : ℝ[X] :=
  ray (quadraticPolynomial p) (hiddenBase t y) 3

theorem hiddenPolynomial_degree (p : Parameters) (t : ℝ) (y : Fin 2 → ℝ) :
    (hiddenPolynomial p t y).natDegree ≤ 2 := by
  apply (OAI.Nagata.W02.natDegree_eval₂_le_totalDegree _ _ ?_).trans (quadraticPolynomial_totalDegree p)
  intro i
  by_cases hi : i = 3
  · simp only [hi,ite_true]
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    simp
  · simp [hi]

theorem hiddenBase_update (t : ℝ) (y : Fin 2 → ℝ) (w : ℝ) :
    Function.update (hiddenBase t y) 3 (hiddenBase t y 3 + w) =
      Fin.cases t (Fin.snoc y w) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    rw [Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3)]
    simp only [hiddenBase,Fin.cases_zero]
  | succ i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change Function.update (hiddenBase t y) 3 (hiddenBase t y 3 + w) 3 = _
      rw [Function.update_self]
      change (Fin.snoc y 0 : Point) (Fin.last 2) + w = (Fin.snoc y w : Point) (Fin.last 2)
      simp only [Fin.snoc_last,zero_add]
    · have hi : j.castSucc.succ ≠ (3 : Fin 4) := by
        intro h
        have hv := congrArg Fin.val h
        have hj := j.isLt
        change j.val + 1 = 3 at hv
        omega
      rw [Function.update_of_ne hi]
      simp only [hiddenBase,Fin.cases_succ,Fin.snoc_castSucc]

theorem hiddenPolynomial_eval (p : Parameters) (t : ℝ) (y : Fin 2 → ℝ) (w : ℝ) :
    (hiddenPolynomial p t y).eval w = testValue p t (Fin.snoc y w) := by
  rw [hiddenPolynomial,ray_eval,hiddenBase_update]
  rfl

theorem hiddenPolynomial_derivative_eval (p : Parameters) (t : ℝ) (y : Fin 2 → ℝ) (w : ℝ) :
    (hiddenPolynomial p t y).derivative.eval w = spatialDerivativeValue p t (Fin.snoc y w) := by
  rw [hiddenPolynomial,ray_derivative,ray_eval,hiddenBase_update]
  rfl

theorem hiddenPolynomial_eval_quadratic (p : Parameters) (t : ℝ) (y : Fin 2 → ℝ) (w : ℝ) :
    testValue p t (Fin.snoc y w) = (hiddenPolynomial p t y).coeff 2 * w^2 +
      (hiddenPolynomial p t y).coeff 1 * w + (hiddenPolynomial p t y).coeff 0 := by
  rw [← hiddenPolynomial_eval]
  have he := OAI.Release061.SignElimination.eval_eq_sum_range_of_natDegree_le
    (hiddenPolynomial p t y) 2 (hiddenPolynomial_degree p t y) w
  simpa [Finset.sum_range_succ,add_comm,add_left_comm,add_assoc] using he

theorem hiddenPolynomial_derivative_affine (p : Parameters) (t : ℝ) (y : Fin 2 → ℝ) (w : ℝ) :
    spatialDerivativeValue p t (Fin.snoc y w) =
      2 * (hiddenPolynomial p t y).coeff 2 * w + (hiddenPolynomial p t y).coeff 1 := by
  rw [← hiddenPolynomial_derivative_eval]
  have hd : (hiddenPolynomial p t y).derivative.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_derivative_le _).trans
    have hh := hiddenPolynomial_degree p t y
    omega
  have he := OAI.Release061.SignElimination.eval_eq_sum_range_of_natDegree_le
    (hiddenPolynomial p t y).derivative 1 hd w
  norm_num [Finset.sum_range_succ,Polynomial.coeff_derivative] at he
  rw [he]
  ring

end Kakeya4.Hard.EligibleFormula
