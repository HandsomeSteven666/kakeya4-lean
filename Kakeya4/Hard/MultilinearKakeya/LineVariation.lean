import Kakeya4.Hard.MultilinearKakeya.CriticalVariation
import Kakeya4.Hard.MultilinearKakeya.SmoothEnergy

/-! The degree-uniform directional variation budget on each entire affine line.
No transversality, genericity, or nonconstant-restriction hypothesis is needed. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem natDegree_eval_affine_le_totalDegree {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (g : Fin n → Polynomial ℝ) (hg : ∀ i, (g i).natDegree ≤ 1) :
    (P.eval₂ Polynomial.C g).natDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ i : Fin n, (g i ^ d i).natDegree ≤ ∑ i : Fin n, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact Polynomial.natDegree_pow_le.trans (by nlinarith [hg i])
    _ = d.sum (fun _ e => e) := by rw [Finsupp.sum_fintype]; simp
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

def linePolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (a v : E n) : Polynomial ℝ :=
  P.eval₂ Polynomial.C (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)

theorem natDegree_linePolynomial_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (a v : E n) :
    (linePolynomial P a v).natDegree ≤ P.totalDegree := by
  apply natDegree_eval_affine_le_totalDegree
  intro i
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · apply Polynomial.natDegree_mul_le.trans
    simp

theorem eval_linePolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (a v : E n) (t : ℝ) :
    (linePolynomial P a v).eval t = MvPolynomial.eval (WithLp.ofLp (a + t • v)) P := by
  change (Polynomial.evalRingHom t) (P.eval₂ Polynomial.C _) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext c
    simp
  · funext i
    change Polynomial.eval t (Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) =
      a i + t * v i
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    ring

theorem fderiv_smoothPolynomial_line_eq {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε : ℝ) (a v : E n) (t : ℝ) :
    fderiv ℝ (smoothPolynomial P ε) (a + t • v) v =
      arctanPolynomialDerivative (linePolynomial P a v) ε t := by
  have heq : (fun s : ℝ => smoothPolynomial P ε (a + s • v)) =
      (fun s => Real.arctan ((linePolynomial P a v).eval s / ε)) := by
    funext s
    rw [eval_linePolynomial]
    rfl
  exact (hasDerivAt_smoothPolynomial_line P ε a v t).unique
    (heq ▸ hasDerivAt_arctanPolynomial (linePolynomial P a v) ε t)

theorem integrable_smoothPolynomial_line {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    {ε : ℝ} (hε : ε ≠ 0) (a v : E n) :
    Integrable (fun t : ℝ => fderiv ℝ (smoothPolynomial P ε) (a + t • v) v) := by
  simp_rw [fderiv_smoothPolynomial_line_eq]
  exact integrable_arctanPolynomialDerivative _ hε

theorem integral_smoothPolynomial_line_le_degree {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    {ε : ℝ} (hε : ε ≠ 0) (a v : E n) :
    ∫ t : ℝ, ‖fderiv ℝ (smoothPolynomial P ε) (a + t • v) v‖ ≤ P.totalDegree * Real.pi := by
  simp_rw [fderiv_smoothPolynomial_line_eq]
  apply (integral_arctanPolynomialDerivative_le_degree _ hε).trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast natDegree_linePolynomial_le P a v)
    Real.pi_pos.le

theorem lintegral_smoothPolynomial_line_le_degree {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    {ε : ℝ} (hε : ε ≠ 0) (a v : E n) :
    ∫⁻ t : ℝ, ENNReal.ofReal ‖fderiv ℝ (smoothPolynomial P ε) (a + t • v) v‖ ≤
      ENNReal.ofReal (P.totalDegree * Real.pi) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_smoothPolynomial_line P hε a v).norm
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (integral_smoothPolynomial_line_le_degree P hε a v)

theorem lintegral_smoothPolynomial_parallel_family_le_degree {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] (μ : Measure Y) (P : MvPolynomial (Fin n) ℝ)
    {ε : ℝ} (hε : ε ≠ 0) (a : Y → E n) (v : E n) :
    ∫⁻ z : Y × ℝ, ENNReal.ofReal
        ‖fderiv ℝ (smoothPolynomial P ε) (a z.1 + z.2 • v) v‖ ∂μ.prod volume ≤
      μ univ * ENNReal.ofReal (P.totalDegree * Real.pi) := by
  apply (lintegral_prod_le _).trans
  calc
    _ ≤ ∫⁻ _y : Y, ENNReal.ofReal (P.totalDegree * Real.pi) ∂μ :=
      lintegral_mono (fun y => lintegral_smoothPolynomial_line_le_degree P hε (a y) v)
    _ = _ := by rw [lintegral_const]; exact mul_comm _ _

end Kakeya4.Hard.MultilinearKakeya
