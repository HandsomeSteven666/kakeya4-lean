import Kakeya4.Hard.Analysis.BoundedMultiplicity
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Jacobian polynomial of the selected line family

For `F_t(s) = b(s) + t • s`, the derivative is `Db(s) + t • id`.
Its determinant, as a polynomial in `t`, is the characteristic polynomial of `-Db(s)`.
Thus monicity and exact degree follow from Mathlib, without an entrywise determinant expansion.
This is the analytic/algebraic interface at manuscript `a01:monic-jacobian`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Polynomial
open scoped ENNReal

namespace Kakeya4.Hard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The spatial position at time `t` of the line with selected intercept `b(s)`. -/
def slopeMap (b : E → E) (t : ℝ) (s : E) : E := b s + t • s

/-- The derivative of the selected-line position with respect to the slope. -/
def slopeDerivative (Db : E → E →L[ℝ] E) (t : ℝ) (s : E) : E →L[ℝ] E :=
  Db s + t • ContinuousLinearMap.id ℝ E

/-- The monic Jacobian polynomial of the affine perturbation `A + t • id`. -/
def jacobianPolynomial (A : E →L[ℝ] E) : ℝ[X] := (-A.toLinearMap).charpoly

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_slopeMap {b : E → E} {Db : E → E →L[ℝ] E}
    {s : E} (hb : HasFDerivAt b (Db s) s) (t : ℝ) :
    HasFDerivAt (slopeMap b t) (slopeDerivative Db t s) s := by
  exact hb.add ((hasFDerivAt_id s).const_smul t)

omit [FiniteDimensional ℝ E] in
theorem contDiffAt_slopeMap {b : E → E} {s : E}
    (hb : ContDiffAt ℝ 1 b s) (t : ℝ) : ContDiffAt ℝ 1 (slopeMap b t) s :=
  hb.add (contDiffAt_id.const_smul t)

theorem jacobianPolynomial_monic (A : E →L[ℝ] E) : (jacobianPolynomial A).Monic :=
  LinearMap.charpoly_monic _

theorem jacobianPolynomial_natDegree (A : E →L[ℝ] E) :
    (jacobianPolynomial A).natDegree = Module.finrank ℝ E :=
  LinearMap.charpoly_natDegree _

theorem eval_jacobianPolynomial (A : E →L[ℝ] E) (t : ℝ) :
    (jacobianPolynomial A).eval t = (A + t • ContinuousLinearMap.id ℝ E).det := by
  rw [jacobianPolynomial, LinearMap.eval_charpoly]
  congr 1
  ext x
  simp [Algebra.algebraMap_eq_smul_one, add_comm]

/-- The manuscript's monic-Jacobian identity. -/
theorem det_slopeDerivative (Db : E → E →L[ℝ] E) (t : ℝ) (s : E) :
    (slopeDerivative Db t s).det = (jacobianPolynomial (Db s)).eval t :=
  (eval_jacobianPolynomial (Db s) t).symm

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The bounded-multiplicity volume comparison specialized to the actual line-position map.
The regular-fiber bound is explicit and still has to come from the semialgebraic argument. -/
theorem slope_volume_le_of_jacobian_lower (μ : Measure E) [IsAddHaarMeasure μ]
    (b : E → E) (Db : E → E →L[ℝ] E) (t : ℝ)
    (S T : Set E) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hbC : ∀ s ∈ S, ContDiffAt ℝ 1 b s)
    (hbD : ∀ s ∈ S, HasFDerivAt b (Db s) s)
    (hdet : ∀ s ∈ S, (jacobianPolynomial (Db s)).eval t ≠ 0)
    (N : ℕ) (a : ℝ≥0∞) (hmap : MapsTo (slopeMap b t) S T)
    (hfiber : ∀ y, {s ∈ S | slopeMap b t s = y}.encard ≤ N)
    (hlower : ∀ s ∈ S, a ≤ ENNReal.ofReal |(jacobianPolynomial (Db s)).eval t|) :
    a * μ S ≤ (N : ℝ≥0∞) * μ T := by
  exact mul_measure_le_of_regular_fibers μ (slopeMap b t) (slopeDerivative Db t) S hS
    (fun s hs => contDiffAt_slopeMap (hbC s hs) t)
    (fun s hs => hasFDerivAt_slopeMap (hbD s hs) t)
    (fun s hs => by simpa only [det_slopeDerivative] using hdet s hs)
    T hT N a hmap hfiber (by simpa only [det_slopeDerivative] using hlower)

end Kakeya4.Hard
