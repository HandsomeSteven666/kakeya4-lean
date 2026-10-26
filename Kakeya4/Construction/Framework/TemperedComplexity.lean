import Kakeya4.Construction.Framework.ExactSequence
import Kakeya4.Construction.Framework.SemialgebraicTests

/-!
# Polynomial complexity along an exact sequence

This file promotes finite-scale semialgebraic density certificates to families indexed by the
resolution parameter. Polynomial bounds use one coefficient and exponent for all sequence
indices. This is independent of the subpower and subsequence semantics delegated to F-001.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- A natural-valued complexity function is polynomially bounded along one exact sequence when
one coefficient and exponent work at every resolution index. -/
structure PolynomiallyBoundedNatAlong (seq : ExactSequence) (f : ℕ → ℕ) where
  coefficient : ℕ
  exponent : ℕ
  bound : ∀ n, (f n : ℝ) ≤ (coefficient : ℝ) * seq.resolution n ^ exponent

namespace PolynomiallyBoundedNatAlong

variable {seq : ExactSequence} {f g : ℕ → ℕ}

/-- Pointwise weakening preserves a polynomial complexity bound. -/
def of_le (hf : PolynomiallyBoundedNatAlong seq g) (hfg : ∀ n, f n ≤ g n) :
    PolynomiallyBoundedNatAlong seq f where
  coefficient := hf.coefficient
  exponent := hf.exponent
  bound n := by
    have hfgReal : (f n : ℝ) ≤ (g n : ℝ) := by exact_mod_cast hfg n
    exact hfgReal.trans (hf.bound n)

/-- The product of two polynomially bounded natural complexity functions is polynomially
bounded, with multiplied coefficients and added exponents. -/
def mul (hf : PolynomiallyBoundedNatAlong seq f)
    (hg : PolynomiallyBoundedNatAlong seq g) :
    PolynomiallyBoundedNatAlong seq (fun n => f n * g n) where
  coefficient := hf.coefficient * hg.coefficient
  exponent := hf.exponent + hg.exponent
  bound n := by
    have hR : 1 ≤ seq.resolution n := seq.resolution_ge_one n
    have hRnonneg : 0 ≤ seq.resolution n := le_trans zero_le_one hR
    calc
      ((f n * g n : ℕ) : ℝ) = (f n : ℝ) * (g n : ℝ) := by norm_num
      _ ≤ ((hf.coefficient : ℝ) * seq.resolution n ^ hf.exponent) *
          ((hg.coefficient : ℝ) * seq.resolution n ^ hg.exponent) := by
        apply mul_le_mul (hf.bound n) (hg.bound n)
        · positivity
        · positivity
      _ = ((hf.coefficient * hg.coefficient : ℕ) : ℝ) *
          seq.resolution n ^ (hf.exponent + hg.exponent) := by
        rw [pow_add]
        push_cast
        ring

end PolynomiallyBoundedNatAlong

/-- A family of real ENNReal bounds is polynomially controlled along an exact sequence. The
coefficient is nonnegative and therefore every displayed real bound is finite. -/
structure PolynomiallyBoundedENNRealAlong (seq : ExactSequence) (f : ℕ → ℝ≥0∞) where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  exponent : ℕ
  bound : ∀ n, f n ≤ ENNReal.ofReal
    (coefficient * seq.resolution n ^ exponent)

/-- A sequence of finite-scale semialgebraic prior certificates with polynomially many pieces,
polynomially many polynomial atoms across all pieces, uniformly bounded variable count and
individual degree, and polynomially bounded density. This implements only these clauses of
`a01:tempered`; other world/chart/label/coordinate/Jacobian fields remain separate. -/
structure TemperedSemialgebraicPriorFamily
    {varCount : ℕ} [MeasurableSpace (Fin varCount → ℝ)] [BorelSpace (Fin varCount → ℝ)]
    (seq : ExactSequence)
    (reference prior : ℕ → Measure (Fin varCount → ℝ))
    (pieceBound atomBound : ℕ → ℕ) (densityBound : ℕ → ℝ≥0∞)
    (variableBound degreeBound : ℕ) where
  pieceBound_polynomial : PolynomiallyBoundedNatAlong seq pieceBound
  atomBound_polynomial : PolynomiallyBoundedNatAlong seq atomBound
  densityBound_polynomial : PolynomiallyBoundedENNRealAlong seq densityBound
  certificate : ∀ n, SemialgebraicPiecewiseDensityCertificate
    (reference n) (prior n) (pieceBound n) variableBound (atomBound n) degreeBound
    (densityBound n)

namespace TemperedSemialgebraicPriorFamily

variable {varCount : ℕ} [MeasurableSpace (Fin varCount → ℝ)] [BorelSpace (Fin varCount → ℝ)]
  {seq : ExactSequence} {reference prior : ℕ → Measure (Fin varCount → ℝ)}
  {pieceBound atomBound : ℕ → ℕ} {densityBound : ℕ → ℝ≥0∞}
  {variableBound degreeBound : ℕ}

/-- The total number of polynomial atom occurrences across all semialgebraic density pieces. -/
def totalAtomCount (C : TemperedSemialgebraicPriorFamily seq reference prior
    pieceBound atomBound densityBound variableBound degreeBound) (n : ℕ) : ℕ :=
  ∑ i : Fin (C.certificate n).pieceCount,
    ((C.certificate n).pieces i).atomCount

/-- The sum of all atom occurrences is bounded by the product of the piece and per-piece atom
bounds. -/
theorem totalAtomCount_le_capacity
    (C : TemperedSemialgebraicPriorFamily seq reference prior
      pieceBound atomBound densityBound variableBound degreeBound) (n : ℕ) :
    C.totalAtomCount n ≤ pieceBound n * atomBound n := by
  unfold totalAtomCount
  calc
    _ ≤ ∑ _i : Fin (C.certificate n).pieceCount, atomBound n := by
      apply Finset.sum_le_sum
      intro i hi
      exact (C.certificate n).atoms_per_piece_le i
    _ = (C.certificate n).pieceCount * atomBound n := by simp
    _ ≤ pieceBound n * atomBound n :=
      Nat.mul_le_mul_right (atomBound n) (C.certificate n).pieceCount_le

/-- Every density value in the family is bounded by the same sequence-polynomial envelope. -/
theorem density_le_polynomial_envelope
    (C : TemperedSemialgebraicPriorFamily seq reference prior
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) (x : Fin varCount → ℝ) :
    (C.certificate n).density x ≤ ENNReal.ofReal
      (C.densityBound_polynomial.coefficient *
        seq.resolution n ^ C.densityBound_polynomial.exponent) := by
  exact ((C.certificate n).density_le_bound x).trans
    (C.densityBound_polynomial.bound n)

/-- Consequently the total number of polynomial conditions over all pieces has a single
polynomial bound along the exact sequence. -/
def totalAtomCount_polynomiallyBounded
    (C : TemperedSemialgebraicPriorFamily seq reference prior
      pieceBound atomBound densityBound variableBound degreeBound) :
    PolynomiallyBoundedNatAlong seq C.totalAtomCount := by
  exact PolynomiallyBoundedNatAlong.of_le
    (PolynomiallyBoundedNatAlong.mul C.pieceBound_polynomial C.atomBound_polynomial)
    C.totalAtomCount_le_capacity

end TemperedSemialgebraicPriorFamily

end Kakeya4.Framework
