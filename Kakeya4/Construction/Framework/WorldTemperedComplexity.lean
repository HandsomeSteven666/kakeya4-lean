import Kakeya4.Construction.Framework.TemperedComplexity

/-!
# Finite world-indexed tempered semialgebraic prior certificates

Each world carries its own reference measure, prior, finite-scale complexity profiles, and
piecewise-density certificate. The certificate and the shared polynomial envelopes are caller
data; this file proves the resulting finite atom-count aggregation statements.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- A finite family of world-indexed semialgebraic prior certificates along one exact sequence.
The reference/prior measures, their exact density certificates, and the pointwise profiles are
provided for every world. The polynomial envelopes are uniform over all worlds. -/
structure WorldTemperedSemialgebraicPriorFamily
    {varCount : ℕ} [MeasurableSpace (Fin varCount → ℝ)] [BorelSpace (Fin varCount → ℝ)]
    (seq : ExactSequence)
    (worldCount : ℕ → ℕ)
    (reference prior : ∀ n, Fin (worldCount n) → Measure (Fin varCount → ℝ))
    (pieceBound atomBound : ∀ n, Fin (worldCount n) → ℕ)
    (densityBound : ∀ n, Fin (worldCount n) → ℝ≥0∞)
    (variableBound degreeBound : ℕ) where
  pieceEnvelope : ℕ → ℕ
  pieceEnvelope_polynomial : PolynomiallyBoundedNatAlong seq pieceEnvelope
  pieceBound_le_envelope : ∀ n γ, pieceBound n γ ≤ pieceEnvelope n
  atomEnvelope : ℕ → ℕ
  atomEnvelope_polynomial : PolynomiallyBoundedNatAlong seq atomEnvelope
  atomBound_le_envelope : ∀ n γ, atomBound n γ ≤ atomEnvelope n
  densityEnvelope : ℕ → ℝ≥0∞
  densityEnvelope_polynomial : PolynomiallyBoundedENNRealAlong seq densityEnvelope
  densityBound_le_envelope : ∀ n γ, densityBound n γ ≤ densityEnvelope n
  worldCount_polynomial : PolynomiallyBoundedNatAlong seq worldCount
  certificate : ∀ n γ, SemialgebraicPiecewiseDensityCertificate
    (reference n γ) (prior n γ) (pieceBound n γ) variableBound (atomBound n γ)
    degreeBound (densityBound n γ)

namespace WorldTemperedSemialgebraicPriorFamily

variable {varCount : ℕ} [MeasurableSpace (Fin varCount → ℝ)] [BorelSpace (Fin varCount → ℝ)]
  {seq : ExactSequence} {worldCount : ℕ → ℕ}
  {reference prior : ∀ n, Fin (worldCount n) → Measure (Fin varCount → ℝ)}
  {pieceBound atomBound : ∀ n, Fin (worldCount n) → ℕ}
  {densityBound : ∀ n, Fin (worldCount n) → ℝ≥0∞}
  {variableBound degreeBound : ℕ}

variable (C : WorldTemperedSemialgebraicPriorFamily seq worldCount reference prior
  pieceBound atomBound densityBound variableBound degreeBound)

/-- The number of atom occurrences in one world's actual certificate. -/
def totalAtomCount (n : ℕ) (γ : Fin (worldCount n)) : ℕ :=
  ∑ i : Fin (C.certificate n γ).pieceCount, ((C.certificate n γ).pieces i).atomCount

/-- The sum of actual atom occurrences over the finite set of world tags. -/
def worldTaggedTotalAtomCount (n : ℕ) : ℕ :=
  ∑ γ : Fin (worldCount n), C.totalAtomCount n γ

/-- A single world's atom count is bounded by its piece capacity times its per-piece atom
capacity. -/
theorem totalAtomCount_le_capacity (n : ℕ) (γ : Fin (worldCount n)) :
    C.totalAtomCount n γ ≤ pieceBound n γ * atomBound n γ := by
  unfold totalAtomCount
  calc
    _ ≤ ∑ _i : Fin (C.certificate n γ).pieceCount, atomBound n γ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (C.certificate n γ).atoms_per_piece_le i
    _ = (C.certificate n γ).pieceCount * atomBound n γ := by simp
    _ ≤ pieceBound n γ * atomBound n γ :=
      Nat.mul_le_mul_right _ (C.certificate n γ).pieceCount_le

/-- Summing over worlds gives the product of the world count and the shared piece/atom
envelopes. This theorem only counts atoms in the caller-supplied certificates. -/
theorem worldTaggedTotalAtomCount_le_envelopes (n : ℕ) :
    C.worldTaggedTotalAtomCount n ≤
      worldCount n * C.pieceEnvelope n * C.atomEnvelope n := by
  unfold worldTaggedTotalAtomCount
  calc
    _ ≤ ∑ γ : Fin (worldCount n), pieceBound n γ * atomBound n γ := by
      apply Finset.sum_le_sum
      intro γ hγ
      exact C.totalAtomCount_le_capacity n γ
    _ ≤ ∑ _γ : Fin (worldCount n), C.pieceEnvelope n * C.atomEnvelope n := by
      apply Finset.sum_le_sum
      intro γ hγ
      exact Nat.mul_le_mul (C.pieceBound_le_envelope n γ) (C.atomBound_le_envelope n γ)
    _ = worldCount n * C.pieceEnvelope n * C.atomEnvelope n := by simp [Nat.mul_assoc]

/-- The total world-tagged atom count has one polynomial envelope, with coefficient product
and exponent sum supplied by the three uniform envelopes. -/
noncomputable def worldTaggedTotalAtomCount_polynomiallyBounded :
    PolynomiallyBoundedNatAlong seq C.worldTaggedTotalAtomCount :=
  PolynomiallyBoundedNatAlong.of_le
    (PolynomiallyBoundedNatAlong.mul
      (PolynomiallyBoundedNatAlong.mul C.worldCount_polynomial C.pieceEnvelope_polynomial)
      C.atomEnvelope_polynomial)
    C.worldTaggedTotalAtomCount_le_envelopes

/-- Every per-world density bound inherits the shared polynomial envelope. This is a separate
statement from the atom-count aggregation theorem. -/
theorem density_le_polynomial_envelope
    (n : ℕ) (γ : Fin (worldCount n)) (x : Fin varCount → ℝ) :
    (C.certificate n γ).density x ≤ ENNReal.ofReal
      (C.densityEnvelope_polynomial.coefficient *
        seq.resolution n ^ C.densityEnvelope_polynomial.exponent) := by
  exact ((C.certificate n γ).density_le_bound x).trans
    ((C.densityBound_le_envelope n γ).trans (C.densityEnvelope_polynomial.bound n))

end WorldTemperedSemialgebraicPriorFamily

end Kakeya4.Framework
