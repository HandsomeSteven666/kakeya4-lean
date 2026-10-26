import Kakeya4.Construction.Framework.WorldTemperedComplexity
import Kakeya4.Construction.Framework.ObservedCoordinates

/-!
# Finite internal trajectory-copy indices for tempered prior certificates

The world tag, the internal coefficient-space copy, and the observed base are kept as separate
coordinates. Per-copy prior certificates and their common polynomial envelopes are caller data;
this file proves the resulting finite atom-count aggregation bounds.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- The finite internal trajectory-copy index over a world tag. This named finite type keeps the
world and copy projections available while giving the tag its discrete measurable structure. -/
structure WorldTrajectoryCopyIndex (worldCount : ℕ)
    (copyCount : Fin worldCount → ℕ) where
  world : Fin worldCount
  copy : Fin (copyCount world)

private def worldTrajectoryCopyIndexEquiv (worldCount : ℕ)
    (copyCount : Fin worldCount → ℕ) :
    (Σ γ : Fin worldCount, Fin (copyCount γ)) ≃
      WorldTrajectoryCopyIndex worldCount copyCount where
  toFun p := ⟨p.1, p.2⟩
  invFun p := ⟨p.world, p.copy⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl

instance worldTrajectoryCopyIndexFintype (worldCount : ℕ)
    (copyCount : Fin worldCount → ℕ) :
    Fintype (WorldTrajectoryCopyIndex worldCount copyCount) :=
  Fintype.ofEquiv (Σ γ : Fin worldCount, Fin (copyCount γ))
    (worldTrajectoryCopyIndexEquiv worldCount copyCount)

instance worldTrajectoryCopyIndexMeasurableSpace (worldCount : ℕ)
    (copyCount : Fin worldCount → ℕ) :
    MeasurableSpace (WorldTrajectoryCopyIndex worldCount copyCount) := ⊤

instance worldTrajectoryCopyIndexMeasurableSingletonClass (worldCount : ℕ)
    (copyCount : Fin worldCount → ℕ) :
    MeasurableSingletonClass (WorldTrajectoryCopyIndex worldCount copyCount) where
  measurableSet_singleton := by simp

/-- The observed-base port keeps world and internal copy as distinct tags, followed by the
observed `(time, spatial point)` base. This is the coordinate shape for the later indexed
incidence-law consumer; no copy is absorbed into the world or into an observed feature. -/
abbrev WorldCopyObservedBase (worldCount : ℕ)
    (copyCount : Fin worldCount → ℕ) (v : ModelVersion) :=
  Σ γ : Fin worldCount, Fin (copyCount γ) × ObservedBase v

/-- Assemble copy-specific base densities on the explicitly tagged
`(world, internal copy, time, spatial point)` port. -/
def worldCopyObservedBaseDensity {worldCount : ℕ}
    (copyCount : Fin worldCount → ℕ) (v : ModelVersion)
    (density : ∀ γ, Fin (copyCount γ) → ObservedBase v → ℝ≥0∞) :
    WorldCopyObservedBase worldCount copyCount v → ℝ≥0∞ := fun p =>
  density p.1 p.2.1 p.2.2

@[simp]
theorem worldCopyObservedBaseDensity_mk {worldCount : ℕ}
    (copyCount : Fin worldCount → ℕ) (v : ModelVersion)
    (density : ∀ γ, Fin (copyCount γ) → ObservedBase v → ℝ≥0∞)
    (γ : Fin worldCount) (i : Fin (copyCount γ)) (base : ObservedBase v) :
    worldCopyObservedBaseDensity copyCount v density ⟨γ, (i, base)⟩ = density γ i base := rfl

/-- A finite family of prior-density certificates indexed independently by resolution, world,
and internal trajectory copy. Shared envelopes control the number of copies per world, pieces,
atoms per piece, and density height. The exact certificates and pointwise bounds are caller
inputs; this structure does not manufacture densities for arbitrary priors. -/
structure WorldCopyTemperedSemialgebraicPriorFamily
    {varCount : ℕ} [MeasurableSpace (Fin varCount → ℝ)] [BorelSpace (Fin varCount → ℝ)]
    (seq : ExactSequence)
    (worldCount : ℕ → ℕ)
    (copyCount : ∀ n, Fin (worldCount n) → ℕ)
    (reference prior : ∀ n (γ : Fin (worldCount n)), Fin (copyCount n γ) →
      Measure (Fin varCount → ℝ))
    (pieceBound atomBound : ∀ n (γ : Fin (worldCount n)), Fin (copyCount n γ) → ℕ)
    (densityBound : ∀ n (γ : Fin (worldCount n)), Fin (copyCount n γ) → ℝ≥0∞)
    (variableBound degreeBound : ℕ) where
  worldCount_polynomial : PolynomiallyBoundedNatAlong seq worldCount
  copyEnvelope : ℕ → ℕ
  copyEnvelope_polynomial : PolynomiallyBoundedNatAlong seq copyEnvelope
  copyCount_le_envelope : ∀ n γ, copyCount n γ ≤ copyEnvelope n
  pieceEnvelope : ℕ → ℕ
  pieceEnvelope_polynomial : PolynomiallyBoundedNatAlong seq pieceEnvelope
  pieceBound_le_envelope : ∀ n (γ : Fin (worldCount n)) (i : Fin (copyCount n γ)),
    pieceBound n γ i ≤ pieceEnvelope n
  atomEnvelope : ℕ → ℕ
  atomEnvelope_polynomial : PolynomiallyBoundedNatAlong seq atomEnvelope
  atomBound_le_envelope : ∀ n (γ : Fin (worldCount n)) (i : Fin (copyCount n γ)),
    atomBound n γ i ≤ atomEnvelope n
  densityEnvelope : ℕ → ℝ≥0∞
  densityEnvelope_polynomial : PolynomiallyBoundedENNRealAlong seq densityEnvelope
  densityBound_le_envelope : ∀ n (γ : Fin (worldCount n)) (i : Fin (copyCount n γ)),
    densityBound n γ i ≤ densityEnvelope n
  certificate : ∀ n γ i, SemialgebraicPiecewiseDensityCertificate
    (reference n γ i) (prior n γ i) (pieceBound n γ i) variableBound (atomBound n γ i)
    degreeBound (densityBound n γ i)

namespace WorldCopyTemperedSemialgebraicPriorFamily

variable {varCount : ℕ} [MeasurableSpace (Fin varCount → ℝ)] [BorelSpace (Fin varCount → ℝ)]
  {seq : ExactSequence} {worldCount : ℕ → ℕ}
  {copyCount : ∀ n, Fin (worldCount n) → ℕ}
  {reference prior : ∀ n (γ : Fin (worldCount n)), Fin (copyCount n γ) →
    Measure (Fin varCount → ℝ)}
  {pieceBound atomBound : ∀ n (γ : Fin (worldCount n)), Fin (copyCount n γ) → ℕ}
  {densityBound : ∀ n (γ : Fin (worldCount n)), Fin (copyCount n γ) → ℝ≥0∞}
  {variableBound degreeBound : ℕ}

variable (C : WorldCopyTemperedSemialgebraicPriorFamily seq worldCount copyCount reference prior
  pieceBound atomBound densityBound variableBound degreeBound)

/-- The number of atom occurrences in one actual world-copy certificate. -/
def totalAtomCount (n : ℕ) (γ : Fin (worldCount n)) (i : Fin (copyCount n γ)) : ℕ :=
  ∑ j : Fin (C.certificate n γ i).pieceCount, ((C.certificate n γ i).pieces j).atomCount

/-- Sum actual atoms over the internal copies of one world, retaining that world tag. -/
def copyTaggedTotalAtomCount (n : ℕ) (γ : Fin (worldCount n)) : ℕ :=
  ∑ i : Fin (copyCount n γ), C.totalAtomCount n γ i

/-- Sum actual atom occurrences over both the world tags and their distinct internal copies. -/
def worldCopyTotalAtomCount (n : ℕ) : ℕ :=
  ∑ γ : Fin (worldCount n), C.copyTaggedTotalAtomCount n γ

/-- A single world-copy certificate uses at most its piece capacity times its atom capacity. -/
theorem totalAtomCount_le_capacity (n : ℕ) (γ : Fin (worldCount n))
    (i : Fin (copyCount n γ)) :
    C.totalAtomCount n γ i ≤ pieceBound n γ i * atomBound n γ i := by
  unfold totalAtomCount
  calc
    _ ≤ ∑ _j : Fin (C.certificate n γ i).pieceCount, atomBound n γ i := by
      apply Finset.sum_le_sum
      intro j hj
      exact (C.certificate n γ i).atoms_per_piece_le j
    _ = (C.certificate n γ i).pieceCount * atomBound n γ i := by simp
    _ ≤ pieceBound n γ i * atomBound n γ i :=
      Nat.mul_le_mul_right _ (C.certificate n γ i).pieceCount_le

/-- The nested finite sum is bounded by the product of world, copy, piece, and per-piece atom
envelopes. Every copy occurrence is counted, including equal certificates at different indices. -/
theorem worldCopyTotalAtomCount_le_envelopes (n : ℕ) :
    C.worldCopyTotalAtomCount n ≤
      worldCount n * C.copyEnvelope n * C.pieceEnvelope n * C.atomEnvelope n := by
  unfold worldCopyTotalAtomCount copyTaggedTotalAtomCount
  calc
    _ ≤ ∑ γ : Fin (worldCount n), ∑ i : Fin (copyCount n γ),
        pieceBound n γ i * atomBound n γ i := by
      apply Finset.sum_le_sum
      intro γ hγ
      apply Finset.sum_le_sum
      intro i hi
      exact C.totalAtomCount_le_capacity n γ i
    _ ≤ ∑ γ : Fin (worldCount n),
        copyCount n γ * (C.pieceEnvelope n * C.atomEnvelope n) := by
      apply Finset.sum_le_sum
      intro γ hγ
      calc
        _ ≤ ∑ _i : Fin (copyCount n γ), C.pieceEnvelope n * C.atomEnvelope n := by
          apply Finset.sum_le_sum
          intro i hi
          exact Nat.mul_le_mul (C.pieceBound_le_envelope n γ i)
            (C.atomBound_le_envelope n γ i)
        _ = copyCount n γ * (C.pieceEnvelope n * C.atomEnvelope n) := by simp
    _ ≤ ∑ _γ : Fin (worldCount n),
        C.copyEnvelope n * (C.pieceEnvelope n * C.atomEnvelope n) := by
      apply Finset.sum_le_sum
      intro γ hγ
      exact Nat.mul_le_mul_right _ (C.copyCount_le_envelope n γ)
    _ = worldCount n * C.copyEnvelope n * C.pieceEnvelope n * C.atomEnvelope n := by
      simp [Nat.mul_assoc]

/-- The full world-copy atom total has a single polynomial profile. Its coefficient is the
product of the four envelope coefficients and its exponent is their sum. -/
noncomputable def worldCopyTotalAtomCount_polynomiallyBounded :
    PolynomiallyBoundedNatAlong seq C.worldCopyTotalAtomCount :=
  PolynomiallyBoundedNatAlong.of_le
    (PolynomiallyBoundedNatAlong.mul
      (PolynomiallyBoundedNatAlong.mul
        (PolynomiallyBoundedNatAlong.mul C.worldCount_polynomial C.copyEnvelope_polynomial)
        C.pieceEnvelope_polynomial)
      C.atomEnvelope_polynomial)
    C.worldCopyTotalAtomCount_le_envelopes

/-- Every copy-specific density inherits the common polynomial density envelope. -/
theorem density_le_polynomial_envelope
    (n : ℕ) (γ : Fin (worldCount n)) (i : Fin (copyCount n γ))
    (x : Fin varCount → ℝ) :
    (C.certificate n γ i).density x ≤ ENNReal.ofReal
      (C.densityEnvelope_polynomial.coefficient *
        seq.resolution n ^ C.densityEnvelope_polynomial.exponent) := by
  exact ((C.certificate n γ i).density_le_bound x).trans
    ((C.densityBound_le_envelope n γ i).trans (C.densityEnvelope_polynomial.bound n))

end WorldCopyTemperedSemialgebraicPriorFamily

end Kakeya4.Framework
