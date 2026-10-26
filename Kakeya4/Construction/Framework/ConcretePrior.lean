import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Kakeya4.Construction.Framework.CoordinateObservationBridge
import Kakeya4.Construction.Framework.IncidenceMeasure
import Kakeya4.Construction.Framework.TemperedComplexity
import Kakeya4.Construction.Framework.WorldTemperedComplexity
import Kakeya4.Construction.Framework.WorldCopyTemperedComplexity
import Kakeya4.Construction.Framework.WorldCopyObservationBridge
import Kakeya4.Construction.Framework.WorldCopySpatialAggregation
import Kakeya4.Construction.Framework.WorldTemperedObservationBridge
import Kakeya4.Construction.Framework.WorldTemperedSpatialMass

/-!
# One explicit tempered scalar prior and its selected observation law

The manuscript leaves each world prior as data, subject to the tempered piecewise-constant
density condition. This module constructs one concrete admissible instance: the uniform law on
the scalar coefficient cube `[-1,1]^5`, followed by selection of the first half of the unit-time
interval. It does not infer absolute continuity for other priors.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace Kakeya4.Framework

/-- The scalar coefficient cube in the canonical order `(y₀,V,w₀,w₁,w₂)`. -/
def scalarCoefficientCube : Set (Fin 5 → ℝ) :=
  Set.Icc (fun _ : Fin 5 => (-1 : ℝ)) (fun _ => 1)

/-- The constant density of the uniform probability law on the five-dimensional coefficient
cube. Its value is `1 / 2^5 = 1/32` on the cube and zero outside it. -/
noncomputable def scalarCubeDensity : (Fin 5 → ℝ) → ℝ≥0∞ :=
  scalarCoefficientCube.indicator (fun _ => ENNReal.ofReal (1 / 32 : ℝ))

/-- The coordinate law is defined from its explicit Lebesgue density, not supplied as a density
certificate. -/
noncomputable def scalarCubeCoordinatePrior : Measure (Fin 5 → ℝ) :=
  volume.withDensity scalarCubeDensity

theorem scalarCoefficientCube_measurable : MeasurableSet scalarCoefficientCube :=
  measurableSet_Icc

theorem scalarCoefficientCube_volume :
    (volume : Measure (Fin 5 → ℝ)) scalarCoefficientCube = ENNReal.ofReal 32 := by
  rw [scalarCoefficientCube, Real.volume_Icc_pi]
  norm_num

theorem scalarCubeDensity_measurable : Measurable scalarCubeDensity := by
  exact measurable_const.indicator scalarCoefficientCube_measurable

theorem scalarCubeCoordinatePrior_isProbability :
    IsProbabilityMeasure scalarCubeCoordinatePrior := by
  constructor
  rw [scalarCubeCoordinatePrior, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  rw [scalarCubeDensity, lintegral_indicator_const scalarCoefficientCube_measurable]
  rw [scalarCoefficientCube_volume]
  rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 32 : ℝ))]
  norm_num

private noncomputable def scalarCubeLowerAtom (i : Fin 5) : PolynomialBooleanFormula 5 :=
  .nonnegative (MvPolynomial.X i + MvPolynomial.C (1 : ℝ))

private noncomputable def scalarCubeUpperAtom (i : Fin 5) : PolynomialBooleanFormula 5 :=
  .nonnegative (MvPolynomial.C (1 : ℝ) - MvPolynomial.X i)

/-- A polynomial Boolean formula for the coefficient cube. It has ten linear atoms. -/
noncomputable def scalarCubeFormula : PolynomialBooleanFormula 5 :=
  .conjunction (scalarCubeLowerAtom 0)
    (.conjunction (scalarCubeUpperAtom 0)
      (.conjunction (scalarCubeLowerAtom 1)
        (.conjunction (scalarCubeUpperAtom 1)
          (.conjunction (scalarCubeLowerAtom 2)
            (.conjunction (scalarCubeUpperAtom 2)
              (.conjunction (scalarCubeLowerAtom 3)
                (.conjunction (scalarCubeUpperAtom 3)
                  (.conjunction (scalarCubeLowerAtom 4)
                    (scalarCubeUpperAtom 4)))))))))

private theorem scalarCubeLowerAtom_degree_le_one (i : Fin 5) :
    (MvPolynomial.X i + MvPolynomial.C (1 : ℝ)).totalDegree ≤ 1 := by
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

private theorem scalarCubeUpperAtom_degree_le_one (i : Fin 5) :
    (MvPolynomial.C (1 : ℝ) - MvPolynomial.X i).totalDegree ≤ 1 := by
  have hrewrite : MvPolynomial.C (1 : ℝ) - MvPolynomial.X i =
      -MvPolynomial.X i + MvPolynomial.C (1 : ℝ) := by ring
  rw [hrewrite]
  calc
    _ ≤ max (-MvPolynomial.X i).totalDegree (MvPolynomial.C (1 : ℝ)).totalDegree :=
      MvPolynomial.totalDegree_add _ _
    _ = 1 := by simp

theorem scalarCubeFormula_atomCount : scalarCubeFormula.atomCount = 10 := by
  simp [scalarCubeFormula, scalarCubeLowerAtom, scalarCubeUpperAtom,
    PolynomialBooleanFormula.atomCount]

theorem scalarCubeFormula_degree_le_one : scalarCubeFormula.maxAtomDegree ≤ 1 := by
  simp only [scalarCubeFormula, scalarCubeLowerAtom, scalarCubeUpperAtom,
    PolynomialBooleanFormula.maxAtomDegree, Nat.max_le]
  exact ⟨scalarCubeLowerAtom_degree_le_one 0,
    ⟨scalarCubeUpperAtom_degree_le_one 0,
      ⟨scalarCubeLowerAtom_degree_le_one 1,
        ⟨scalarCubeUpperAtom_degree_le_one 1,
          ⟨scalarCubeLowerAtom_degree_le_one 2,
            ⟨scalarCubeUpperAtom_degree_le_one 2,
              ⟨scalarCubeLowerAtom_degree_le_one 3,
                ⟨scalarCubeUpperAtom_degree_le_one 3,
                  ⟨scalarCubeLowerAtom_degree_le_one 4,
                    scalarCubeUpperAtom_degree_le_one 4⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem scalarCubeFormula_models : scalarCubeFormula.models = scalarCoefficientCube := by
  ext x
  simp only [PolynomialBooleanFormula.models, Set.mem_setOf_eq, scalarCubeFormula,
    scalarCubeLowerAtom, scalarCubeUpperAtom, PolynomialBooleanFormula.Holds,
    map_add, map_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X, scalarCoefficientCube, Set.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h0l, h0u, h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u⟩
    constructor
    · intro i
      fin_cases i <;> simp at * <;> linarith
    · intro i
      fin_cases i <;> simp at * <;> linarith
  · rintro ⟨hl, hu⟩
    exact ⟨by linarith [hl 0], by linarith [hu 0],
      by linarith [hl 1], by linarith [hu 1],
      by linarith [hl 2], by linarith [hu 2],
      by linarith [hl 3], by linarith [hu 3],
      by linarith [hl 4], by linarith [hu 4]⟩

/-- The trajectory prior is the coordinate law transported back through the manuscript's
canonical scalar chart. -/
noncomputable def scalarCubeTrajectoryPrior : Measure ScalarTrajectory :=
  scalarCubeCoordinatePrior.map scalarTrajectoryFinMeasurableEquiv.symm

theorem scalarCubeTrajectoryPrior_map_chart :
    scalarCubeTrajectoryPrior.map scalarTrajectoryFinMeasurableEquiv =
      scalarCubeCoordinatePrior := by
  simp [scalarCubeTrajectoryPrior]

theorem scalarCubeTrajectoryPrior_isProbability :
    IsProbabilityMeasure scalarCubeTrajectoryPrior := by
  letI : IsProbabilityMeasure scalarCubeCoordinatePrior :=
    scalarCubeCoordinatePrior_isProbability
  unfold scalarCubeTrajectoryPrior
  exact inferInstance

/-- A one-world system whose actual prior is the constructed scalar coefficient-cube law. -/
noncomputable def scalarCubeWorldPriorSystem : WorldPriorSystem (Trajectory .scalar) where
  worldCount := 1
  weight := fun _ => 1
  weight_sum := by simp
  prior := fun _ => scalarCubeTrajectoryPrior
  prior_isProbability := by
    intro γ
    exact scalarCubeTrajectoryPrior_isProbability

/-- The two-piece partition is the cube and its complement. The density is `1/32` on the cube
and zero on the complement; the certificate is constructed from the actual law above. -/
noncomputable def scalarCubeStandardDensityCertificate :
    SemialgebraicPiecewiseDensityCertificate
      (volume : Measure (Fin 5 → ℝ))
      ((scalarCubeWorldPriorSystem.prior (0 : Fin 1)).map scalarTrajectoryFinMeasurableEquiv)
      2 5 10 1 (ENNReal.ofReal (1 / 32 : ℝ)) where
  pieceCount := 2
  pieceCount_le := le_rfl
  variableCount_le := le_rfl
  pieces i := if i.val = 0 then scalarCubeFormula else .complement scalarCubeFormula
  atoms_per_piece_le := by
    intro i
    by_cases hi : i.val = 0
    · simp [hi, scalarCubeFormula_atomCount]
    · simp [hi, scalarCubeFormula_atomCount, PolynomialBooleanFormula.atomCount]
  degree_per_piece_le := by
    intro i
    by_cases hi : i.val = 0
    · simp [hi, scalarCubeFormula_degree_le_one]
    · simp [hi, scalarCubeFormula_degree_le_one,
        PolynomialBooleanFormula.maxAtomDegree]
  pieces_pairwise_disjoint := by
    intro i hi j hj hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint scalarCubeFormula.models scalarCubeFormula.complement.models
      simp [Set.disjoint_left, PolynomialBooleanFormula.models,
        PolynomialBooleanFormula.Holds]
    · change Disjoint scalarCubeFormula.complement.models scalarCubeFormula.models
      simp [Set.disjoint_left, PolynomialBooleanFormula.models,
        PolynomialBooleanFormula.Holds]
    · exact (hij rfl).elim
  pieces_cover := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      by_cases hx : x ∈ scalarCoefficientCube
      · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
        simp [hx, scalarCubeFormula_models]
      · refine Set.mem_iUnion.mpr ⟨1, ?_⟩
        change x ∈ (scalarCubeFormula.complement).models
        have hnot : x ∉ scalarCubeFormula.models := by
          rw [scalarCubeFormula_models]
          exact hx
        change ¬ scalarCubeFormula.Holds x
        simpa [PolynomialBooleanFormula.models] using hnot
  density := scalarCubeDensity
  density_measurable := scalarCubeDensity_measurable
  value i := if i.val = 0 then ENNReal.ofReal (1 / 32 : ℝ) else 0
  density_eq_value := by
    intro i x hx
    fin_cases i
    · change x ∈ scalarCubeFormula.models at hx
      have hcube : x ∈ scalarCoefficientCube := by
        simpa only [scalarCubeFormula_models] using hx
      simp [scalarCubeDensity, hcube]
    · change x ∈ (scalarCubeFormula.complement).models at hx
      have hnot : x ∉ scalarCubeFormula.models := by
        simpa [PolynomialBooleanFormula.models, PolynomialBooleanFormula.Holds] using hx
      have hnotCube : x ∉ scalarCoefficientCube := by
        simpa only [scalarCubeFormula_models] using hnot
      simp [scalarCubeDensity, hnotCube]
  densityBound_lt_top := ENNReal.ofReal_lt_top
  density_le_bound := by
    intro x
    by_cases hx : x ∈ scalarCoefficientCube <;>
      simp [scalarCubeDensity, hx]
  prior_eq_withDensity := by
    change (scalarCubeTrajectoryPrior.map scalarTrajectoryFinMeasurableEquiv) =
      volume.withDensity scalarCubeDensity
    rw [scalarCubeTrajectoryPrior_map_chart]
    rfl

/-- The same actual coordinate prior at every exact-sequence index. This constructs one
constant-complexity family for the finite piece/atom/density clauses; it is not a certificate
for arbitrary manuscript world priors or the other tempered fields. -/
noncomputable def scalarCubeConstantTemperedFamily (seq : ExactSequence) :
    TemperedSemialgebraicPriorFamily seq
      (fun _ : ℕ => (volume : Measure (Fin 5 → ℝ)))
      (fun _ => (scalarCubeWorldPriorSystem.prior (0 : Fin 1)).map
        scalarTrajectoryFinMeasurableEquiv)
      (fun _ => 2) (fun _ => 10) (fun _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 where
  pieceBound_polynomial := {
    coefficient := 2
    exponent := 0
    bound := by intro n; norm_num
  }
  atomBound_polynomial := {
    coefficient := 10
    exponent := 0
    bound := by intro n; norm_num
  }
  densityBound_polynomial := {
    coefficient := 1 / 32
    coefficient_nonneg := by norm_num
    exponent := 0
    bound := by intro n; simp
  }
  certificate := fun _ => scalarCubeStandardDensityCertificate

/-- Each member of the constant family contains at most twenty atom occurrences in total. -/
theorem scalarCubeConstantTemperedFamily_totalAtomCount_le20
    (seq : ExactSequence) (n : ℕ) :
    (scalarCubeConstantTemperedFamily seq).totalAtomCount n ≤ 20 := by
  calc
    _ ≤ (fun _ : ℕ => 2) n * (fun _ : ℕ => 10) n :=
      (scalarCubeConstantTemperedFamily seq).totalAtomCount_le_capacity n
    _ = 20 := by norm_num

/-- The existing family theorem yields the uniform exact-sequence polynomial bound on total
semialgebraic atom count. -/
noncomputable def scalarCubeConstantTemperedFamily_totalAtomCount_polynomiallyBounded
    (seq : ExactSequence) :
    PolynomiallyBoundedNatAlong seq (scalarCubeConstantTemperedFamily seq).totalAtomCount :=
  (scalarCubeConstantTemperedFamily seq).totalAtomCount_polynomiallyBounded

/-- The generic atom-count closure chooses the explicit envelope `20 * resolution^0`. -/
theorem scalarCubeConstantTemperedFamily_totalAtomCount_boundProfile
    (seq : ExactSequence) :
    let p := (scalarCubeConstantTemperedFamily seq).totalAtomCount_polynomiallyBounded
    p.coefficient = 20 ∧ p.exponent = 0 := by
  constructor <;> rfl

/-- The family density has the explicit pointwise bound `ofReal (1/32)`. -/
theorem scalarCubeConstantTemperedFamily_density_le
    (seq : ExactSequence) (n : ℕ) (x : Fin 5 → ℝ) :
    ((scalarCubeConstantTemperedFamily seq).certificate n).density x ≤
      ENNReal.ofReal (1 / 32 : ℝ) :=
  ((scalarCubeConstantTemperedFamily seq).certificate n).density_le_bound x

/-- The explicit scalar cube prior as a one-world instance of the finite world-indexed family.
The world certificate is constructed from the actual prior above; it is not an arbitrary-prior
absolute-continuity inference. -/
noncomputable def scalarCubeOneWorldTemperedFamily (seq : ExactSequence) :
    WorldTemperedSemialgebraicPriorFamily seq (fun _ : ℕ => 1)
      (fun _ _ => (volume : Measure (Fin 5 → ℝ)))
      (fun _ _ => (scalarCubeWorldPriorSystem.prior (0 : Fin 1)).map
        scalarTrajectoryFinMeasurableEquiv)
      (fun _ _ => 2) (fun _ _ => 10)
      (fun _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 where
  pieceEnvelope := fun _ => 2
  pieceEnvelope_polynomial := {
    coefficient := 2
    exponent := 0
    bound := by intro n; norm_num
  }
  pieceBound_le_envelope := by intro n γ; rfl
  atomEnvelope := fun _ => 10
  atomEnvelope_polynomial := {
    coefficient := 10
    exponent := 0
    bound := by intro n; norm_num
  }
  atomBound_le_envelope := by intro n γ; rfl
  densityEnvelope := fun _ => ENNReal.ofReal (1 / 32 : ℝ)
  densityEnvelope_polynomial := {
    coefficient := 1 / 32
    coefficient_nonneg := by norm_num
    exponent := 0
    bound := by intro n; simp
  }
  densityBound_le_envelope := by intro n γ; rfl
  worldCount_polynomial := {
    coefficient := 1
    exponent := 0
    bound := by intro n; simp
  }
  certificate := by
    intro n γ
    exact scalarCubeStandardDensityCertificate

/-- The explicit one-world cube certificate has at most twenty world-tagged atom occurrences
at every resolution. -/
theorem scalarCubeOneWorldTemperedFamily_totalAtomCount_le20
    (seq : ExactSequence) (n : ℕ) :
    (scalarCubeOneWorldTemperedFamily seq).worldTaggedTotalAtomCount n ≤ 20 := by
  have h := (scalarCubeOneWorldTemperedFamily seq).worldTaggedTotalAtomCount_le_envelopes n
  norm_num [scalarCubeOneWorldTemperedFamily] at h ⊢
  exact h

/-- The one-world cube instance calls the generic world-tagged polynomial-bound consumer. -/
noncomputable def scalarCubeOneWorldTemperedFamily_totalAtomCount_polynomiallyBounded
    (seq : ExactSequence) :
    PolynomiallyBoundedNatAlong seq
      (scalarCubeOneWorldTemperedFamily seq).worldTaggedTotalAtomCount :=
  (scalarCubeOneWorldTemperedFamily seq).worldTaggedTotalAtomCount_polynomiallyBounded

/-- The one-world cube family inherits the explicit aggregate envelope `(20,0)`. -/
theorem scalarCubeOneWorldTemperedFamily_totalAtomCount_boundProfile
    (seq : ExactSequence) :
    let p := scalarCubeOneWorldTemperedFamily_totalAtomCount_polynomiallyBounded seq
    p.coefficient = 20 ∧ p.exponent = 0 := by
  constructor <;> rfl

/-- Two internal copies of the actual scalar Fin5 cube prior, kept under one world tag. The same
certificate is supplied at each copy index; both occurrences are counted by the generic family. -/
noncomputable def scalarCubeTwoCopyTemperedFamily (seq : ExactSequence) :
    WorldCopyTemperedSemialgebraicPriorFamily seq (fun _ : ℕ => 1) (fun _ _ => 2)
      (fun _ _ _ => (volume : Measure (Fin 5 → ℝ)))
      (fun _ _ _ => (scalarCubeWorldPriorSystem.prior (0 : Fin 1)).map
        scalarTrajectoryFinMeasurableEquiv)
      (fun _ _ _ => 2) (fun _ _ _ => 10)
      (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 where
  worldCount_polynomial := {
    coefficient := 1
    exponent := 0
    bound := by intro n; simp
  }
  copyEnvelope := fun _ => 2
  copyEnvelope_polynomial := {
    coefficient := 2
    exponent := 0
    bound := by intro n; norm_num
  }
  copyCount_le_envelope := by intro n γ; rfl
  pieceEnvelope := fun _ => 2
  pieceEnvelope_polynomial := {
    coefficient := 2
    exponent := 0
    bound := by intro n; norm_num
  }
  pieceBound_le_envelope := by intro n γ i; rfl
  atomEnvelope := fun _ => 10
  atomEnvelope_polynomial := {
    coefficient := 10
    exponent := 0
    bound := by intro n; norm_num
  }
  atomBound_le_envelope := by intro n γ i; rfl
  densityEnvelope := fun _ => ENNReal.ofReal (1 / 32 : ℝ)
  densityEnvelope_polynomial := {
    coefficient := 1 / 32
    coefficient_nonneg := by norm_num
    exponent := 0
    bound := by intro n; simp
  }
  densityBound_le_envelope := by intro n γ i; rfl
  certificate := by
    intro n γ i
    exact scalarCubeStandardDensityCertificate

/-- The two-copy regression obtains the explicit aggregate atom bound `1 × 2 × 2 × 10 = 40`
from the generic world-copy theorem. -/
theorem scalarCubeTwoCopyTemperedFamily_worldCopyTotalAtomCount_le40
    (seq : ExactSequence) (n : ℕ) :
    (scalarCubeTwoCopyTemperedFamily seq).worldCopyTotalAtomCount n ≤ 40 := by
  have h := (scalarCubeTwoCopyTemperedFamily seq).worldCopyTotalAtomCount_le_envelopes n
  simpa [scalarCubeTwoCopyTemperedFamily] using h

/-- The two-copy scalar cube family calls the generic world-copy polynomial closure. -/
noncomputable def scalarCubeTwoCopyTemperedFamily_totalAtomCount_polynomiallyBounded
    (seq : ExactSequence) :
    PolynomiallyBoundedNatAlong seq
      (scalarCubeTwoCopyTemperedFamily seq).worldCopyTotalAtomCount :=
  (scalarCubeTwoCopyTemperedFamily seq).worldCopyTotalAtomCount_polynomiallyBounded

/-- The finite two-copy regression has aggregate polynomial profile `(40,0)`. -/
theorem scalarCubeTwoCopyTemperedFamily_totalAtomCount_boundProfile
    (seq : ExactSequence) :
    let p := scalarCubeTwoCopyTemperedFamily_totalAtomCount_polynomiallyBounded seq
    p.coefficient = 40 ∧ p.exponent = 0 := by
  constructor <;> rfl

/-- The selected event keeps every trajectory during the first half of the unit-time interval. -/
def scalarHalfTimeWindow : Set ℝ := Set.Icc (0 : ℝ) (1 / 2)

def scalarHalfTimeEvent : Set (ScalarTrajectory × ℝ) :=
  Set.univ ×ˢ scalarHalfTimeWindow

/-- Polynomial syntax for the half-time interval, considered as a one-coordinate semialgebraic
set. -/
noncomputable def scalarHalfTimeFormula : PolynomialBooleanFormula 1 :=
  .conjunction (.nonnegative (MvPolynomial.X 0))
    (.nonnegative (MvPolynomial.C (1 / 2 : ℝ) - MvPolynomial.X 0))

theorem scalarHalfTimeFormula_models :
    scalarHalfTimeFormula.models =
      Set.Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1 / 2) := by
  ext x
  simp only [PolynomialBooleanFormula.models, Set.mem_setOf_eq, scalarHalfTimeFormula,
    PolynomialBooleanFormula.Holds, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Set.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · intro i
      fin_cases i
      simpa using h0
    · intro i
      fin_cases i
      simp
      linarith
  · rintro ⟨h0, h1⟩
    exact ⟨h0 0, by linarith [h1 0]⟩

theorem scalarHalfTimeEvent_eq_formula_preimage :
    scalarHalfTimeEvent =
      {p : ScalarTrajectory × ℝ |
        (fun _ : Fin 1 => p.2) ∈ scalarHalfTimeFormula.models} := by
  ext ⟨l, t⟩
  simp only [scalarHalfTimeEvent, Set.mem_prod, Set.mem_univ, true_and]
  rw [scalarHalfTimeWindow, scalarHalfTimeFormula_models]
  simp [Set.mem_Icc, Pi.le_def]

theorem scalarHalfTimeEvent_measurable : MeasurableSet scalarHalfTimeEvent := by
  exact MeasurableSet.prod MeasurableSet.univ measurableSet_Icc

/-- The concrete incidence selection restricts to a genuine half-time window. Its selected
measure is left unnormalized. -/
noncomputable def scalarCubeHalfTimeSelection : IncidenceSelection .scalar where
  priors := scalarCubeWorldPriorSystem
  event := fun _ => scalarHalfTimeEvent
  event_measurable := fun _ => scalarHalfTimeEvent_measurable

/-- A real two-copy selection: both copies use the constructed scalar cube prior and the same
measurable half-time incidence event, while each copy keeps a separate tag and receives weight
`1/2` within the single world. -/
noncomputable def scalarCubeTwoCopyHalfTimeSelection : WorldCopyIncidenceSelection .scalar where
  worldCount := 1
  copyCount := fun _ => 2
  worldWeight := fun _ => 1
  copyWeight := fun _ _ => (1 / 2 : ℝ≥0)
  prior := fun _ _ => scalarCubeTrajectoryPrior
  prior_isProbability := by
    intro γ i
    exact scalarCubeTrajectoryPrior_isProbability
  event := fun _ _ => scalarHalfTimeEvent
  event_measurable := by
    intro γ i
    exact scalarHalfTimeEvent_measurable

theorem scalarHalfTimeWindow_measure :
    unitTimeMeasure scalarHalfTimeWindow = ENNReal.ofReal (1 / 2 : ℝ) := by
  unfold unitTimeMeasure scalarHalfTimeWindow
  rw [Measure.restrict_apply measurableSet_Icc]
  have hinter : Set.Icc (0 : ℝ) (1 / 2) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · rintro ⟨ht, _⟩
      exact ht
    · intro ht
      exact ⟨ht, ⟨ht.1, ht.2.trans (by norm_num)⟩⟩
  rw [hinter, Real.volume_Icc]
  norm_num

theorem scalarCubeHalfTimeSelection_totalMass :
    scalarCubeHalfTimeSelection.totalMass = ENNReal.ofReal (1 / 2 : ℝ) := by
  have hprior : scalarCubeTrajectoryPrior Set.univ = 1 := by
    letI : IsProbabilityMeasure scalarCubeTrajectoryPrior :=
      scalarCubeTrajectoryPrior_isProbability
    exact measure_univ
  have hselected :
      ((scalarCubeTrajectoryPrior.prod unitTimeMeasure).restrict scalarHalfTimeEvent)
        Set.univ =
        ENNReal.ofReal (1 / 2 : ℝ) := by
    change ((scalarCubeTrajectoryPrior.prod unitTimeMeasure).restrict
      (Set.univ ×ˢ scalarHalfTimeWindow)) Set.univ = _
    haveI : SFinite unitTimeMeasure := by
      unfold unitTimeMeasure
      infer_instance
    rw [Measure.restrict_apply_univ]
    rw [Measure.prod_prod]
    change scalarCubeTrajectoryPrior Set.univ *
      unitTimeMeasure scalarHalfTimeWindow = _
    rw [hprior, one_mul, scalarHalfTimeWindow_measure]
  change ∑ γ : Fin 1,
      (scalarCubeWorldPriorSystem.weight γ : ℝ≥0∞) *
        scalarCubeWorldPriorSystem.selectedIncidenceMeasure
          scalarCubeHalfTimeSelection.event γ Set.univ = _
  rw [Fin.sum_univ_one]
  simp only [scalarCubeWorldPriorSystem, ENNReal.coe_one, one_mul]
  exact hselected

/-- The actual observation-law density theorem for this concrete prior and selected event. Its
right-hand side retains the half-time event indicator through the selected density certificate
and keeps the selected mass `1/2` unnormalized. -/
theorem scalarCubeHalfTimeSelection_observationLaw
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin 1 → VersionWorldData .scalar) :
    worldTaggedObservationBaseBinLaw scalarCubeHalfTimeSelection seq depth n worldData =
      ((Measure.count : Measure (Fin 1)).prod
        ((observedBaseReference .scalar).prod
          (Measure.count : Measure (HiddenBin .scalar)))).withDensity
        (fun p => (scalarCubeHalfTimeSelection.priors.weight p.1 : ℝ≥0∞) *
          observedCoordinateHiddenBinSliceDensity .scalar
            (unobservedFiberReference .scalar)
            (selectedObservedCoordinateDensity scalarCubeHalfTimeSelection
              (trajectoryPriorDensityCertificates_of_standardSemialgebraic .scalar
                scalarCubeHalfTimeSelection.priors 2 5 10 1
                (ENNReal.ofReal (1 / 32 : ℝ))
                (fun _ => scalarCubeStandardDensityCertificate)) p.1)
            (dyadicRoundedWidth
              (seq.depthScale depth n / worldDerivativeScale .scalar (worldData p.1))) p.2) := by
  exact worldTaggedObservationBaseBinLaw_eq_withDensity_of_standardSemialgebraic
    scalarCubeHalfTimeSelection seq depth n worldData 2 5 10 1
    (ENNReal.ofReal (1 / 32 : ℝ)) (fun _ => scalarCubeStandardDensityCertificate)

/-- Regression consumer for the world-tempered observation adapter. It uses the actual
half-time-selected scalar cube prior at every scale and obtains the law directly from the
shared-envelope certificate family. -/
theorem scalarCubeHalfTimeSelection_observationLaw_of_worldTemperedFamily
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin 1 → VersionWorldData .scalar) :
    worldTaggedObservationBaseBinLaw scalarCubeHalfTimeSelection seq depth n worldData =
      ((Measure.count : Measure (Fin 1)).prod
        ((observedBaseReference .scalar).prod
          (Measure.count : Measure (HiddenBin .scalar)))).withDensity
        (fun p => (scalarCubeHalfTimeSelection.priors.weight p.1 : ℝ≥0∞) *
          observedCoordinateHiddenBinSliceDensity .scalar
            (unobservedFiberReference .scalar)
            (selectedObservedCoordinateDensity scalarCubeHalfTimeSelection
              (trajectoryPriorDensityCertificates_of_standardSemialgebraic .scalar
                scalarCubeHalfTimeSelection.priors 2 5 10 1
                (ENNReal.ofReal (1 / 32 : ℝ))
                (fun γ =>
                  (scalarCubeOneWorldTemperedFamily seq).standardCoordinateCertificate
                    (fun _ => scalarCubeHalfTimeSelection) seq
                    (fun _ _ => 2) (fun _ _ => 10)
                    (fun _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ)) p.1)
            (dyadicRoundedWidth
              (seq.depthScale depth n / worldDerivativeScale .scalar (worldData p.1))) p.2) := by
  exact worldTaggedObservationBaseBinLaw_eq_withDensity_of_worldTemperedFamily
    (fun _ => scalarCubeHalfTimeSelection) seq depth (fun _ => worldData)
    (fun _ _ => 2) (fun _ _ => 10) (fun _ _ => ENNReal.ofReal (1 / 32 : ℝ))
    5 1 (scalarCubeOneWorldTemperedFamily seq) n

/-- Concrete world-tagged `(time, spatial point)` density for the selected scalar cube prior.
The hidden-bin partition is summed out, while the half-time event and its unnormalized mass
remain encoded in the selected density. -/
theorem scalarCubeHalfTimeSelection_worldTaggedBaseLaw_eq_withDensity_of_worldTemperedFamily
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin 1 → VersionWorldData .scalar) :
    worldTaggedObservationBaseLaw scalarCubeHalfTimeSelection seq depth n worldData =
      ((Measure.count : Measure (Fin 1)).prod
        (observedBaseReference .scalar)).withDensity
        (fun p => (scalarCubeHalfTimeSelection.priors.weight p.1 : ℝ≥0∞) *
          ∫⁻ fiber, selectedObservedCoordinateDensity scalarCubeHalfTimeSelection
            ((scalarCubeOneWorldTemperedFamily seq).trajectoryDensityCertificates
              (fun _ => scalarCubeHalfTimeSelection) seq
              (fun _ _ => 2) (fun _ _ => 10)
              (fun _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n)
            p.1 (p.2, fiber) ∂unobservedFiberReference .scalar) := by
  exact worldTaggedObservationBaseLaw_eq_withDensity_of_worldTemperedFamily
    (fun _ => scalarCubeHalfTimeSelection) seq depth (fun _ => worldData)
    (fun _ _ => 2) (fun _ _ => 10)
    (fun _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1
    (scalarCubeOneWorldTemperedFamily seq) n

/-- Actual two-copy density consumer. The cube prior and half-time event are separately supplied
at each copy, the Fin2 copy tag is retained beside the Fin1 world tag, and the exact pushed
semialgebraic certificates from `scalarCubeTwoCopyTemperedFamily` feed the copy-indexed theorem. -/
theorem scalarCubeTwoCopyHalfTimeSelection_observationLaw_eq_withDensity
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    worldCopyObservationBaseLaw scalarCubeTwoCopyHalfTimeSelection
        seq depth n worldData =
      ((Measure.count : Measure
        (WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2))).prod
        (observedBaseReference .scalar)).withDensity
        (fun p =>
          ((scalarCubeTwoCopyHalfTimeSelection.worldWeight p.1.world *
            scalarCubeTwoCopyHalfTimeSelection.copyWeight p.1.world p.1.copy : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ fiber, selectedObservedCoordinateDensity
            (scalarCubeTwoCopyHalfTimeSelection.singletonSelection p.1.world p.1.copy)
            ((scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
              (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
              (fun _ _ _ => 2) (fun _ _ _ => 10)
              (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n
              p.1.world p.1.copy)
            (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex p.1.world p.1.copy)
            (p.2, fiber) ∂unobservedFiberReference .scalar) := by
  exact worldCopyObservationBaseLaw_eq_withDensity_of_temperedFamily
    (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq depth (fun _ => worldData)
    (fun _ _ _ => 2) (fun _ _ _ => 10)
    (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1
    (scalarCubeTwoCopyTemperedFamily seq) n

/-- The finite copy-weighted incidence mass of the concrete two-copy half-time selection is
exactly one half. Each copy remains a separate summand, with weight `1/2` and selected event
mass `1/2`. -/
theorem scalarCubeTwoCopyHalfTimeSelection_weightedEventMass_eq_half :
    scalarCubeTwoCopyHalfTimeSelection.weightedEventMass =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  let Tag := WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2)
  let e : (Σ γ : Fin 1, Fin 2) ≃ Tag := {
    toFun := fun p => ⟨p.1, p.2⟩
    invFun := fun q => ⟨q.world, q.copy⟩
    left_inv := by intro p; cases p; rfl
    right_inv := by intro q; cases q; rfl
  }
  have hbaseMass :
      scalarCubeHalfTimeSelection.measure (0 : Fin 1) Set.univ =
        ENNReal.ofReal (1 / 2 : ℝ) := by
    have h := scalarCubeHalfTimeSelection_totalMass
    change ∑ γ : Fin 1,
      (scalarCubeWorldPriorSystem.weight γ : ℝ≥0∞) *
        scalarCubeWorldPriorSystem.selectedIncidenceMeasure
          (fun _ => scalarHalfTimeEvent) γ Set.univ = _ at h
    rw [Fin.sum_univ_one] at h
    simp only [scalarCubeWorldPriorSystem, ENNReal.coe_one, one_mul] at h
    exact h
  have hcomponent : ∀ (γ : Fin 1) (i : Fin 2),
      (scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i).measure
          (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex γ i) Set.univ =
        ENNReal.ofReal (1 / 2 : ℝ) := by
    intro γ i
    change scalarCubeWorldPriorSystem.selectedIncidenceMeasure
      (fun _ => scalarHalfTimeEvent) (0 : Fin 1) Set.univ = _
    exact hbaseMass
  let f : Tag → ℝ≥0∞ := fun q =>
    ((scalarCubeTwoCopyHalfTimeSelection.worldWeight q.world *
      scalarCubeTwoCopyHalfTimeSelection.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞) *
      (scalarCubeTwoCopyHalfTimeSelection.singletonSelection q.world q.copy).measure
        (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex q.world q.copy) Set.univ
  calc
    scalarCubeTwoCopyHalfTimeSelection.weightedEventMass = ∑ q : Tag, f q := by
      rfl
    _ = ∑ p : (Σ γ : Fin 1, Fin 2), f (e p) := by
      symm
      exact e.sum_comp f
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [Fintype.sum_sigma]
      change (∑ γ : Fin 1, ∑ i : Fin 2,
        ((scalarCubeTwoCopyHalfTimeSelection.worldWeight γ *
          scalarCubeTwoCopyHalfTimeSelection.copyWeight γ i : ℝ≥0) : ℝ≥0∞) *
        (scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i).measure
          (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex γ i) Set.univ) = _
      simp_rw [hcomponent]
      have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
        norm_num
      simp [Fin.sum_univ_one, Fin.sum_univ_two,
        scalarCubeTwoCopyHalfTimeSelection, hhalf, ENNReal.coe_inv_two]
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

/-- Integrating the actual Fin5 two-copy observation density over its retained copy tag and
`dt × dy` base recovers the exact unnormalized half-time incidence mass `1/2`. -/
theorem scalarCubeTwoCopyHalfTimeSelection_observationDensityIntegral_eq_half
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    ∫⁻ p, worldCopyObservationBaseDensity scalarCubeTwoCopyHalfTimeSelection
      (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
        (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
        (fun _ _ _ => 2) (fun _ _ _ => 10)
        (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i) p ∂
      ((Measure.count : Measure
        (WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2))).prod
        (observedBaseReference .scalar)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  calc
    _ = scalarCubeTwoCopyHalfTimeSelection.weightedEventMass := by
      exact worldCopyObservationBaseDensity_lintegral_eq_weightedEventMass_of_temperedFamily
        (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq depth
        (fun _ γ i => worldData γ i) (fun _ _ _ => 2) (fun _ _ _ => 10)
        (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1
        (scalarCubeTwoCopyTemperedFamily seq) n
    _ = ENNReal.ofReal (1 / 2 : ℝ) :=
      scalarCubeTwoCopyHalfTimeSelection_weightedEventMass_eq_half

/-- The actual Fin5 two-copy spatial marginal has its exact copy-tagged density over spatial
Lebesgue measure. Each copy uses the certificate produced by the concrete cube family. -/
theorem scalarCubeTwoCopyHalfTimeSelection_spatialLaw_eq_withDensity
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    worldCopyObservationSpatialLaw scalarCubeTwoCopyHalfTimeSelection seq depth n
        (fun γ i => worldData γ i) =
      ((Measure.count : Measure
        (WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2))).prod
        (observedSpatialReference .scalar)).withDensity
        (worldCopyObservationSpatialDensity scalarCubeTwoCopyHalfTimeSelection
          (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
            (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
            (fun _ _ _ => 2) (fun _ _ _ => 10)
            (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)) := by
  exact worldCopyObservationSpatialLaw_eq_withDensity_of_temperedFamily
    (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq depth
    (fun _ γ i => worldData γ i) (fun _ _ _ => 2) (fun _ _ _ => 10)
    (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1
    (scalarCubeTwoCopyTemperedFamily seq) n

/-- Integrating the actual Fin5 two-copy spatial density preserves the unnormalized half-time
incidence mass exactly: the total is `1/2` with both copy tags and caller weights retained. -/
theorem scalarCubeTwoCopyHalfTimeSelection_spatialDensityIntegral_eq_half
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    ∫⁻ p, worldCopyObservationSpatialDensity scalarCubeTwoCopyHalfTimeSelection
      (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
        (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
        (fun _ _ _ => 2) (fun _ _ _ => 10)
        (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i) p ∂
      ((Measure.count : Measure
        (WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2))).prod
        (observedSpatialReference .scalar)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  calc
    _ = scalarCubeTwoCopyHalfTimeSelection.weightedEventMass :=
      worldCopyObservationSpatialDensity_lintegral_eq_weightedEventMass_of_temperedFamily
        (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq depth
        (fun _ γ i => worldData γ i) (fun _ _ _ => 2) (fun _ _ _ => 10)
        (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1
        (scalarCubeTwoCopyTemperedFamily seq) n
    _ = ENNReal.ofReal (1 / 2 : ℝ) :=
      scalarCubeTwoCopyHalfTimeSelection_weightedEventMass_eq_half

/-- The actual Fin5 two-copy spatial law after projecting away both finite labels. Its density is
the sum of the two copy-specific selected spatial densities with the original `1/2` weights. -/
theorem scalarCubeTwoCopyHalfTimeSelection_untaggedSpatialLaw_eq_withDensity
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    worldCopyObservationUntaggedSpatialLaw scalarCubeTwoCopyHalfTimeSelection seq depth n
        (fun γ i => worldData γ i) =
      (observedSpatialReference .scalar).withDensity
        (worldCopyObservationUntaggedSpatialDensity scalarCubeTwoCopyHalfTimeSelection
          (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
            (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
            (fun _ _ _ => 2) (fun _ _ _ => 10)
            (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)) := by
  exact worldCopyObservationUntaggedSpatialLaw_eq_withDensity
    scalarCubeTwoCopyHalfTimeSelection
    (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
      (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
      (fun _ _ _ => 2) (fun _ _ _ => 10)
      (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)
    seq depth n (fun γ i => worldData γ i)

/-- Integrating the actual untagged Fin5 two-copy spatial density gives the original unnormalized
half-time event mass `1/2`; removing labels does not merge, normalize, or remove either copy. -/
theorem scalarCubeTwoCopyHalfTimeSelection_untaggedSpatialDensityIntegral_eq_half
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    ∫⁻ y, worldCopyObservationUntaggedSpatialDensity scalarCubeTwoCopyHalfTimeSelection
      (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
        (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
        (fun _ _ _ => 2) (fun _ _ _ => 10)
        (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i) y
      ∂observedSpatialReference .scalar = ENNReal.ofReal (1 / 2 : ℝ) := by
  calc
    _ = scalarCubeTwoCopyHalfTimeSelection.weightedEventMass :=
      worldCopyObservationUntaggedSpatialDensity_lintegral_eq_weightedEventMass
        scalarCubeTwoCopyHalfTimeSelection
        (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
          (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
          (fun _ _ _ => 2) (fun _ _ _ => 10)
          (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)
        seq depth n (fun γ i => worldData γ i)
    _ = ENNReal.ofReal (1 / 2 : ℝ) :=
      scalarCubeTwoCopyHalfTimeSelection_weightedEventMass_eq_half

/-- The actual two-copy scalar law after retaining the world tag and aggregating internal
copies. Both matching Fin5 cube certificates feed the world-retaining pushforward theorem. -/
theorem scalarCubeTwoCopyHalfTimeSelection_worldSpatialLaw_eq_withDensity
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    worldCopyObservationWorldSpatialLaw scalarCubeTwoCopyHalfTimeSelection seq depth n
        (fun γ i => worldData γ i) =
      ((Measure.count : Measure (Fin 1)).prod
        (observedSpatialReference .scalar)).withDensity
        (worldCopyObservationWorldSpatialDensity scalarCubeTwoCopyHalfTimeSelection
          (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
            (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
            (fun _ _ _ => 2) (fun _ _ _ => 10)
            (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)) := by
  exact worldCopyObservationWorldSpatialLaw_eq_withDensity scalarCubeTwoCopyHalfTimeSelection
    (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
      (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
      (fun _ _ _ => 2) (fun _ _ _ => 10)
      (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)
    seq depth n (fun γ i => worldData γ i)

/-- The retained world's density integrates to `1/2` after its two internal copies have been
aggregated. The proof calls the per-world mass-sum interface with the actual cube family. -/
theorem scalarCubeTwoCopyHalfTimeSelection_worldSpatialDensityIntegral_eq_half
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar)
    (γ : Fin 1) :
    ∫⁻ y, worldCopyObservationWorldSpatialDensity scalarCubeTwoCopyHalfTimeSelection
      (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
        (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
        (fun _ _ _ => 2) (fun _ _ _ => 10)
        (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i) (γ, y)
      ∂observedSpatialReference .scalar = ENNReal.ofReal (1 / 2 : ℝ) := by
  have h := worldCopyObservationWorldSpatialDensity_sum_lintegral_eq_weightedEventMass
    scalarCubeTwoCopyHalfTimeSelection
    (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
      (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
      (fun _ _ _ => 2) (fun _ _ _ => 10)
      (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)
    seq depth n (fun γ i => worldData γ i)
  have hγ : γ = 0 := Subsingleton.elim _ _
  change (∑ γ : Fin 1, _) = _ at h
  simpa only [hγ, Fin.sum_univ_one,
    scalarCubeTwoCopyHalfTimeSelection_weightedEventMass_eq_half] using h

/-- Concrete world-tagged spatial law density formula for the half-time scalar cube family.
The base-bin law is projected through the actual spatial marginal API and remains unnormalized. -/
theorem scalarCubeHalfTimeSelection_worldTaggedSpatialLaw_eq_withDensity_of_worldTemperedFamily
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin 1 → VersionWorldData .scalar) :
    worldTaggedObservationSpatialLaw scalarCubeHalfTimeSelection seq depth n worldData =
      ((Measure.count : Measure (Fin 1)).prod
        (observedSpatialReference .scalar)).withDensity
        (fun p => (scalarCubeHalfTimeSelection.priors.weight p.1 : ℝ≥0∞) *
          selectedObservationSpatialDensity scalarCubeHalfTimeSelection
            ((scalarCubeOneWorldTemperedFamily seq).trajectoryDensityCertificates
              (fun _ => scalarCubeHalfTimeSelection) seq
              (fun _ _ => 2) (fun _ _ => 10)
              (fun _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n) p.1 p.2) := by
  exact worldTemperedWorldTaggedSpatialLaw_eq_withDensity
    (fun _ => scalarCubeHalfTimeSelection) seq depth (fun _ => worldData)
    (fun _ _ => 2) (fun _ _ => 10)
    (fun _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1
    (scalarCubeOneWorldTemperedFamily seq) n

/-- The world-tempered spatial marginal consumer preserves the actual selected mass of the
half-time cube law; its density integrates to one half with the original world weight. -/
theorem scalarCubeHalfTimeSelection_spatialDensityIntegral_of_worldTemperedFamily
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin 1 → VersionWorldData .scalar) :
    (∑ γ : Fin 1,
      (scalarCubeHalfTimeSelection.priors.weight γ : ℝ≥0∞) *
        ∫⁻ y, selectedObservationSpatialDensity scalarCubeHalfTimeSelection
          ((scalarCubeOneWorldTemperedFamily seq).trajectoryDensityCertificates
            (fun _ => scalarCubeHalfTimeSelection) seq
            (fun _ _ => 2) (fun _ _ => 10)
            (fun _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n) γ y
          ∂observedSpatialReference .scalar) = ENNReal.ofReal (1 / 2 : ℝ) := by
  calc
    _ = scalarCubeHalfTimeSelection.totalMass :=
      worldTemperedWeightedSpatialDensityIntegral_eq_totalMass
        (fun _ => scalarCubeHalfTimeSelection) seq depth (fun _ => worldData)
        (fun _ _ => 2) (fun _ _ => 10)
        (fun _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1
        (scalarCubeOneWorldTemperedFamily seq) n
    _ = ENNReal.ofReal (1 / 2 : ℝ) :=
      scalarCubeHalfTimeSelection_totalMass

/-- The full two-copy scalar observation law retains the actual hidden bin and has its exact
joint density. Each copy uses its own geometry-dependent bin width and constructed Fin5 prior. -/
theorem scalarCubeTwoCopyHalfTimeSelection_baseBinLaw_eq_withDensity
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    worldCopyObservationBaseBinLaw scalarCubeTwoCopyHalfTimeSelection seq depth n
        (fun γ i => worldData γ i) =
      ((Measure.count : Measure (WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2))).prod
        ((observedBaseReference .scalar).prod (Measure.count : Measure (HiddenBin .scalar)))).withDensity
          (worldCopyObservationBaseBinDensity scalarCubeTwoCopyHalfTimeSelection
            (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
              (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
              (fun _ _ _ => 2) (fun _ _ _ => 10)
              (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)
            seq depth n (fun γ i => worldData γ i)) := by
  exact worldCopyObservationBaseBinLaw_eq_withDensity scalarCubeTwoCopyHalfTimeSelection
    (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
      (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
      (fun _ _ _ => 2) (fun _ _ _ => 10)
      (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)
    seq depth n (fun γ i => worldData γ i)

/-- Dropping only the hidden bin in the actual two-copy cube example recovers the original
copy-tagged `(time,space)` law, even when the two copies have different world data. -/
theorem scalarCubeTwoCopyHalfTimeSelection_baseLaw_eq_map_baseBinLaw
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    worldCopyObservationBaseLaw scalarCubeTwoCopyHalfTimeSelection seq depth n
        (fun γ i => worldData γ i) =
      Measure.map (fun p : WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2) ×
        (ObservedBase .scalar × HiddenBin .scalar) => (p.1, p.2.1))
        (worldCopyObservationBaseBinLaw scalarCubeTwoCopyHalfTimeSelection seq depth n
          (fun γ i => worldData γ i)) := by
  exact worldCopyObservationBaseLaw_eq_map_baseBinLaw scalarCubeTwoCopyHalfTimeSelection
    seq depth n (fun γ i => worldData γ i)

/-- The actual full hidden-bin density of the two-copy half-time cube integrates to `1/2`,
before any bin, world or copy label is discarded or any selected mass is normalized. -/
theorem scalarCubeTwoCopyHalfTimeSelection_baseBinDensityIntegral_eq_half
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ : Fin 1, ∀ i : Fin 2, VersionWorldData .scalar) :
    ∫⁻ p, worldCopyObservationBaseBinDensity scalarCubeTwoCopyHalfTimeSelection
      (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
        (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
        (fun _ _ _ => 2) (fun _ _ _ => 10)
        (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)
      seq depth n (fun γ i => worldData γ i) p ∂
      ((Measure.count : Measure (WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2))).prod
        ((observedBaseReference .scalar).prod (Measure.count : Measure (HiddenBin .scalar)))) =
        ENNReal.ofReal (1 / 2 : ℝ) := by
  calc
    _ = scalarCubeTwoCopyHalfTimeSelection.weightedEventMass :=
      worldCopyObservationBaseBinDensity_lintegral_eq_weightedEventMass
        scalarCubeTwoCopyHalfTimeSelection
        (fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
          (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
          (fun _ _ _ => 2) (fun _ _ _ => 10)
          (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i)
        seq depth n (fun γ i => worldData γ i)
    _ = ENNReal.ofReal (1 / 2 : ℝ) :=
      scalarCubeTwoCopyHalfTimeSelection_weightedEventMass_eq_half


/-- Actual scalar observed/fiber coordinates in the order `(t,y,V,w0,w1,w2)`. -/
def scalarObservedHiddenBinCoordinates
    (p : ObservedBase .scalar × UnobservedFiber .scalar) : Fin 6 → ℝ :=
  ![p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]

/-- The lower boundary polynomial for the actual scalar hidden bin, with fixed width. -/
noncomputable def scalarObservedHiddenBinPolynomial (width : ℝ) (j : ℤ) :
    MvPolynomial (Fin 6) ℝ :=
  MvPolynomial.X 3 + MvPolynomial.X 0 * MvPolynomial.X 4 +
    MvPolynomial.X 0 ^ 2 * MvPolynomial.X 5 + MvPolynomial.C (-(j : ℝ) * width)

/-- Half-open bin syntax: its lower endpoint is included and upper endpoint excluded. -/
noncomputable def scalarObservedHiddenBinFormula (width : ℝ) (j : ℤ) :
    PolynomialBooleanFormula 6 :=
  .conjunction (.nonnegative (scalarObservedHiddenBinPolynomial width j))
    (.complement (.nonnegative (scalarObservedHiddenBinPolynomial width (j + 1))))

/-- Each scalar hidden-bin formula uses exactly two polynomial sign atoms. -/
theorem scalarObservedHiddenBinFormula_atomCount (width : ℝ) (j : ℤ) :
    (scalarObservedHiddenBinFormula width j).atomCount = 2 := by
  rfl

private theorem scalarObservedHiddenBinPolynomial_degree (width : ℝ) (j : ℤ) :
    (scalarObservedHiddenBinPolynomial width j).totalDegree ≤ 3 := by
  unfold scalarObservedHiddenBinPolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  simp only [MvPolynomial.totalDegree_C, max_le_iff]
  constructor
  · apply (MvPolynomial.totalDegree_add _ _).trans
    simp only [max_le_iff]
    constructor
    · apply (MvPolynomial.totalDegree_add _ _).trans
      simp only [MvPolynomial.totalDegree_X, max_le_iff]
      constructor
      · omega
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by
        simp only [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X]
        omega)
  · omega

/-- Total degree at most three, uniformly in every integer bin and positive width. -/
theorem scalarObservedHiddenBinFormula_degree (width : ℝ) (j : ℤ) :
    (scalarObservedHiddenBinFormula width j).maxAtomDegree ≤ 3 := by
  exact max_le (scalarObservedHiddenBinPolynomial_degree width j)
    (scalarObservedHiddenBinPolynomial_degree width (j + 1))

/-- A produced complexity certificate for each actual scalar bin: six coordinates, two atoms,
and degree at most three. These bounds are uniform in the bin label and width. -/
noncomputable def scalarObservedHiddenBinBoundedTest (width : ℝ) (j : ℤ) :
    BoundedPolynomialTest 6 2 3 where
  variableCount := 6
  variableCount_le := le_rfl
  formula := scalarObservedHiddenBinFormula width j
  atomCount_le := (scalarObservedHiddenBinFormula_atomCount width j).le
  degree_le := scalarObservedHiddenBinFormula_degree width j

/-- The formula reads the actual floor bin, including both endpoint conventions. Width
positivity is explicit; no coefficient-height or finite-bin claim follows from this equation. -/
theorem scalarObservedHiddenBinFormula_mem_iff (width : ℝ) (hwidth : 0 < width)
    (j : ℤ) (p : ObservedBase .scalar × UnobservedFiber .scalar) :
    scalarObservedHiddenBinCoordinates p ∈ (scalarObservedHiddenBinFormula width j).models ↔
      observedFiberHiddenBin .scalar p.1 p.2 width = j := by
  rcases p with ⟨⟨t, y⟩, V, w0, w1, w2⟩
  simp only [scalarObservedHiddenBinFormula, PolynomialBooleanFormula.models,
    Set.mem_ofPred_eq, PolynomialBooleanFormula.Holds, scalarObservedHiddenBinPolynomial,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  change (0 ≤ w0 + t * w1 + t ^ 2 * w2 + -(j : ℝ) * width ∧
    ¬ 0 ≤ w0 + t * w1 + t ^ 2 * w2 + -((j + 1 : ℤ) : ℝ) * width) ↔
    Int.floor ((w0 + t * w1 + t ^ 2 * w2) / width) = j
  rw [Int.floor_eq_iff, le_div_iff₀ hwidth, div_lt_iff₀ hwidth]
  push_cast
  constructor <;> intro h <;> constructor <;> linarith

/-- Pulling back the two-atom formula is exactly the actual fixed-bin level set. -/
theorem scalarObservedHiddenBinFormula_preimage (width : ℝ) (hwidth : 0 < width) (j : ℤ) :
    scalarObservedHiddenBinCoordinates ⁻¹' (scalarObservedHiddenBinFormula width j).models =
      {p : ObservedBase .scalar × UnobservedFiber .scalar |
        observedFiberHiddenBin .scalar p.1 p.2 width = j} := by
  ext p
  exact scalarObservedHiddenBinFormula_mem_iff width hwidth j p

/-- Actual fiber-density consumer of the polynomial bin predicate. The full-coordinate density
and reference measures stay explicit, and this is the existing selected-bin pushforward. -/
theorem scalarObservedHiddenBinFormula_slice_baseMeasure_eq_withDensity
    (μ : Measure (ObservedBase .scalar)) (ν : Measure (UnobservedFiber .scalar))
    [SFinite μ] [SFinite ν]
    (density : ObservedBase .scalar × UnobservedFiber .scalar → ℝ≥0∞)
    (width : ℝ) (hwidth : 0 < width) (hdensity : Measurable density) (j : ℤ) :
    Measure.map Prod.fst
      ((μ.prod ν).withDensity
        ((scalarObservedHiddenBinCoordinates ⁻¹'
          (scalarObservedHiddenBinFormula width j).models).indicator density)) =
      μ.withDensity (fun base =>
        observedCoordinateHiddenBinSliceDensity .scalar ν density width (base, j)) := by
  rw [scalarObservedHiddenBinFormula_preimage width hwidth j]
  exact observedCoordinate_hiddenBinSlice_baseMeasure_eq_withDensity
    .scalar μ ν density width hdensity j


/-- Actual planar observed/fiber coordinates `(t,y0,y1,V0,V1,w00,w01,wV0,wV1)`. -/
def planarObservedHiddenBinCoordinates
    (p : ObservedBase .planar × UnobservedFiber .planar) : Fin 9 → ℝ :=
  ![p.1.1, p.1.2.ofLp 0, p.1.2.ofLp 1, p.2.1.ofLp 0, p.2.1.ofLp 1,
    p.2.2.1.ofLp 0, p.2.2.1.ofLp 1, p.2.2.2.ofLp 0, p.2.2.2.ofLp 1]

/-- Lower boundary polynomial in one actual planar hidden coordinate. -/
noncomputable def planarObservedHiddenBinPolynomial (width : ℝ) (i : Fin 2) (j : ℤ) :
    MvPolynomial (Fin 9) ℝ :=
  MvPolynomial.X (if i = 0 then 5 else 6) +
    MvPolynomial.X 0 * MvPolynomial.X (if i = 0 then 7 else 8) +
    MvPolynomial.C (-(j : ℝ) * width)

private noncomputable def planarObservedHiddenBinCoordinateFormula
    (width : ℝ) (i : Fin 2) (j : ℤ) : PolynomialBooleanFormula 9 :=
  .conjunction (.nonnegative (planarObservedHiddenBinPolynomial width i j))
    (.complement (.nonnegative (planarObservedHiddenBinPolynomial width i (j + 1))))

/-- The two actual half-open planar bin conditions, retaining both integer coordinates. -/
noncomputable def planarObservedHiddenBinFormula (width : ℝ) (j : Fin 2 → ℤ) :
    PolynomialBooleanFormula 9 :=
  .conjunction (planarObservedHiddenBinCoordinateFormula width 0 (j 0))
    (planarObservedHiddenBinCoordinateFormula width 1 (j 1))

/-- Every actual planar bin uses exactly four polynomial sign atoms. -/
theorem planarObservedHiddenBinFormula_atomCount (width : ℝ) (j : Fin 2 → ℤ) :
    (planarObservedHiddenBinFormula width j).atomCount = 4 := by
  rfl

private theorem planarObservedHiddenBinPolynomial_degree (width : ℝ) (i : Fin 2) (j : ℤ) :
    (planarObservedHiddenBinPolynomial width i j).totalDegree ≤ 2 := by
  unfold planarObservedHiddenBinPolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  simp only [MvPolynomial.totalDegree_C, max_le_iff]
  constructor
  · apply (MvPolynomial.totalDegree_add _ _).trans
    simp only [MvPolynomial.totalDegree_X, max_le_iff]
    constructor
    · omega
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · omega

/-- Each of the four atoms has degree at most two, uniformly in width and bin. -/
theorem planarObservedHiddenBinFormula_degree (width : ℝ) (j : Fin 2 → ℤ) :
    (planarObservedHiddenBinFormula width j).maxAtomDegree ≤ 2 := by
  change max (max _ _) (max _ _) ≤ 2
  exact max_le
    (max_le (planarObservedHiddenBinPolynomial_degree width 0 (j 0))
      (planarObservedHiddenBinPolynomial_degree width 0 (j 0 + 1)))
    (max_le (planarObservedHiddenBinPolynomial_degree width 1 (j 1))
      (planarObservedHiddenBinPolynomial_degree width 1 (j 1 + 1)))

/-- Produced planar bin complexity: nine real coordinates, four atoms, degree at most two. -/
noncomputable def planarObservedHiddenBinBoundedTest (width : ℝ) (j : Fin 2 → ℤ) :
    BoundedPolynomialTest 9 4 2 where
  variableCount := 9
  variableCount_le := le_rfl
  formula := planarObservedHiddenBinFormula width j
  atomCount_le := (planarObservedHiddenBinFormula_atomCount width j).le
  degree_le := planarObservedHiddenBinFormula_degree width j

private theorem planarObservedHiddenBinCoordinateFormula_holds_iff
    (width : ℝ) (hwidth : 0 < width) (i : Fin 2) (j : ℤ)
    (p : ObservedBase .planar × UnobservedFiber .planar) :
    (planarObservedHiddenBinCoordinateFormula width i j).Holds
      (planarObservedHiddenBinCoordinates p) ↔
      observedFiberHiddenBin .planar p.1 p.2 width i = j := by
  rcases p with ⟨⟨t, y⟩, V, w0, wV⟩
  simp only [planarObservedHiddenBinCoordinateFormula, PolynomialBooleanFormula.Holds,
    planarObservedHiddenBinPolynomial, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  have hcoords0 : planarObservedHiddenBinCoordinates ((t,y),V,w0,wV) 0 = t := rfl
  have hcoordsW : planarObservedHiddenBinCoordinates ((t,y),V,w0,wV)
      (if i = 0 then 5 else 6) = w0.ofLp i := by fin_cases i <;> rfl
  have hcoordsV : planarObservedHiddenBinCoordinates ((t,y),V,w0,wV)
      (if i = 0 then 7 else 8) = wV.ofLp i := by fin_cases i <;> rfl
  rw [hcoords0, hcoordsW, hcoordsV]
  change (0 ≤ w0.ofLp i + t * wV.ofLp i + -(j : ℝ) * width ∧
    ¬ 0 ≤ w0.ofLp i + t * wV.ofLp i + -((j + 1 : ℤ) : ℝ) * width) ↔
    Int.floor ((w0.ofLp i + t * wV.ofLp i) / width) = j
  rw [Int.floor_eq_iff, le_div_iff₀ hwidth, div_lt_iff₀ hwidth]
  push_cast
  constructor <;> intro h <;> constructor <;> linarith

/-- Polynomial syntax is exactly the actual planar floor-bin pair, for positive width. -/
theorem planarObservedHiddenBinFormula_mem_iff (width : ℝ) (hwidth : 0 < width)
    (j : Fin 2 → ℤ) (p : ObservedBase .planar × UnobservedFiber .planar) :
    planarObservedHiddenBinCoordinates p ∈ (planarObservedHiddenBinFormula width j).models ↔
      observedFiberHiddenBin .planar p.1 p.2 width = j := by
  change ((planarObservedHiddenBinCoordinateFormula width 0 (j 0)).Holds
    (planarObservedHiddenBinCoordinates p) ∧
    (planarObservedHiddenBinCoordinateFormula width 1 (j 1)).Holds
      (planarObservedHiddenBinCoordinates p)) ↔ _
  rw [planarObservedHiddenBinCoordinateFormula_holds_iff width hwidth,
    planarObservedHiddenBinCoordinateFormula_holds_iff width hwidth]
  exact (Fin.forall_fin_two.symm.trans funext_iff.symm)

/-- The actual planar fixed-bin level set is the pullback of its four-atom formula. -/
theorem planarObservedHiddenBinFormula_preimage (width : ℝ) (hwidth : 0 < width)
    (j : Fin 2 → ℤ) :
    planarObservedHiddenBinCoordinates ⁻¹' (planarObservedHiddenBinFormula width j).models =
      {p : ObservedBase .planar × UnobservedFiber .planar |
        observedFiberHiddenBin .planar p.1 p.2 width = j} := by
  ext p
  exact planarObservedHiddenBinFormula_mem_iff width hwidth j p

/-- The planar polynomial predicate feeds the actual existing fiber-density slice consumer. -/
theorem planarObservedHiddenBinFormula_slice_baseMeasure_eq_withDensity
    (μ : Measure (ObservedBase .planar)) (ν : Measure (UnobservedFiber .planar))
    [SFinite μ] [SFinite ν]
    (density : ObservedBase .planar × UnobservedFiber .planar → ℝ≥0∞)
    (width : ℝ) (hwidth : 0 < width) (hdensity : Measurable density) (j : Fin 2 → ℤ) :
    Measure.map Prod.fst
      ((μ.prod ν).withDensity
        ((planarObservedHiddenBinCoordinates ⁻¹'
          (planarObservedHiddenBinFormula width j).models).indicator density)) =
      μ.withDensity (fun base =>
        observedCoordinateHiddenBinSliceDensity .planar ν density width (base, j)) := by
  rw [planarObservedHiddenBinFormula_preimage width hwidth j]
  exact observedCoordinate_hiddenBinSlice_baseMeasure_eq_withDensity
    .planar μ ν density width hdensity j


/-- Finite interval containing every scalar bin of a hidden value in `[-M,M]`. -/
noncomputable def boundedScalarHiddenBins (M width : ℝ) : Finset ℤ :=
  Finset.Icc (Int.floor (-M / width)) (Int.floor (M / width))

/-- Exact finite interval cardinality, including possible empty intervals. -/
theorem boundedScalarHiddenBins_card (M width : ℝ) :
    (boundedScalarHiddenBins M width).card =
      (Int.floor (M / width) + 1 - Int.floor (-M / width)).toNat := by
  exact Int.card_Icc _ _

/-- Actual floor labels, including negative labels and boundary points, lie in this interval. -/
theorem hiddenBin_scalar_mem_boundedScalarHiddenBins (M width x : ℝ)
    (hwidth : 0 < width) (hx : |x| ≤ M) :
    hiddenBin .scalar x width ∈ boundedScalarHiddenBins M width := by
  change Int.floor (x / width) ∈ Finset.Icc (Int.floor (-M / width)) (Int.floor (M / width))
  apply Finset.mem_Icc.mpr
  exact ⟨Int.floor_mono ((div_le_div_iff_of_pos_right hwidth).mpr (abs_le.mp hx).1),
    Int.floor_mono ((div_le_div_iff_of_pos_right hwidth).mpr (abs_le.mp hx).2)⟩

/-- Explicit real cardinality bound, uniform over every hidden value in the stated range. -/
theorem boundedScalarHiddenBins_card_le (M width : ℝ) (hM : 0 ≤ M)
    (hwidth : 0 < width) :
    ((boundedScalarHiddenBins M width).card : ℝ) ≤ 2 * M / width + 2 := by
  have horder : Int.floor (-M / width) ≤ Int.floor (M / width) :=
    Int.floor_mono ((div_le_div_iff_of_pos_right hwidth).mpr (by linarith))
  have hcard : ((boundedScalarHiddenBins M width).card : ℝ) =
      (Int.floor (M / width) : ℝ) + 1 - (Int.floor (-M / width) : ℝ) := by
    exact_mod_cast (Int.card_Icc_of_le (a := Int.floor (-M / width))
      (b := Int.floor (M / width)) (by omega))
  rw [hcard]
  have hu := Int.floor_le (M / width)
  have hl := Int.lt_floor_add_one (-M / width)
  have hneg : -M / width = -(M / width) := neg_div _ _
  have htwo : 2 * M / width = 2 * (M / width) := by ring
  rw [htwo]
  linarith

/-- Finite box of both actual planar integer labels. -/
noncomputable def boundedPlanarHiddenBins (M width : ℝ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 2 => boundedScalarHiddenBins M width)

/-- The planar box cardinality is exactly the square of its scalar interval cardinality. -/
theorem boundedPlanarHiddenBins_card (M width : ℝ) :
    (boundedPlanarHiddenBins M width).card = (boundedScalarHiddenBins M width).card ^ 2 := by
  simp [boundedPlanarHiddenBins]

/-- Each coordinate of the actual planar floor label belongs to the finite box. -/
theorem hiddenBin_planar_mem_boundedPlanarHiddenBins (M width : ℝ) (x : E2)
    (hwidth : 0 < width) (hx : ∀ i : Fin 2, |x.ofLp i| ≤ M) :
    hiddenBin .planar x width ∈ boundedPlanarHiddenBins M width := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact hiddenBin_scalar_mem_boundedScalarHiddenBins M width (x.ofLp i) hwidth (hx i)

/-- Planar bin count, with the genuine square loss rather than a scalar estimate. -/
theorem boundedPlanarHiddenBins_card_le (M width : ℝ) (hM : 0 ≤ M)
    (hwidth : 0 < width) :
    ((boundedPlanarHiddenBins M width).card : ℝ) ≤ (2 * M / width + 2) ^ 2 := by
  rw [boundedPlanarHiddenBins_card, Nat.cast_pow]
  exact pow_le_pow_left₀ (by positivity) (boundedScalarHiddenBins_card_le M width hM hwidth) 2

/-- Dyadic upward rounding controls the inverse actual width by the requested inverse width. -/
theorem dyadicRoundedWidth_inv_le (requested : ℝ) (hrequested : 0 < requested) :
    (dyadicRoundedWidth requested)⁻¹ ≤ requested⁻¹ := by
  exact (inv_le_inv₀
    (hrequested.trans_le (requested_le_dyadicRoundedWidth requested hrequested)) hrequested).mpr
      (requested_le_dyadicRoundedWidth requested hrequested)

/-- The actual world-dependent observation width has an explicit reciprocal bound. -/
theorem observation_bin_width_inv_le (v : ModelVersion) {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData v) (γ : Fin worldCount) :
    (dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale v (worldData γ)))⁻¹ ≤
      worldDerivativeScale v (worldData γ) / seq.depthScale depth n := by
  simpa only [inv_div] using dyadicRoundedWidth_inv_le _
    (observation_requested_width_pos v seq depth n worldData γ)

/-- Real coefficient and time bounds produce a bound for the actual quadratic hidden value. -/
theorem scalar_hiddenAt_abs_le (l : ScalarTrajectory) (t R T : ℝ)
    (_hR : 0 ≤ R) (hT : 0 ≤ T) (ht : |t| ≤ T)
    (hw0 : |l.w0| ≤ R) (hw1 : |l.w1| ≤ R) (hw2 : |l.w2| ≤ R) :
    |(show ℝ from hiddenAt .scalar l t)| ≤ R * (1 + T + T ^ 2) := by
  change |l.w0 + t * l.w1 + t ^ 2 * l.w2| ≤ _
  calc
    _ ≤ |l.w0| + |t * l.w1| + |t ^ 2 * l.w2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ R + T * R + T ^ 2 * R := by
      rw [abs_mul, abs_mul, abs_pow]
      gcongr
    _ = R * (1 + T + T ^ 2) := by ring

/-- Real planar coefficient bounds produce each component of the actual affine hidden value. -/
theorem planar_hiddenAt_abs_le (l : PlanarTrajectory) (t R T : ℝ)
    (_hR : 0 ≤ R) (hT : 0 ≤ T) (ht : |t| ≤ T)
    (hw0 : ∀ i : Fin 2, |l.w0.ofLp i| ≤ R)
    (hwV : ∀ i : Fin 2, |l.wVelocity.ofLp i| ≤ R) (i : Fin 2) :
    |(hiddenAt .planar l t).ofLp i| ≤ R * (1 + T) := by
  change |l.w0.ofLp i + t * l.wVelocity.ofLp i| ≤ _
  calc
    _ ≤ |l.w0.ofLp i| + |t * l.wVelocity.ofLp i| := abs_add_le _ _
    _ ≤ R + T * R := by
      rw [abs_mul]
      exact add_le_add (hw0 i) (mul_le_mul ht (hwV i) (abs_nonneg _) hT)
    _ = R * (1 + T) := by ring

/-- The explicit scalar cube and unit-time support produce the hidden range without a caller
range certificate. This bound applies in particular to the existing two-copy half-time law. -/
theorem scalarCube_hiddenAt_abs_le_three (l : ScalarTrajectory) (t : ℝ)
    (hl : scalarTrajectoryFinMeasurableEquiv l ∈ scalarCoefficientCube)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(show ℝ from hiddenAt .scalar l t)| ≤ 3 := by
  change (∀ i, -1 ≤ scalarTrajectoryCoords l i) ∧
    (∀ i, scalarTrajectoryCoords l i ≤ 1) at hl
  have hc (i : Fin 5) : |scalarTrajectoryCoords l i| ≤ 1 := abs_le.mpr ⟨hl.1 i,hl.2 i⟩
  have hw0 : |l.w0| ≤ 1 := by simpa [scalarTrajectoryCoords] using hc 2
  have hw1 : |l.w1| ≤ 1 := by simpa [scalarTrajectoryCoords] using hc 3
  have hw2 : |l.w2| ≤ 1 := by simpa [scalarTrajectoryCoords] using hc 4
  have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  convert scalar_hiddenAt_abs_le l t 1 1 (by norm_num) (by norm_num) ht' hw0 hw1 hw2 using 1; norm_num

/-- A finite family containing the actual scalar-cube hidden label on the actual time support. -/
theorem scalarCube_hiddenBin_mem_boundedScalarHiddenBins (l : ScalarTrajectory) (t width : ℝ)
    (hwidth : 0 < width)
    (hl : scalarTrajectoryFinMeasurableEquiv l ∈ scalarCoefficientCube)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    hiddenBin .scalar (hiddenAt .scalar l t) width ∈ boundedScalarHiddenBins 3 width :=
  hiddenBin_scalar_mem_boundedScalarHiddenBins 3 width _ hwidth
    (scalarCube_hiddenAt_abs_le_three l t hl ht)


/-- The finite scalar family at the genuine world-dependent width has a bound in the actual
scale and derivative factor; the threshold is not reintroduced as a caller certificate. -/
theorem observation_boundedScalarHiddenBins_card_le (v : ModelVersion) {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData v) (γ : Fin worldCount)
    (M : ℝ) (hM : 0 ≤ M) :
    ((boundedScalarHiddenBins M (dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale v (worldData γ)))).card : ℝ) ≤
      2 * M * (worldDerivativeScale v (worldData γ) / seq.depthScale depth n) + 2 := by
  apply (boundedScalarHiddenBins_card_le M _ hM
    (observation_bin_width_pos v seq depth n worldData γ)).trans
  have hmul := mul_le_mul_of_nonneg_left
    (observation_bin_width_inv_le v seq depth n worldData γ) (by positivity : 0 ≤ 2 * M)
  simpa only [div_eq_mul_inv] using add_le_add hmul (le_refl (2 : ℝ))

/-- The actual constructed coordinate prior is concentrated on its defining cube. -/
theorem scalarCubeCoordinatePrior_ae_mem_cube :
    ∀ᵐ x ∂scalarCubeCoordinatePrior, x ∈ scalarCoefficientCube := by
  rw [scalarCubeCoordinatePrior, ae_withDensity_iff scalarCubeDensity_measurable]
  filter_upwards [] with x hx
  by_contra hnot
  simp [scalarCubeDensity, hnot] at hx

/-- Concentration of the actual trajectory prior, transported through its genuine chart. -/
theorem scalarCubeTrajectoryPrior_ae_mem_cube :
    ∀ᵐ l ∂scalarCubeTrajectoryPrior,
      scalarTrajectoryFinMeasurableEquiv l ∈ scalarCoefficientCube := by
  rw [scalarCubeTrajectoryPrior, ae_map_iff
    scalarTrajectoryFinMeasurableEquiv.symm.measurable.aemeasurable
    (scalarCoefficientCube_measurable.preimage scalarTrajectoryFinMeasurableEquiv.measurable)]
  simpa using scalarCubeCoordinatePrior_ae_mem_cube

/-- The actual coefficient-cube product time law produces the hidden range almost everywhere,
without a bounded-support certificate supplied by the caller. -/
theorem scalarCube_product_ae_hiddenAt_abs_le_three :
    ∀ᵐ p ∂scalarCubeTrajectoryPrior.prod unitTimeMeasure,
      |(show ℝ from hiddenAt .scalar p.1 p.2)| ≤ 3 := by
  let : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
  have hrect : MeasurableSet {p : ScalarTrajectory × ℝ |
      scalarTrajectoryFinMeasurableEquiv p.1 ∈ scalarCoefficientCube ∧
        p.2 ∈ Set.Icc (0 : ℝ) 1} :=
    (scalarCoefficientCube_measurable.preimage
      (scalarTrajectoryFinMeasurableEquiv.measurable.comp measurable_fst)).inter
      (measurableSet_Icc.preimage measurable_snd)
  have ha : ∀ᵐ p ∂scalarCubeTrajectoryPrior.prod unitTimeMeasure,
      scalarTrajectoryFinMeasurableEquiv p.1 ∈ scalarCoefficientCube ∧
        p.2 ∈ Set.Icc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae hrect).mpr
    filter_upwards [scalarCubeTrajectoryPrior_ae_mem_cube] with l hl
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
    exact ⟨hl,ht⟩
  filter_upwards [ha] with p hp
  exact scalarCube_hiddenAt_abs_le_three p.1 p.2 hp.1 hp.2

/-- Any incidence restriction of the actual cube product law, including each actual half-time
copy, retains a finite bin support at the actual world width. No event mass is renormalized. -/
theorem scalarCube_selected_ae_observationAt_bin_mem {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData .scalar) (γ : Fin worldCount)
    (event : Set (ScalarTrajectory × ℝ)) :
    ∀ᵐ p ∂(scalarCubeTrajectoryPrior.prod unitTimeMeasure).restrict event,
      (observationAt .scalar seq depth n worldData γ p.1 p.2).2.2.2 ∈
        boundedScalarHiddenBins 3 (dyadicRoundedWidth
          (seq.depthScale depth n / worldDerivativeScale .scalar (worldData γ))) := by
  filter_upwards [ae_restrict_of_ae (s := event) scalarCube_product_ae_hiddenAt_abs_le_three]
    with p hp
  exact hiddenBin_scalar_mem_boundedScalarHiddenBins 3 _ _
    (observation_bin_width_pos .scalar seq depth n worldData γ) hp


/-- Each actual half-time copy's selected base/bin law is concentrated on the finite family at
that same copy's genuine width. The prior support is proved internally, not supplied as data. -/
theorem scalarCubeTwoCopyHalfTimeSelection_baseBinLaw_ae_finiteBins
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar)
    (γ : Fin 1) (i : Fin 2) :
    ∀ᵐ z ∂selectedObservationBaseBinLaw
      (scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i)
      seq depth n (fun _ => worldData γ i)
      (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex γ i),
      z.2 ∈ boundedScalarHiddenBins 3 (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale .scalar (worldData γ i))) := by
  let bins := boundedScalarHiddenBins 3 (dyadicRoundedWidth
    (seq.depthScale depth n / worldDerivativeScale .scalar (worldData γ i)))
  have hbins : MeasurableSet (bins : Set ℤ) := bins.finite_toSet.measurableSet
  erw [selectedObservationBaseBinLaw_eq_map_observationPushforward]
  erw [ae_map_iff (observationDataToBaseBin_measurable .scalar).aemeasurable
    (hbins.preimage measurable_snd)]
  erw [observationPushforward, ae_map_iff
    (observationAt_measurable .scalar seq depth n
      (fun _ => worldData γ i)
      (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex γ i)).aemeasurable
    (hbins.preimage (measurable_snd.snd.snd))]
  exact scalarCube_selected_ae_observationAt_bin_mem seq depth n
    (fun _ : Fin 1 => worldData γ i) (0 : Fin 1) scalarHalfTimeEvent


/-- A finite tagged mixture preserves any almost-everywhere right-coordinate property of
all components, with the original finite nonnegative weights and arbitrary zero masses. -/
theorem finiteTaggedMeasure_ae_right {ι α : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace α]
    (weight : ι → ℝ≥0) (law : ι → Measure α) [∀ i, SFinite (law i)]
    (p : α → Prop) (hp : MeasurableSet {x | p x}) (h : ∀ i, ∀ᵐ x ∂law i, p x) :
    ∀ᵐ z ∂finiteTaggedMeasure (fun i => (weight i : ℝ≥0∞)) law, p z.2 := by
  rw [finiteTaggedMeasure, Measure.ae_sum_iff]
  intro i
  rw [Measure.dirac_prod]
  exact (ae_map_iff measurable_prodMk_left.aemeasurable
    (hp.preimage (measurable_snd : Measurable (Prod.snd : ι × α → α)))).mpr
      (Measure.ae_smul_measure (h i) (weight i : ℝ≥0∞))

/-- The scalar model has derivative scale exactly one; this is the same genuine bin family at
each copy, even when the two actual world-data inputs differ. -/
noncomputable def scalarCubeFiniteHiddenBins (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) : Finset ℤ :=
  boundedScalarHiddenBins 3 (dyadicRoundedWidth (seq.depthScale depth n))

/-- The common scalar family coincides with each actual copy's world-dependent width formula. -/
theorem scalarCubeFiniteHiddenBins_eq_copyBins (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) (worldData : VersionWorldData .scalar) :
    scalarCubeFiniteHiddenBins seq depth n = boundedScalarHiddenBins 3
      (dyadicRoundedWidth (seq.depthScale depth n / worldDerivativeScale .scalar worldData)) := by
  simp [scalarCubeFiniteHiddenBins, worldDerivativeScale]

/-- Uniform finite-scale scalar bin count, independent of the copy and actual cube trajectory. -/
theorem scalarCubeFiniteHiddenBins_card_le (seq : ExactSequence) (depth : Depth seq) (n : ℕ) :
    ((scalarCubeFiniteHiddenBins seq depth n).card : ℝ) ≤ 6 / seq.depthScale depth n + 2 := by
  have h := boundedScalarHiddenBins_card_le 3 (dyadicRoundedWidth (seq.depthScale depth n))
    (by norm_num) ((seq.depthScale_pos depth n).trans_le
      (requested_le_dyadicRoundedWidth _ (seq.depthScale_pos depth n)))
  have hinv := mul_le_mul_of_nonneg_left
    (dyadicRoundedWidth_inv_le _ (seq.depthScale_pos depth n)) (by norm_num : 0 ≤ (6 : ℝ))
  apply h.trans
  norm_num only [show (2 : ℝ) * 3 = 6 by norm_num]
  simpa only [div_eq_mul_inv] using add_le_add hinv (le_refl (2 : ℝ))

/-- Restricting each actual selected copy to its finite hidden-bin support leaves its complete
base/bin law unchanged; no density or normalization assumption is used. -/
theorem scalarCubeTwoCopyHalfTimeSelection_baseBinLaw_restrict_finiteBins
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar)
    (γ : Fin 1) (i : Fin 2) :
    (selectedObservationBaseBinLaw
      (scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i) seq depth n
      (fun _ => worldData γ i) (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex γ i)).restrict
      {z : ObservedBase .scalar × HiddenBin .scalar |
        z.2 ∈ scalarCubeFiniteHiddenBins seq depth n} =
      selectedObservationBaseBinLaw
        (scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i) seq depth n
        (fun _ => worldData γ i) (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex γ i) := by
  apply Measure.restrict_eq_self_of_ae_mem
  erw [scalarCubeFiniteHiddenBins_eq_copyBins seq depth n (worldData γ i)]
  convert scalarCubeTwoCopyHalfTimeSelection_baseBinLaw_ae_finiteBins seq depth n worldData γ i using 1
  rfl

/-- The real world/copy weighted joint law is supported on the finite bins. The distinct copy
indices, actual events, time/space variables and original weights are all retained. -/
theorem scalarCubeTwoCopyHalfTimeSelection_jointLaw_ae_finiteBins
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    ∀ᵐ z ∂worldCopyObservationBaseBinLaw scalarCubeTwoCopyHalfTimeSelection seq depth n worldData,
      z.2.2 ∈ scalarCubeFiniteHiddenBins seq depth n := by
  let I := scalarCubeTwoCopyHalfTimeSelection
  let law := fun q : WorldTrajectoryCopyIndex I.worldCount I.copyCount =>
    selectedObservationBaseBinLaw (I.singletonSelection q.world q.copy) seq depth n
      (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy)
  let : ∀ q, SFinite (law q) := by
    intro q
    let S := I.singletonSelection q.world q.copy
    let γ₀ := I.singletonWorldIndex q.world q.copy
    let : IsProbabilityMeasure (S.priors.prior γ₀) := S.priors.prior_isProbability γ₀
    let : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
    let : SFinite (S.measure γ₀) := by
      dsimp [IncidenceSelection.measure, WorldPriorSystem.selectedIncidenceMeasure,
        WorldPriorSystem.productIncidenceMeasure]
      infer_instance
    change SFinite (selectedObservationBaseBinLaw S seq depth n (fun _ => worldData q.world q.copy) γ₀)
    unfold selectedObservationBaseBinLaw
    infer_instance
  have hmeas : MeasurableSet {x : ObservedBase .scalar × HiddenBin .scalar |
      x.2 ∈ scalarCubeFiniteHiddenBins seq depth n} :=
    (scalarCubeFiniteHiddenBins seq depth n).finite_toSet.measurableSet.preimage measurable_snd
  apply finiteTaggedMeasure_ae_right
    (fun q => I.worldWeight q.world * I.copyWeight q.world q.copy) law
    (fun x => x.2 ∈ scalarCubeFiniteHiddenBins seq depth n) hmeas
  intro q
  dsimp only [law, I]
  erw [scalarCubeFiniteHiddenBins_eq_copyBins seq depth n (worldData q.world q.copy)]
  convert scalarCubeTwoCopyHalfTimeSelection_baseBinLaw_ae_finiteBins seq depth n worldData q.world q.copy using 1

/-- The finite-bin restriction is exactly the same original weighted joint measure. -/
theorem scalarCubeTwoCopyHalfTimeSelection_jointLaw_restrict_finiteBins
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    (worldCopyObservationBaseBinLaw scalarCubeTwoCopyHalfTimeSelection seq depth n worldData).restrict
      {z | z.2.2 ∈ scalarCubeFiniteHiddenBins seq depth n} =
      worldCopyObservationBaseBinLaw scalarCubeTwoCopyHalfTimeSelection seq depth n worldData := by
  exact Measure.restrict_eq_self_of_ae_mem
    (scalarCubeTwoCopyHalfTimeSelection_jointLaw_ae_finiteBins seq depth n worldData)

/-- The actual finite-bin weighted joint law retains the original unnormalized half-time mass. -/
theorem scalarCubeTwoCopyHalfTimeSelection_jointLaw_restrict_finiteBins_mass
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    ((worldCopyObservationBaseBinLaw scalarCubeTwoCopyHalfTimeSelection seq depth n worldData).restrict
      {z | z.2.2 ∈ scalarCubeFiniteHiddenBins seq depth n}) Set.univ =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [scalarCubeTwoCopyHalfTimeSelection_jointLaw_restrict_finiteBins]
  erw [worldCopyObservationBaseBinLaw_univ]
  exact scalarCubeTwoCopyHalfTimeSelection_weightedEventMass_eq_half


/-- A finite bin support of an actual product-reference density implies an almost-everywhere
finite-sum formula on the base. No pointwise density support is inferred from law support. -/
theorem finiteBinDensity_sum_eq_tsum_ae {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (μ : Measure α) (density : α × β → ℝ≥0∞) (hdensity : Measurable density)
    (bins : Finset β)
    (hsupport : ∀ᵐ z ∂(μ.prod (Measure.count : Measure β)).withDensity density,
      z.2 ∈ bins) :
    ∀ᵐ x ∂μ, (∑ j ∈ bins, density (x,j)) = ∑' j, density (x,j) := by
  have hz : ∀ᵐ z ∂μ.prod (Measure.count : Measure β),
      z.2 ∉ bins → density z = 0 := by
    have h := (ae_withDensity_iff hdensity).mp hsupport
    filter_upwards [h] with z hz hout
    by_contra hne
    exact hout (hz hne)
  have hrows := Measure.ae_ae_of_ae_prod hz
  filter_upwards [hrows] with x hx
  have hall : ∀ j : β, j ∉ bins → density (x,j) = 0 := Measure.ae_count_iff.mp hx
  exact (tsum_eq_sum hall).symm

/-- Density certificates produced from the already accepted actual two-copy cube family. -/
noncomputable def scalarCubeTwoCopyActualDensityCertificates (seq : ExactSequence) (n : ℕ) :
    ∀ γ i, TrajectoryPriorDensityCertificates .scalar
      (scalarCubeTwoCopyHalfTimeSelection.singletonPriors γ i) :=
  fun γ i => (scalarCubeTwoCopyTemperedFamily seq).trajectoryDensityCertificate
    (fun _ => scalarCubeTwoCopyHalfTimeSelection) seq
    (fun _ _ _ => 2) (fun _ _ _ => 10)
    (fun _ _ _ => ENNReal.ofReal (1 / 32 : ℝ)) 5 1 n γ i

/-- Actual two-copy finite bin density sum, retaining original world/copy weights. The
certificate is produced internally; equality is with respect to the actual base reference. -/
theorem scalarCubeTwoCopyHalfTimeSelection_finiteBinDensity_sum_ae
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar)
    (q : WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2)) :
    ∀ᵐ base ∂observedBaseReference .scalar,
      (∑ j ∈ scalarCubeFiniteHiddenBins seq depth n,
        worldCopyObservationBaseBinDensity scalarCubeTwoCopyHalfTimeSelection
          (scalarCubeTwoCopyActualDensityCertificates seq n) seq depth n worldData (q,(base,j))) =
      worldCopyObservationBaseDensity scalarCubeTwoCopyHalfTimeSelection
        (scalarCubeTwoCopyActualDensityCertificates seq n) (q,base) := by
  let I := scalarCubeTwoCopyHalfTimeSelection
  let C := scalarCubeTwoCopyActualDensityCertificates seq n
  let S := I.singletonSelection q.world q.copy
  let γ₀ := I.singletonWorldIndex q.world q.copy
  let fullDensity := selectedObservedCoordinateDensity S (C q.world q.copy) γ₀
  let width := dyadicRoundedWidth
    (seq.depthScale depth n / worldDerivativeScale .scalar (worldData q.world q.copy))
  let density := observedCoordinateHiddenBinSliceDensity .scalar
    (unobservedFiberReference .scalar) fullDensity width
  let : SFinite (unobservedFiberReference .scalar) := by
    dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
      UnobservedFiber, ScalarUnobservedFiber]
    infer_instance
  have hdensity : Measurable density :=
    observedCoordinateHiddenBinSliceDensity_measurable .scalar _ _ _
      (selectedObservedCoordinateDensity_measurable S (C q.world q.copy) γ₀)
  have hsupport : ∀ᵐ z ∂((observedBaseReference .scalar).prod
      (Measure.count : Measure (HiddenBin .scalar))).withDensity density,
      z.2 ∈ scalarCubeFiniteHiddenBins seq depth n := by
    have h := scalarCubeTwoCopyHalfTimeSelection_baseBinLaw_ae_finiteBins
      seq depth n worldData q.world q.copy
    erw [S.selectedObservationBaseBinLaw_eq_withDensity (C q.world q.copy)
      seq depth n (fun _ => worldData q.world q.copy) γ₀] at h
    erw [scalarCubeFiniteHiddenBins_eq_copyBins seq depth n (worldData q.world q.copy)]
    convert h using 1
  have hfinite := finiteBinDensity_sum_eq_tsum_ae (observedBaseReference .scalar)
    density hdensity (scalarCubeFiniteHiddenBins seq depth n) hsupport
  filter_upwards [hfinite] with base hbase
  let w : ℝ≥0∞ := ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞)
  have hweighted : (∑ j ∈ scalarCubeFiniteHiddenBins seq depth n, w * density (base,j)) =
      ∑' j, w * density (base,j) := by
    erw [← Finset.mul_sum, hbase, ENNReal.tsum_mul_left]
  calc
    _ = ∑' j, worldCopyObservationBaseBinDensity I C seq depth n worldData (q,(base,j)) := by
      exact hweighted
    _ = _ := tsum_worldCopyObservationBaseBinDensity_eq_baseDensity I C seq depth n worldData q base


/-- One integer exponent fixed before all legal depths and all sequence indices controls every
inverse depth scale. This is a genuine all-index estimate, independent of F-001 semantics. -/
theorem ExactSequence.depthScale_inv_le_resolution_pow_lengthCeil (seq : ExactSequence)
    (depth : Depth seq) (n : ℕ) :
    (seq.depthScale depth n)⁻¹ ≤ seq.resolution n ^ Nat.ceil seq.length := by
  have hN : 0 ≤ seq.resolution n := le_trans zero_le_one (seq.resolution_ge_one n)
  have hdepth : depth.value ≤ (Nat.ceil seq.length : ℝ) :=
    depth.value_le_length.trans (Nat.le_ceil _)
  calc
    (seq.depthScale depth n)⁻¹ = seq.resolution n ^ depth.value := by
      simp [ExactSequence.depthScale, ExactSequence.scale, Real.rpow_neg hN]
    _ ≤ seq.resolution n ^ (Nat.ceil seq.length : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (seq.resolution_ge_one n) hdepth
    _ = _ := Real.rpow_natCast _ _

/-- All actual scalar-cube bin counts have the same coefficient eight and length-ceiling
exponent, uniformly over every legal depth and every index. -/
theorem scalarCubeFiniteHiddenBins_uniform_card_bound (seq : ExactSequence)
    (depth : Depth seq) (n : ℕ) :
    ((scalarCubeFiniteHiddenBins seq depth n).card : ℝ) ≤
      8 * seq.resolution n ^ Nat.ceil seq.length := by
  have h := scalarCubeFiniteHiddenBins_card_le seq depth n
  have hinv := mul_le_mul_of_nonneg_left
    (seq.depthScale_inv_le_resolution_pow_lengthCeil depth n) (by norm_num : 0 ≤ (6 : ℝ))
  have hpow : (1 : ℝ) ≤ seq.resolution n ^ Nat.ceil seq.length :=
    one_le_pow₀ (seq.resolution_ge_one n)
  rw [div_eq_mul_inv] at h
  linarith

/-- A polynomial complexity certificate produced from the actual finite-bin family. -/
noncomputable def scalarCubeFiniteHiddenBins_polynomiallyBounded
    (seq : ExactSequence) (depth : Depth seq) :
    PolynomiallyBoundedNatAlong seq (fun n => (scalarCubeFiniteHiddenBins seq depth n).card) where
  coefficient := 8
  exponent := Nat.ceil seq.length
  bound := scalarCubeFiniteHiddenBins_uniform_card_bound seq depth

/-- With an explicit uniform derivative bound, scalar-bin counts at actual per-index world
widths have a uniform all-depth polynomial bound. No bound on arbitrary world data is inferred. -/
theorem observation_scalarBins_uniform_card_bound
    (v : ModelVersion) {worldCount : ℕ} (seq : ExactSequence)
    (worldData : ℕ → Fin worldCount → VersionWorldData v)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hworld : ∀ n γ, worldDerivativeScale v (worldData n γ) ≤ B)
    (depth : Depth seq) (n : ℕ) (γ : Fin worldCount) :
    ((boundedScalarHiddenBins M (dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale v (worldData n γ)))).card : ℝ) ≤
      (2 * M * B + 2) * seq.resolution n ^ Nat.ceil seq.length := by
  have hcount := observation_boundedScalarHiddenBins_card_le v seq depth n (worldData n) γ M hM
  have hD : worldDerivativeScale v (worldData n γ) / seq.depthScale depth n ≤
      B * seq.resolution n ^ Nat.ceil seq.length := by
    calc
      _ ≤ B / seq.depthScale depth n :=
        (div_le_div_iff_of_pos_right (seq.depthScale_pos depth n)).mpr (hworld n γ)
      _ ≤ _ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (seq.depthScale_inv_le_resolution_pow_lengthCeil depth n) hB
  have hmul := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 2 * M)
  have hpow : (1 : ℝ) ≤ seq.resolution n ^ Nat.ceil seq.length :=
    one_le_pow₀ (seq.resolution_ge_one n)
  nlinarith

/-- The planar integer-box count retains the square and doubled polynomial exponent, with
all support-radius and derivative hypotheses explicit and fixed before depth/index/world. -/
theorem observation_planarBins_uniform_card_bound
    (v : ModelVersion) {worldCount : ℕ} (seq : ExactSequence)
    (worldData : ℕ → Fin worldCount → VersionWorldData v)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hworld : ∀ n γ, worldDerivativeScale v (worldData n γ) ≤ B)
    (depth : Depth seq) (n : ℕ) (γ : Fin worldCount) :
    ((boundedPlanarHiddenBins M (dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale v (worldData n γ)))).card : ℝ) ≤
      (2 * M * B + 2) ^ 2 * seq.resolution n ^ (2 * Nat.ceil seq.length) := by
  rw [boundedPlanarHiddenBins_card, Nat.cast_pow]
  have h := observation_scalarBins_uniform_card_bound v seq worldData M B hM hB hworld depth n γ
  have hsq := pow_le_pow_left₀ (by positivity) h 2
  apply hsq.trans_eq
  rw [mul_pow, ← pow_mul]
  congr 1
  congr 1
  omega


/-- Explicit scalar coefficient support propagates through the actual independent unit-time
law; bounded hidden support is proved rather than assumed. -/
theorem scalarPrior_product_ae_hiddenAt_abs_le (prior : Measure ScalarTrajectory)
    (R : ℝ) (hR : 0 ≤ R)
    (hcoeff : ∀ᵐ l ∂prior, |l.w0| ≤ R ∧ |l.w1| ≤ R ∧ |l.w2| ≤ R) :
    ∀ᵐ p ∂prior.prod unitTimeMeasure,
      |(show ℝ from hiddenAt .scalar p.1 p.2)| ≤ 3 * R := by
  let : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
  have hc := (Measure.quasiMeasurePreserving_fst (μ := prior) (ν := unitTimeMeasure)).ae hcoeff
  have ht := (Measure.quasiMeasurePreserving_snd (μ := prior) (ν := unitTimeMeasure)).ae
    (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc)
  filter_upwards [hc,ht] with p hp htime
  have habs : |p.2| ≤ 1 := by rw [abs_of_nonneg htime.1]; exact htime.2
  convert scalar_hiddenAt_abs_le p.1 p.2 R 1 hR (by norm_num) habs hp.1 hp.2.1 hp.2.2 using 1
  ring

/-- Explicit planar coefficient support propagates through unit time componentwise, retaining
both hidden coordinates and the original measure. No boundedness of arbitrary priors is claimed. -/
theorem planarPrior_product_ae_hiddenAt_abs_le (prior : Measure PlanarTrajectory)
    (R : ℝ) (hR : 0 ≤ R)
    (hcoeff : ∀ᵐ l ∂prior, ∀ i : Fin 2,
      |l.w0.ofLp i| ≤ R ∧ |l.wVelocity.ofLp i| ≤ R) :
    ∀ᵐ p ∂prior.prod unitTimeMeasure, ∀ i : Fin 2,
      |(hiddenAt .planar p.1 p.2).ofLp i| ≤ 2 * R := by
  let : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
  have hc := (Measure.quasiMeasurePreserving_fst (μ := prior) (ν := unitTimeMeasure)).ae hcoeff
  have ht := (Measure.quasiMeasurePreserving_snd (μ := prior) (ν := unitTimeMeasure)).ae
    (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc)
  filter_upwards [hc,ht] with p hp htime
  intro i
  have habs : |p.2| ≤ 1 := by rw [abs_of_nonneg htime.1]; exact htime.2
  convert planar_hiddenAt_abs_le p.1 p.2 R 1 hR (by norm_num) habs
    (fun j => (hp j).1) (fun j => (hp j).2) i using 1
  ring

/-- A general actual planar selection obtains finite-bin support from explicit prior coefficient
bounds, at its own genuine dyadic observation width; no hidden-range certificate is assumed. -/
theorem IncidenceSelection.planar_baseBinLaw_ae_finiteBins_of_ae_coeffBounds
    (I : @IncidenceSelection .planar (instMeasurableSpaceTrajectory .planar))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData .planar)
    (γ : Fin I.priors.worldCount) (R : ℝ) (hR : 0 ≤ R)
    (hcoeff : ∀ᵐ l ∂I.priors.prior γ, ∀ i : Fin 2,
      |l.w0.ofLp i| ≤ R ∧ |l.wVelocity.ofLp i| ≤ R) :
    ∀ᵐ z ∂selectedObservationBaseBinLaw I seq depth n worldData γ,
      z.2 ∈ boundedPlanarHiddenBins (2 * R) (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale .planar (worldData γ))) := by
  let width := dyadicRoundedWidth
    (seq.depthScale depth n / worldDerivativeScale .planar (worldData γ))
  let bins := boundedPlanarHiddenBins (2 * R) width
  have hbins : MeasurableSet (bins : Set (Fin 2 → ℤ)) := bins.finite_toSet.measurableSet
  erw [selectedObservationBaseBinLaw_eq_map_observationPushforward]
  erw [ae_map_iff (observationDataToBaseBin_measurable .planar).aemeasurable
    (hbins.preimage measurable_snd)]
  erw [observationPushforward, ae_map_iff
    (observationAt_measurable .planar seq depth n worldData γ).aemeasurable
    (hbins.preimage measurable_snd.snd.snd)]
  have hprod := planarPrior_product_ae_hiddenAt_abs_le (I.priors.prior γ) R hR hcoeff
  have hselected := ae_restrict_of_ae (s := I.event γ) hprod
  dsimp only [IncidenceSelection.measure, WorldPriorSystem.selectedIncidenceMeasure,
    WorldPriorSystem.productIncidenceMeasure]
  filter_upwards [hselected] with p hp
  exact hiddenBin_planar_mem_boundedPlanarHiddenBins (2 * R) width _
    (observation_bin_width_pos .planar seq depth n worldData γ) hp

/-- The scalar counterpart produces finite-bin support from the stated original-prior
coefficient bounds and real event restriction, with no density hypothesis. -/
theorem IncidenceSelection.scalar_baseBinLaw_ae_finiteBins_of_ae_coeffBounds
    (I : @IncidenceSelection .scalar (instMeasurableSpaceTrajectory .scalar))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData .scalar)
    (γ : Fin I.priors.worldCount) (R : ℝ) (hR : 0 ≤ R)
    (hcoeff : ∀ᵐ l ∂I.priors.prior γ, |l.w0| ≤ R ∧ |l.w1| ≤ R ∧ |l.w2| ≤ R) :
    ∀ᵐ z ∂selectedObservationBaseBinLaw I seq depth n worldData γ,
      z.2 ∈ boundedScalarHiddenBins (3 * R) (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale .scalar (worldData γ))) := by
  let width := dyadicRoundedWidth
    (seq.depthScale depth n / worldDerivativeScale .scalar (worldData γ))
  let bins := boundedScalarHiddenBins (3 * R) width
  have hbins : MeasurableSet (bins : Set ℤ) := bins.finite_toSet.measurableSet
  erw [selectedObservationBaseBinLaw_eq_map_observationPushforward]
  erw [ae_map_iff (observationDataToBaseBin_measurable .scalar).aemeasurable
    (hbins.preimage measurable_snd)]
  erw [observationPushforward, ae_map_iff
    (observationAt_measurable .scalar seq depth n worldData γ).aemeasurable
    (hbins.preimage measurable_snd.snd.snd)]
  have hprod := scalarPrior_product_ae_hiddenAt_abs_le (I.priors.prior γ) R hR hcoeff
  have hselected := ae_restrict_of_ae (s := I.event γ) hprod
  dsimp only [IncidenceSelection.measure, WorldPriorSystem.selectedIncidenceMeasure,
    WorldPriorSystem.productIncidenceMeasure]
  filter_upwards [hselected] with p hp
  exact hiddenBin_scalar_mem_boundedScalarHiddenBins (3 * R) width _
    (observation_bin_width_pos .scalar seq depth n worldData γ) hp


/-- With a finite tag, a base-a.e. property on every tag is a.e. on the count-product
reference. Measurable embeddings avoid any unjustified pointwise or measurability upgrade. -/
theorem ae_count_prod_of_forall_ae {ι α : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (p : ι × α → Prop) (h : ∀ i, ∀ᵐ x ∂μ, p (i,x)) :
    ∀ᵐ z ∂(Measure.count : Measure ι).prod μ, p z := by
  have hc : (Measure.count : Measure ι) = Measure.sum (fun i : ι => Measure.dirac i) := by
    symm
    simpa using (Measure.sum_smul_dirac (Measure.count : Measure ι))
  rw [hc, Measure.prod_sum_left, Measure.ae_sum_iff]
  intro i
  rw [Measure.dirac_prod]
  exact (measurableEmbedding_prodMk_left i).ae_map_iff.mpr (h i)

/-- The finite-bin density integrated over the actual count(world-copy) times base reference
has the exact original unnormalized half-time mass. No bin, copy or weight is dropped. -/
theorem scalarCubeTwoCopyHalfTimeSelection_finiteBinDensityIntegral_eq_half
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    ∫⁻ p, (∑ j ∈ scalarCubeFiniteHiddenBins seq depth n,
      worldCopyObservationBaseBinDensity scalarCubeTwoCopyHalfTimeSelection
        (scalarCubeTwoCopyActualDensityCertificates seq n) seq depth n worldData (p.1,(p.2,j))) ∂
      ((Measure.count : Measure (WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2))).prod
        (observedBaseReference .scalar)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  let : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
  let : SFinite (observedBaseReference .scalar) := by
    dsimp [observedBaseReference, scalarObservedBaseReference, ObservedBase, ScalarObservedBase]
    infer_instance
  have hae := ae_count_prod_of_forall_ae (observedBaseReference .scalar)
    (fun p : WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2) × ObservedBase .scalar =>
      (∑ j ∈ scalarCubeFiniteHiddenBins seq depth n,
        worldCopyObservationBaseBinDensity scalarCubeTwoCopyHalfTimeSelection
          (scalarCubeTwoCopyActualDensityCertificates seq n) seq depth n worldData (p.1,(p.2,j))) =
        worldCopyObservationBaseDensity scalarCubeTwoCopyHalfTimeSelection
          (scalarCubeTwoCopyActualDensityCertificates seq n) p)
    (fun q => scalarCubeTwoCopyHalfTimeSelection_finiteBinDensity_sum_ae seq depth n worldData q)
  calc
    _ = ∫⁻ p, worldCopyObservationBaseDensity scalarCubeTwoCopyHalfTimeSelection
        (scalarCubeTwoCopyActualDensityCertificates seq n) p ∂
        ((Measure.count : Measure (WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2))).prod
          (observedBaseReference .scalar)) := lintegral_congr_ae hae
    _ = scalarCubeTwoCopyHalfTimeSelection.weightedEventMass :=
      worldCopyObservationBaseDensity_lintegral_eq_weightedEventMass scalarCubeTwoCopyHalfTimeSelection
        (scalarCubeTwoCopyActualDensityCertificates seq n) seq depth n worldData
    _ = ENNReal.ofReal (1 / 2 : ℝ) := scalarCubeTwoCopyHalfTimeSelection_weightedEventMass_eq_half

end Kakeya4.Framework
