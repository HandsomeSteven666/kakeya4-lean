import Experiments.FiniteBins.SelectedSourceSemialgebraic
import Experiments.FiniteBins.FiniteHiddenBinCopyComplexity

/-!
# Complete finite source-bin partitions for the actual scalar selected law

Index zero is the source complement, including all zero-density points. Every other index is
the original source intersected with a genuine half-open bin. The reference is kept as the
original observed-base/fiber product, including its unit-time restriction.
-/
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace Kakeya4.Framework

/-- The actual finite partition formulas, with exactly one extra zero-density piece. -/
noncomputable def scalarSelectedSourceBinPartitionFormula (width : ℝ) :
    Fin ((boundedScalarHiddenBins 3 width).card + 1) → PolynomialBooleanFormula 6 :=
  Fin.cases (.complement scalarObservedSelectedSourceFormula)
    (fun i => scalarSelectedSourceBinFormula width
      (finiteHiddenBinLabel (boundedScalarHiddenBins 3 width) i))

/-- The actual polynomial pullbacks, including the source complement at index zero. -/
def scalarSelectedSourceBinPartitionModels (width : ℝ)
    (i : Fin ((boundedScalarHiddenBins 3 width).card + 1)) :
    Set (ObservedBase .scalar × UnobservedFiber .scalar) :=
  scalarObservedHiddenBinCoordinates ⁻¹' (scalarSelectedSourceBinPartitionFormula width i).models

/-- The zero piece is exactly the complement of the true selected source. -/
theorem scalarSelectedSourceBinPartitionModels_zero (width : ℝ) :
    scalarSelectedSourceBinPartitionModels width 0 = scalarObservedSelectedSourceᶜ := by rfl

/-- Successor pieces are the already produced genuine positive-density source-bin pieces. -/
theorem scalarSelectedSourceBinPartitionModels_succ (width : ℝ)
    (i : Fin (boundedScalarHiddenBins 3 width).card) :
    scalarSelectedSourceBinPartitionModels width i.succ =
      scalarSelectedSourceBinTestModels width i := by rfl

/-- The zero piece retains its twelve source atoms, despite its density being zero. -/
theorem scalarSelectedSourceBinPartitionFormula_atomCount_zero (width : ℝ) :
    (scalarSelectedSourceBinPartitionFormula width 0).atomCount = 12 := by rfl

/-- Every positive piece retains all fourteen source and bin atoms. -/
theorem scalarSelectedSourceBinPartitionFormula_atomCount_succ (width : ℝ)
    (i : Fin (boundedScalarHiddenBins 3 width).card) :
    (scalarSelectedSourceBinPartitionFormula width i.succ).atomCount = 14 := by rfl

/-- Uniform per-piece atom bound, including the source complement. -/
theorem scalarSelectedSourceBinPartitionFormula_atomCount_le (width : ℝ)
    (i : Fin ((boundedScalarHiddenBins 3 width).card + 1)) :
    (scalarSelectedSourceBinPartitionFormula width i).atomCount ≤ 14 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [scalarSelectedSourceBinPartitionFormula_atomCount_zero]; omega
  · rw [scalarSelectedSourceBinPartitionFormula_atomCount_succ]

/-- Uniform cubic degree bound for the entire actual partition. -/
theorem scalarSelectedSourceBinPartitionFormula_degree (width : ℝ)
    (i : Fin ((boundedScalarHiddenBins 3 width).card + 1)) :
    (scalarSelectedSourceBinPartitionFormula width i).maxAtomDegree ≤ 3 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact scalarObservedSelectedSourceFormula_degree.trans (by omega)
  · exact scalarSelectedSourceBinFormula_degree width _

/-- All pieces are measurable by their actual polynomial formulas and coordinate map. -/
theorem scalarSelectedSourceBinPartitionModels_measurable (width : ℝ)
    (i : Fin ((boundedScalarHiddenBins 3 width).card + 1)) :
    MeasurableSet (scalarSelectedSourceBinPartitionModels width i) :=
  (scalarSelectedSourceBinPartitionFormula width i).measurableSet_models.preimage
    scalarObservedHiddenBinCoordinates_measurable

/-- The full finite partition covers the whole observed/fiber space, not only source support. -/
theorem scalarSelectedSourceBinPartitionModels_cover (width : ℝ) (hw : 0 < width) :
    (⋃ i, scalarSelectedSourceBinPartitionModels width i) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hp : p ∈ scalarObservedSelectedSource
  · have hp' : p ∈ ⋃ i, scalarSelectedSourceBinTestModels width i := by
      rw [scalarSelectedSourceBinTestModels_cover width hw]
      exact hp
    rcases Set.mem_iUnion.mp hp' with ⟨i,hi⟩
    exact ⟨i.succ,hi⟩
  · exact ⟨0,hp⟩

/-- The zero piece and the genuine half-open positive pieces are pairwise disjoint. -/
theorem scalarSelectedSourceBinPartitionModels_pairwiseDisjoint (width : ℝ) (hw : 0 < width) :
    Set.PairwiseDisjoint Set.univ (scalarSelectedSourceBinPartitionModels width) := by
  intro i _ j _ hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  refine Fin.cases ?_ (fun a => ?_) i hi hij
  · intro hi' hij'
    refine Fin.cases ?_ (fun b => ?_) j hj hij'
    · intro _ h; exact h rfl
    · intro hj' _
      exact hi' ((scalarSelectedSourceBinFormula_mem_iff width hw _ p).mp hj').1
  · intro hi' hij'
    refine Fin.cases ?_ (fun b => ?_) j hj hij'
    · intro hj' _
      exact hj' ((scalarSelectedSourceBinFormula_mem_iff width hw _ p).mp hi').1
    · intro hj' hij''
      exact Set.disjoint_left.mp
        (scalarSelectedSourceBinTestModels_pairwiseDisjoint width hw
          (Set.mem_univ a) (Set.mem_univ b) (fun h => hij'' (congrArg Fin.succ h))) hi' hj'

/-- True total atom count, including the extra zero-density source-complement formula. -/
theorem scalarSelectedSourceBinPartitionFormula_totalAtomCount (width : ℝ) :
    (∑ i, (scalarSelectedSourceBinPartitionFormula width i).atomCount) =
      14 * (boundedScalarHiddenBins 3 width).card + 12 := by
  rw [Fin.sum_univ_succ]
  simp only [scalarSelectedSourceBinPartitionFormula_atomCount_zero,
    scalarSelectedSourceBinPartitionFormula_atomCount_succ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- The values of the actual selected coordinate density on all partition pieces. -/
noncomputable def scalarSelectedSourceBinPartitionValue (width : ℝ) :
    Fin ((boundedScalarHiddenBins 3 width).card + 1) → ℝ≥0∞ :=
  Fin.cases (0 : ℝ≥0∞) (fun _ => ENNReal.ofReal (1/32 : ℝ))

/-- Actual density is constant with the produced value on every genuine partition piece. -/
theorem scalarSelectedSourceBinPartition_density_eq_value (width : ℝ) (hw : 0 < width)
    (i : Fin ((boundedScalarHiddenBins 3 width).card + 1))
    (p : ObservedBase .scalar × UnobservedFiber .scalar)
    (hp : p ∈ scalarSelectedSourceBinPartitionModels width i) :
    scalarObservedSelectedSource.indicator (fun _ => ENNReal.ofReal (1/32 : ℝ)) p =
      scalarSelectedSourceBinPartitionValue width i := by
  refine Fin.cases ?_ (fun j => ?_) i hp
  · intro h
    exact Set.indicator_of_notMem (show p ∉ scalarObservedSelectedSource from h)
      (fun _ => ENNReal.ofReal (1/32 : ℝ))
  · intro h
    exact Set.indicator_of_mem ((scalarSelectedSourceBinFormula_mem_iff width hw _ p).mp h).1 _

/-- Internally produce the full source-bin density certificate for the actual selected law,
relative to its original base/fiber product reference. No partition or range is caller input. -/
noncomputable def scalarCubeHalfTimeSelectedSourceBinDensityCertificate
    (width : ℝ) (hw : 0 < width) (γ : Fin 1) :
    FinitePiecewiseDensityCertificate (observedCoordinateProductReference .scalar)
      ((scalarCubeHalfTimeSelection.measure γ).map (observedCoordinateEquiv .scalar)) where
  pieceCount := (boundedScalarHiddenBins 3 width).card + 1
  pieces := scalarSelectedSourceBinPartitionModels width
  pieces_measurable := scalarSelectedSourceBinPartitionModels_measurable width
  pieces_pairwise_disjoint := scalarSelectedSourceBinPartitionModels_pairwiseDisjoint width hw
  pieces_cover := scalarSelectedSourceBinPartitionModels_cover width hw
  density := scalarObservedSelectedSource.indicator (fun _ => ENNReal.ofReal (1/32 : ℝ))
  density_measurable := measurable_const.indicator scalarObservedSelectedSource_measurable
  value := scalarSelectedSourceBinPartitionValue width
  density_eq_value := scalarSelectedSourceBinPartition_density_eq_value width hw
  prior_eq_withDensity := scalarCubeHalfTimeSelection_observedCoordinateLaw_sourceIndicator γ

/-- The genuine six-coordinate measurable equivalence, with the explicit coordinate inverse. -/
def scalarObservedFiberFinMeasurableEquiv :
    (ObservedBase .scalar × UnobservedFiber .scalar) ≃ᵐ (Fin 6 → ℝ) where
  toFun := scalarObservedHiddenBinCoordinates
  invFun x := ((x 0,x 1),(x 2,(x 3,(x 4,x 5))))
  left_inv := by intro p; rcases p with ⟨⟨t,y⟩,v,w0,w1,w2⟩; rfl
  right_inv := by intro x; funext i; fin_cases i <;> rfl
  measurable_toFun := scalarObservedHiddenBinCoordinates_measurable
  measurable_invFun := by
    change Measurable (fun x : Fin 6 → ℝ => ((x 0,x 1),(x 2,(x 3,(x 4,x 5)))))
    fun_prop

/-- Produce the complete finite semialgebraic density certificate in the actual six-coordinate
chart. The reference is still the original unit-time observed/fiber measure, not full `ℝ⁶` volume. -/
noncomputable def scalarCubeHalfTimeSelectedSourceBinSemialgebraicCertificate
    (width : ℝ) (hw : 0 < width) (γ : Fin 1) :
    CoordinateSemialgebraicDensityCertificate scalarObservedFiberFinMeasurableEquiv
      (observedCoordinateProductReference .scalar)
      ((scalarCubeHalfTimeSelection.measure γ).map (observedCoordinateEquiv .scalar))
      ((boundedScalarHiddenBins 3 width).card + 1) 6 14 3 (ENNReal.ofReal (1/32 : ℝ)) where
  pieceCount := (boundedScalarHiddenBins 3 width).card + 1
  pieceCount_le := le_rfl
  variableCount_le := le_rfl
  pieces := scalarSelectedSourceBinPartitionFormula width
  atoms_per_piece_le := scalarSelectedSourceBinPartitionFormula_atomCount_le width
  degree_per_piece_le := scalarSelectedSourceBinPartitionFormula_degree width
  pieces_pairwise_disjoint := scalarSelectedSourceBinPartitionModels_pairwiseDisjoint width hw
  pieces_cover := scalarSelectedSourceBinPartitionModels_cover width hw
  density := scalarObservedSelectedSource.indicator (fun _ => ENNReal.ofReal (1/32 : ℝ))
  density_measurable := measurable_const.indicator scalarObservedSelectedSource_measurable
  value := scalarSelectedSourceBinPartitionValue width
  density_eq_value := scalarSelectedSourceBinPartition_density_eq_value width hw
  densityBound_lt_top := ENNReal.ofReal_lt_top
  density_le_bound := by
    intro p
    by_cases hp : p ∈ scalarObservedSelectedSource <;> simp [Set.indicator, hp]
  prior_eq_withDensity := scalarCubeHalfTimeSelection_observedCoordinateLaw_sourceIndicator γ

/-- The genuine per-copy world-data width instantiates the produced full partition and density.
No range, cover, semialgebraic partition, or prior-density certificate is caller input. -/
noncomputable def scalarCubeTwoCopyHalfTimeSelectedSourceBinSemialgebraicCertificate
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar)
    (γ : Fin 1) (i : Fin 2) :
    CoordinateSemialgebraicDensityCertificate scalarObservedFiberFinMeasurableEquiv
      (observedCoordinateProductReference .scalar)
      (((scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i).measure (0 : Fin 1)).map
        (observedCoordinateEquiv .scalar))
      ((boundedScalarHiddenBins 3 (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale .scalar (worldData γ i)))).card + 1)
      6 14 3 (ENNReal.ofReal (1/32 : ℝ)) :=
  scalarCubeHalfTimeSelectedSourceBinSemialgebraicCertificate _
    (observation_bin_width_pos .scalar seq depth n (fun _ : Fin 1 => worldData γ i) 0) 0

/-- The actual per-copy partition has precisely one extra piece beyond its genuine finite bins. -/
noncomputable def scalarSelectedSourceBinPartitionCount (width : ℝ) : ℕ :=
  (boundedScalarHiddenBins 3 width).card + 1

/-- Record the actual formula sum rather than a per-piece upper-bound surrogate. -/
noncomputable def scalarSelectedSourceBinPartitionAtomCount (width : ℝ) : ℕ :=
  ∑ i, (scalarSelectedSourceBinPartitionFormula width i).atomCount

/-- The complete partition has at most `9 N^ceil(L)` pieces on the actual scalar scales. -/
noncomputable def scalarSelectedSourceBinPartitionCount_polynomiallyBounded
    (seq : ExactSequence) (depth : Depth seq) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      scalarSelectedSourceBinPartitionCount (dyadicRoundedWidth (seq.depthScale depth n))) where
  coefficient := 9
  exponent := Nat.ceil seq.length
  bound n := by
    change (((scalarCubeFiniteHiddenBins seq depth n).card + 1 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add, Nat.cast_one]
    have h := scalarCubeFiniteHiddenBins_uniform_card_bound seq depth n
    have hp : (1 : ℝ) ≤ seq.resolution n ^ Nat.ceil seq.length :=
      one_le_pow₀ (seq.resolution_ge_one n)
    norm_num only [Nat.cast_ofNat]
    linarith

/-- Paying all source atoms and the zero piece gives `124 N^ceil(L)`, uniformly at every index. -/
noncomputable def scalarSelectedSourceBinPartitionAtomCount_polynomiallyBounded
    (seq : ExactSequence) (depth : Depth seq) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      scalarSelectedSourceBinPartitionAtomCount (dyadicRoundedWidth (seq.depthScale depth n))) where
  coefficient := 124
  exponent := Nat.ceil seq.length
  bound n := by
    unfold scalarSelectedSourceBinPartitionAtomCount
    rw [scalarSelectedSourceBinPartitionFormula_totalAtomCount, Nat.cast_add, Nat.cast_mul]
    have h := scalarCubeFiniteHiddenBins_uniform_card_bound seq depth n
    have hp : (1 : ℝ) ≤ seq.resolution n ^ Nat.ceil seq.length :=
      one_le_pow₀ (seq.resolution_ge_one n)
    change (14 : ℝ) * ((scalarCubeFiniteHiddenBins seq depth n).card : ℝ) + 12 ≤ _
    norm_num only [Nat.cast_ofNat]
    linarith

/-- The new observed-coordinate certificate agrees pointwise with the original trajectory-
certificate density used by the actual hidden-bin law. -/
theorem scalarCubeTwoCopyHalfTimeSelectedSourceBinSemialgebraicCertificate_density
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar)
    (γ : Fin 1) (i : Fin 2) :
    selectedObservedCoordinateDensity (scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i)
      (scalarCubeTwoCopyActualDensityCertificates seq n γ i) (0 : Fin 1) =
    (scalarCubeTwoCopyHalfTimeSelectedSourceBinSemialgebraicCertificate
      seq depth n worldData γ i).density :=
  scalarCubeTwoCopyHalfTimeSelection_selectedObservedCoordinateDensity seq n γ i

/-- Sum the actual full partition counts over both original world/copy tags. -/
noncomputable def scalarCubeWorldCopySourceBinPartitionCount
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) : ℕ :=
  ∑ q : WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2),
    scalarSelectedSourceBinPartitionCount (dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale .scalar (worldData q.world q.copy)))

/-- Count every formula occurrence, including one zero-density piece for each actual copy. -/
noncomputable def scalarCubeWorldCopySourceBinPartitionAtomCount
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) : ℕ :=
  ∑ q : WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2),
    scalarSelectedSourceBinPartitionAtomCount (dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale .scalar (worldData q.world q.copy)))

/-- Equal scalar widths do not remove the two separate source-complement pieces. -/
theorem scalarCubeWorldCopySourceBinPartitionCount_eq
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    scalarCubeWorldCopySourceBinPartitionCount seq depth n worldData =
      2 * (scalarCubeFiniteHiddenBins seq depth n).card + 2 := by
  unfold scalarCubeWorldCopySourceBinPartitionCount
  rw [sum_worldCopyHiddenBinTags]
  simp [scalarSelectedSourceBinPartitionCount, worldDerivativeScale,
    scalarCubeFiniteHiddenBins, two_mul]
  omega

/-- The exact two-copy atom total pays both zero-piece formulas. -/
theorem scalarCubeWorldCopySourceBinPartitionAtomCount_eq
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    scalarCubeWorldCopySourceBinPartitionAtomCount seq depth n worldData =
      28 * (scalarCubeFiniteHiddenBins seq depth n).card + 24 := by
  unfold scalarCubeWorldCopySourceBinPartitionAtomCount scalarSelectedSourceBinPartitionAtomCount
  simp only [scalarSelectedSourceBinPartitionFormula_totalAtomCount]
  rw [sum_worldCopyHiddenBinTags]
  simp [worldDerivativeScale, scalarCubeFiniteHiddenBins]
  omega

/-- Produced all-index polynomial bound on both actual partition counts, with their zero pieces. -/
noncomputable def scalarCubeWorldCopySourceBinPartitionCount_polynomiallyBounded
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ℕ → ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      scalarCubeWorldCopySourceBinPartitionCount seq depth n (worldData n)) where
  coefficient := 18
  exponent := Nat.ceil seq.length
  bound n := by
    rw [scalarCubeWorldCopySourceBinPartitionCount_eq, Nat.cast_add, Nat.cast_mul]
    have h := scalarCubeFiniteHiddenBins_uniform_card_bound seq depth n
    have hp : (1 : ℝ) ≤ seq.resolution n ^ Nat.ceil seq.length :=
      one_le_pow₀ (seq.resolution_ge_one n)
    norm_num only [Nat.cast_ofNat]
    linarith

/-- Produced all-index atom profile for both copies; `248` includes both twelve-atom zero pieces. -/
noncomputable def scalarCubeWorldCopySourceBinPartitionAtomCount_polynomiallyBounded
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ℕ → ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      scalarCubeWorldCopySourceBinPartitionAtomCount seq depth n (worldData n)) where
  coefficient := 248
  exponent := Nat.ceil seq.length
  bound n := by
    rw [scalarCubeWorldCopySourceBinPartitionAtomCount_eq, Nat.cast_add, Nat.cast_mul]
    have h := scalarCubeFiniteHiddenBins_uniform_card_bound seq depth n
    have hp : (1 : ℝ) ≤ seq.resolution n ^ Nat.ceil seq.length :=
      one_le_pow₀ (seq.resolution_ge_one n)
    norm_num only [Nat.cast_ofNat]
    linarith

end Kakeya4.Framework
