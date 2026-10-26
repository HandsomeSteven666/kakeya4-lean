import Kakeya4.Construction.Framework.ConcretePrior
import Mathlib.Data.Fintype.EquivFin







set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace Kakeya4.Framework

/-- Enumerate the genuine labels of a finite family without replacing them by new labels. -/
noncomputable def finiteHiddenBinLabel {α : Type*} (bins : Finset α)
    (i : Fin bins.card) : α := (bins.equivFin.symm i).1

/-- Each enumerated label belongs to the original finite set. -/
theorem finiteHiddenBinLabel_mem {α : Type*} (bins : Finset α) (i : Fin bins.card) :
    finiteHiddenBinLabel bins i ∈ bins := (bins.equivFin.symm i).2

/-- Enumeration does not merge two distinct test indices. -/
theorem finiteHiddenBinLabel_injective {α : Type*} (bins : Finset α) :
    Function.Injective (finiteHiddenBinLabel bins) := by
  intro i j h
  exact bins.equivFin.symm.injective (Subtype.ext h)

/-- Every original label is represented by an actual finite test index. -/
theorem exists_finiteHiddenBinLabel_eq {α : Type*} (bins : Finset α) (j : α) (hj : j ∈ bins) :
    ∃ i : Fin bins.card, finiteHiddenBinLabel bins i = j := by
  refine ⟨bins.equivFin ⟨j,hj⟩, ?_⟩
  exact congrArg Subtype.val (bins.equivFin.symm_apply_apply ⟨j,hj⟩)

/-- The scalar finite family is built from the actual two-atom cubic bin formulas. -/
noncomputable def scalarFiniteHiddenBinTestFamily (M width : ℝ) :
    BoundedPolynomialTestFamily (boundedScalarHiddenBins M width).card 6 2 3 where
  testCount := (boundedScalarHiddenBins M width).card
  testCount_le := le_rfl
  test i := scalarObservedHiddenBinBoundedTest width
    (finiteHiddenBinLabel (boundedScalarHiddenBins M width) i)

/-- The planar finite family keeps the actual four-atom quadratic bin-pair formulas. -/
noncomputable def planarFiniteHiddenBinTestFamily (M width : ℝ) :
    BoundedPolynomialTestFamily (boundedPlanarHiddenBins M width).card 9 4 2 where
  testCount := (boundedPlanarHiddenBins M width).card
  testCount_le := le_rfl
  test i := planarObservedHiddenBinBoundedTest width
    (finiteHiddenBinLabel (boundedPlanarHiddenBins M width) i)

/-- Pull back the actual scalar test in the produced family through its real coordinate map. -/
def scalarFiniteHiddenBinTestModels (M width : ℝ)
    (i : Fin (boundedScalarHiddenBins M width).card) :
    Set (ObservedBase .scalar × UnobservedFiber .scalar) :=
  {p | scalarObservedHiddenBinCoordinates p ∈
    ((scalarFiniteHiddenBinTestFamily M width).test i).formula.models}

/-- Pull back the actual planar family test, retaining both hidden coordinates. -/
def planarFiniteHiddenBinTestModels (M width : ℝ)
    (i : Fin (boundedPlanarHiddenBins M width).card) :
    Set (ObservedBase .planar × UnobservedFiber .planar) :=
  {p | planarObservedHiddenBinCoordinates p ∈
    ((planarFiniteHiddenBinTestFamily M width).test i).formula.models}

/-- Actual scalar test membership is the genuine bin label equality. -/
theorem scalarFiniteHiddenBinTestModels_mem_iff (M width : ℝ) (hw : 0 < width)
    (i : Fin (boundedScalarHiddenBins M width).card)
    (p : ObservedBase .scalar × UnobservedFiber .scalar) :
    p ∈ scalarFiniteHiddenBinTestModels M width i ↔
      observedFiberHiddenBin .scalar p.1 p.2 width =
        finiteHiddenBinLabel (boundedScalarHiddenBins M width) i := by
  exact scalarObservedHiddenBinFormula_mem_iff width hw _ p

/-- Actual planar test membership is equality of both genuine integer bin coordinates. -/
theorem planarFiniteHiddenBinTestModels_mem_iff (M width : ℝ) (hw : 0 < width)
    (i : Fin (boundedPlanarHiddenBins M width).card)
    (p : ObservedBase .planar × UnobservedFiber .planar) :
    p ∈ planarFiniteHiddenBinTestModels M width i ↔
      observedFiberHiddenBin .planar p.1 p.2 width =
        finiteHiddenBinLabel (boundedPlanarHiddenBins M width) i := by
  exact planarObservedHiddenBinFormula_mem_iff width hw _ p

/-- Distinct scalar bin tests are disjoint on the actual observed/fiber space. -/
theorem scalarFiniteHiddenBinTestModels_pairwiseDisjoint (M width : ℝ) (hw : 0 < width) :
    Set.PairwiseDisjoint Set.univ (scalarFiniteHiddenBinTestModels M width) := by
  intro i _ j _ hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have heq := (scalarFiniteHiddenBinTestModels_mem_iff M width hw i p).mp hi
  have heq' := (scalarFiniteHiddenBinTestModels_mem_iff M width hw j p).mp hj
  exact hij (finiteHiddenBinLabel_injective _ (heq.symm.trans heq'))

/-- Distinct planar bin-pair tests are disjoint, rather than merely separate per coordinate. -/
theorem planarFiniteHiddenBinTestModels_pairwiseDisjoint (M width : ℝ) (hw : 0 < width) :
    Set.PairwiseDisjoint Set.univ (planarFiniteHiddenBinTestModels M width) := by
  intro i _ j _ hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have heq := (planarFiniteHiddenBinTestModels_mem_iff M width hw i p).mp hi
  have heq' := (planarFiniteHiddenBinTestModels_mem_iff M width hw j p).mp hj
  exact hij (finiteHiddenBinLabel_injective _ (heq.symm.trans heq'))

/-- The scalar produced tests cover exactly the finite-bin part of the actual coordinate space. -/
theorem scalarFiniteHiddenBinTestModels_cover_iff (M width : ℝ) (hw : 0 < width)
    (p : ObservedBase .scalar × UnobservedFiber .scalar) :
    p ∈ ⋃ i, scalarFiniteHiddenBinTestModels M width i ↔
      observedFiberHiddenBin .scalar p.1 p.2 width ∈ boundedScalarHiddenBins M width := by
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨i,hi⟩
    have heq := (scalarFiniteHiddenBinTestModels_mem_iff M width hw i p).mp hi
    rw [heq]
    exact finiteHiddenBinLabel_mem _ i
  · intro hp
    rcases exists_finiteHiddenBinLabel_eq _ _ hp with ⟨i,hi⟩
    exact Set.mem_iUnion.mpr ⟨i,
      (scalarFiniteHiddenBinTestModels_mem_iff M width hw i p).mpr hi.symm⟩

/-- The planar tests cover exactly the actual finite bin-pair support, without losing labels. -/
theorem planarFiniteHiddenBinTestModels_cover_iff (M width : ℝ) (hw : 0 < width)
    (p : ObservedBase .planar × UnobservedFiber .planar) :
    p ∈ ⋃ i, planarFiniteHiddenBinTestModels M width i ↔
      observedFiberHiddenBin .planar p.1 p.2 width ∈ boundedPlanarHiddenBins M width := by
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨i,hi⟩
    have heq := (planarFiniteHiddenBinTestModels_mem_iff M width hw i p).mp hi
    rw [heq]
    exact finiteHiddenBinLabel_mem _ i
  · intro hp
    rcases exists_finiteHiddenBinLabel_eq _ _ hp with ⟨i,hi⟩
    exact Set.mem_iUnion.mpr ⟨i,
      (planarFiniteHiddenBinTestModels_mem_iff M width hw i p).mpr hi.symm⟩

/-- The real coordinate equivalence preserves the hidden bin read from the actual trajectory. -/
theorem observedFiberHiddenBin_observedCoordinateEquiv (v : ModelVersion)
    (p : Trajectory v × ℝ) (width : ℝ) :
    observedFiberHiddenBin v (observedCoordinateEquiv v p).1
      (observedCoordinateEquiv v p).2 width = hiddenBin v (hiddenAt v p.1 p.2) width := by
  cases v with
  | scalar => rcases p with ⟨⟨y,V,w0,w1,w2⟩,t⟩; rfl
  | planar => rcases p with ⟨⟨y,V,w0,wV⟩,t⟩; rfl

/-- The actual cube selected incidence support is covered by the produced scalar tests, at the
same actual observation width, for any event restriction and without a caller range certificate. -/
theorem scalarCube_selected_ae_finiteHiddenBinTests_cover {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData .scalar) (γ : Fin worldCount)
    (event : Set (ScalarTrajectory × ℝ)) :
    ∀ᵐ p ∂(scalarCubeTrajectoryPrior.prod unitTimeMeasure).restrict event,
      observedCoordinateEquiv .scalar p ∈ ⋃ i,
        scalarFiniteHiddenBinTestModels 3 (dyadicRoundedWidth
          (seq.depthScale depth n / worldDerivativeScale .scalar (worldData γ))) i := by
  filter_upwards [scalarCube_selected_ae_observationAt_bin_mem seq depth n worldData γ event]
    with p hp
  apply (scalarFiniteHiddenBinTestModels_cover_iff 3 _
    (observation_bin_width_pos .scalar seq depth n worldData γ) _).mpr
  rw [observedFiberHiddenBin_observedCoordinateEquiv]
  exact hp

/-- Exact scalar atom count for the produced finite family, counting repeated atoms per test. -/
theorem scalarFiniteHiddenBinTestFamily_totalAtomCount (M width : ℝ) :
    (∑ i : Fin (scalarFiniteHiddenBinTestFamily M width).testCount,
      ((scalarFiniteHiddenBinTestFamily M width).test i).formula.atomCount) =
      2 * (boundedScalarHiddenBins M width).card := by
  change (∑ _i : Fin (boundedScalarHiddenBins M width).card, (2 : ℕ)) = _
  simp [mul_comm]

/-- Exact planar atom count retains four atoms for every genuine bin pair. -/
theorem planarFiniteHiddenBinTestFamily_totalAtomCount (M width : ℝ) :
    (∑ i : Fin (planarFiniteHiddenBinTestFamily M width).testCount,
      ((planarFiniteHiddenBinTestFamily M width).test i).formula.atomCount) =
      4 * (boundedPlanarHiddenBins M width).card := by
  change (∑ _i : Fin (boundedPlanarHiddenBins M width).card, (4 : ℕ)) = _
  simp [mul_comm]

/-- Actual scalar-cube test-family cardinality has the already proved uniform polynomial bound. -/
noncomputable def scalarCubeFiniteHiddenBinTestFamily_count_polynomiallyBounded
    (seq : ExactSequence) (depth : Depth seq) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      (scalarFiniteHiddenBinTestFamily 3 (dyadicRoundedWidth (seq.depthScale depth n))).testCount) :=
  scalarCubeFiniteHiddenBins_polynomiallyBounded seq depth

/-- Total actual scalar test atoms have coefficient sixteen and exponent ceil(length), fixed
before every depth and sequence index. -/
noncomputable def scalarCubeFiniteHiddenBinTestFamily_atoms_polynomiallyBounded
    (seq : ExactSequence) (depth : Depth seq) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      ∑ i : Fin (scalarFiniteHiddenBinTestFamily 3
        (dyadicRoundedWidth (seq.depthScale depth n))).testCount,
        ((scalarFiniteHiddenBinTestFamily 3
          (dyadicRoundedWidth (seq.depthScale depth n))).test i).formula.atomCount) where
  coefficient := 16
  exponent := Nat.ceil seq.length
  bound n := by
    rw [scalarFiniteHiddenBinTestFamily_totalAtomCount, Nat.cast_mul]
    have h := scalarCubeFiniteHiddenBins_uniform_card_bound seq depth n
    change (2 : ℝ) * ((scalarCubeFiniteHiddenBins seq depth n).card : ℝ) ≤ _
    norm_num only [Nat.cast_ofNat]
    linarith


/-- The actual two-copy half-time source is covered copy by copy, with each copy's matching
world data and original selected incidence measure. The support proof is produced internally. -/
theorem scalarCubeTwoCopyHalfTimeSelection_ae_finiteHiddenBinTests_cover
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar)
    (γ : Fin 1) (i : Fin 2) :
    ∀ᵐ p ∂(scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i).measure
      (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex γ i),
      observedCoordinateEquiv .scalar p ∈ ⋃ j,
        scalarFiniteHiddenBinTestModels 3 (dyadicRoundedWidth
          (seq.depthScale depth n / worldDerivativeScale .scalar (worldData γ i))) j := by
  convert scalarCube_selected_ae_finiteHiddenBinTests_cover seq depth n
    (fun _ : Fin 1 => worldData γ i) (0 : Fin 1) scalarHalfTimeEvent using 1
  rfl

/-- General actual planar incidence selections are covered by the produced tests under the
stated original-prior coefficient bounds; a hidden-range certificate is not an input. -/
theorem IncidenceSelection.planar_ae_finiteHiddenBinTests_cover_of_ae_coeffBounds
    (I : @IncidenceSelection .planar (instMeasurableSpaceTrajectory .planar))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData .planar)
    (γ : Fin I.priors.worldCount) (R : ℝ) (hR : 0 ≤ R)
    (hcoeff : ∀ᵐ l ∂I.priors.prior γ, ∀ i : Fin 2,
      |l.w0.ofLp i| ≤ R ∧ |l.wVelocity.ofLp i| ≤ R) :
    ∀ᵐ p ∂I.measure γ,
      observedCoordinateEquiv .planar p ∈ ⋃ i,
        planarFiniteHiddenBinTestModels (2 * R) (dyadicRoundedWidth
          (seq.depthScale depth n / worldDerivativeScale .planar (worldData γ))) i := by
  have hprod := planarPrior_product_ae_hiddenAt_abs_le (I.priors.prior γ) R hR hcoeff
  have hselected := ae_restrict_of_ae (s := I.event γ) hprod
  dsimp only [IncidenceSelection.measure, WorldPriorSystem.selectedIncidenceMeasure,
    WorldPriorSystem.productIncidenceMeasure]
  filter_upwards [hselected] with p hp
  apply (planarFiniteHiddenBinTestModels_cover_iff (2 * R) _
    (observation_bin_width_pos .planar seq depth n worldData γ) _).mpr
  rw [observedFiberHiddenBin_observedCoordinateEquiv]
  exact hiddenBin_planar_mem_boundedPlanarHiddenBins (2 * R) _ _
    (observation_bin_width_pos .planar seq depth n worldData γ) hp

/-- Actual planar finite test counts have an all-index polynomial certificate, with the true
squared count and doubled exponent and every world derivative bound stated before the index. -/
noncomputable def planarFiniteHiddenBinTestFamily_count_polynomiallyBounded
    {worldCount : ℕ} (seq : ExactSequence) (depth : Depth seq)
    (worldData : ℕ → Fin worldCount → VersionWorldData .planar)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hworld : ∀ n γ, worldDerivativeScale .planar (worldData n γ) ≤ B)
    (γ : Fin worldCount) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      (planarFiniteHiddenBinTestFamily M (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale .planar (worldData n γ)))).testCount) where
  coefficient := Nat.ceil ((2 * M * B + 2) ^ 2)
  exponent := 2 * Nat.ceil seq.length
  bound n := by
    apply (observation_planarBins_uniform_card_bound .planar seq worldData M B hM hB hworld
      depth n γ).trans
    have hN : 0 ≤ seq.resolution n := le_trans zero_le_one (seq.resolution_ge_one n)
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)

/-- Total planar test atoms have an explicit natural coefficient four times the bin-count
coefficient, without hiding the extra coordinate or the copy-independent exponent. -/
noncomputable def planarFiniteHiddenBinTestFamily_atoms_polynomiallyBounded
    {worldCount : ℕ} (seq : ExactSequence) (depth : Depth seq)
    (worldData : ℕ → Fin worldCount → VersionWorldData .planar)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hworld : ∀ n γ, worldDerivativeScale .planar (worldData n γ) ≤ B)
    (γ : Fin worldCount) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      ∑ i : Fin (planarFiniteHiddenBinTestFamily M (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale .planar (worldData n γ)))).testCount,
        ((planarFiniteHiddenBinTestFamily M (dyadicRoundedWidth
          (seq.depthScale depth n / worldDerivativeScale .planar (worldData n γ)))).test i).formula.atomCount) where
  coefficient := 4 * Nat.ceil ((2 * M * B + 2) ^ 2)
  exponent := 2 * Nat.ceil seq.length
  bound n := by
    rw [planarFiniteHiddenBinTestFamily_totalAtomCount, Nat.cast_mul, Nat.cast_mul]
    have h := (planarFiniteHiddenBinTestFamily_count_polynomiallyBounded
      seq depth worldData M B hM hB hworld γ).bound n
    change (4 : ℝ) * ((boundedPlanarHiddenBins M (dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale .planar (worldData n γ)))).card : ℝ) ≤ _
    simpa only [planarFiniteHiddenBinTestFamily_count_polynomiallyBounded,
      planarFiniteHiddenBinTestFamily, Nat.cast_ofNat, mul_assoc] using
      mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (4 : ℝ))

end Kakeya4.Framework
