import Experiments.FiniteBins.FiniteHiddenBinTests

/-!
# Actual world/copy finite-test complexity

This isolated module retains every original copy and every polynomial atom occurrence.
Equal formulas at different copies are not deduplicated.
-/
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace Kakeya4.Framework

/-- Public reindexing adapted from the existing private spatial aggregation helper. -/
theorem sum_worldCopyHiddenBinTags {W : ℕ} {count : Fin W → ℕ}
    {α : Type*} [AddCommMonoid α] (f : WorldTrajectoryCopyIndex W count → α) :
    ∑ q, f q = ∑ γ, ∑ i, f ⟨γ,i⟩ := by
  let e : (Σ γ : Fin W, Fin (count γ)) ≃ WorldTrajectoryCopyIndex W count := {
    toFun := fun p => ⟨p.1,p.2⟩
    invFun := fun q => ⟨q.world,q.copy⟩
    left_inv := by intro p; cases p; rfl
    right_inv := by intro q; cases q; rfl }
  rw [← e.sum_comp f, Fintype.sum_sigma]
  rfl

/-- A test retains its actual world/copy tag and its local test ordinal. -/
abbrev WorldCopyFiniteHiddenBinTestIndex {W : ℕ} {count : Fin W → ℕ}
    {bound : WorldTrajectoryCopyIndex W count → ℕ} {V A D : ℕ}
    (families : ∀ q, BoundedPolynomialTestFamily (bound q) V A D) :=
  Σ q : WorldTrajectoryCopyIndex W count, Fin (families q).testCount

/-- Count all tagged test occurrences, including repeated geometric formulas. -/
def worldCopyFiniteHiddenBinTestCount {W : ℕ} {count : Fin W → ℕ}
    {bound : WorldTrajectoryCopyIndex W count → ℕ} {V A D : ℕ}
    (families : ∀ q, BoundedPolynomialTestFamily (bound q) V A D) : ℕ :=
  ∑ q, (families q).testCount

/-- Count all atoms in every actual tagged test. -/
def worldCopyFiniteHiddenBinAtomCount {W : ℕ} {count : Fin W → ℕ}
    {bound : WorldTrajectoryCopyIndex W count → ℕ} {V A D : ℕ}
    (families : ∀ q, BoundedPolynomialTestFamily (bound q) V A D) : ℕ :=
  ∑ q, ∑ j : Fin (families q).testCount, ((families q).test j).formula.atomCount

/-- The actual dependent test-index cardinality equals the test-occurrence total. -/
theorem worldCopyFiniteHiddenBinTestIndex_card {W : ℕ} {count : Fin W → ℕ}
    {bound : WorldTrajectoryCopyIndex W count → ℕ} {V A D : ℕ}
    (families : ∀ q, BoundedPolynomialTestFamily (bound q) V A D) :
    Fintype.card (WorldCopyFiniteHiddenBinTestIndex families) =
      worldCopyFiniteHiddenBinTestCount families := by
  simp [WorldCopyFiniteHiddenBinTestIndex, worldCopyFiniteHiddenBinTestCount]

/-- Expose the separate world and copy finite sums. -/
theorem worldCopyFiniteHiddenBinTestCount_eq_nested {W : ℕ} {count : Fin W → ℕ}
    {bound : WorldTrajectoryCopyIndex W count → ℕ} {V A D : ℕ}
    (families : ∀ q, BoundedPolynomialTestFamily (bound q) V A D) :
    worldCopyFiniteHiddenBinTestCount families = ∑ γ, ∑ i, (families ⟨γ,i⟩).testCount :=
  sum_worldCopyHiddenBinTags _

/-- Uniform copy and per-family bounds produce the total test bound. -/
theorem worldCopyFiniteHiddenBinTestCount_le_envelopes {W : ℕ} {count : Fin W → ℕ}
    {bound : WorldTrajectoryCopyIndex W count → ℕ} {V A D : ℕ}
    (families : ∀ q, BoundedPolynomialTestFamily (bound q) V A D)
    (copyEnvelope testEnvelope : ℕ) (hc : ∀ γ, count γ ≤ copyEnvelope)
    (ht : ∀ q, (families q).testCount ≤ testEnvelope) :
    worldCopyFiniteHiddenBinTestCount families ≤ W * copyEnvelope * testEnvelope := by
  rw [worldCopyFiniteHiddenBinTestCount_eq_nested]
  calc
    _ ≤ ∑ γ : Fin W, count γ * testEnvelope := by
      apply Finset.sum_le_sum
      intro γ _
      calc
        _ ≤ ∑ _i : Fin (count γ), testEnvelope := Finset.sum_le_sum (fun i _ => ht ⟨γ,i⟩)
        _ = _ := by simp
    _ ≤ ∑ _γ : Fin W, copyEnvelope * testEnvelope :=
      Finset.sum_le_sum (fun γ _ => Nat.mul_le_mul_right _ (hc γ))
    _ = _ := by simp [Nat.mul_assoc]

/-- Per-test atom bounds preserve all actual occurrences in the total. -/
theorem worldCopyFiniteHiddenBinAtomCount_le_testCount_mul {W : ℕ} {count : Fin W → ℕ}
    {bound : WorldTrajectoryCopyIndex W count → ℕ} {V A D : ℕ}
    (families : ∀ q, BoundedPolynomialTestFamily (bound q) V A D) :
    worldCopyFiniteHiddenBinAtomCount families ≤ worldCopyFiniteHiddenBinTestCount families * A := by
  unfold worldCopyFiniteHiddenBinAtomCount worldCopyFiniteHiddenBinTestCount
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q _
  calc
    _ ≤ ∑ _j : Fin (families q).testCount, A :=
      Finset.sum_le_sum (fun j _ => ((families q).test j).atomCount_le)
    _ = _ := by simp

/-- Worlds, copies, tests per copy and atoms per test all enter the actual bound. -/
theorem worldCopyFiniteHiddenBinAtomCount_le_envelopes {W : ℕ} {count : Fin W → ℕ}
    {bound : WorldTrajectoryCopyIndex W count → ℕ} {V A D : ℕ}
    (families : ∀ q, BoundedPolynomialTestFamily (bound q) V A D)
    (copyEnvelope testEnvelope : ℕ) (hc : ∀ γ, count γ ≤ copyEnvelope)
    (ht : ∀ q, (families q).testCount ≤ testEnvelope) :
    worldCopyFiniteHiddenBinAtomCount families ≤ W * copyEnvelope * testEnvelope * A :=
  (worldCopyFiniteHiddenBinAtomCount_le_testCount_mul families).trans
    (Nat.mul_le_mul_right A (worldCopyFiniteHiddenBinTestCount_le_envelopes
      families copyEnvelope testEnvelope hc ht))

/-- Produce each actual cube copy's finite family at its own world-data width. -/
noncomputable def scalarCubeWorldCopyHiddenBinTests (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar)
    (q : WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2)) :
    BoundedPolynomialTestFamily
      (boundedScalarHiddenBins 3 (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale .scalar (worldData q.world q.copy)))).card
      6 2 3 :=
  scalarFiniteHiddenBinTestFamily 3 (dyadicRoundedWidth
    (seq.depthScale depth n / worldDerivativeScale .scalar (worldData q.world q.copy)))

/-- Count both actual cube-copy test families. -/
noncomputable def scalarCubeWorldCopyHiddenBinTestCount (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) : ℕ :=
  worldCopyFiniteHiddenBinTestCount (scalarCubeWorldCopyHiddenBinTests seq depth n worldData)

/-- Sum all actual cube-copy atoms. -/
noncomputable def scalarCubeWorldCopyHiddenBinAtomCount (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) : ℕ :=
  worldCopyFiniteHiddenBinAtomCount (scalarCubeWorldCopyHiddenBinTests seq depth n worldData)

/-- Equal widths do not remove the actual factor two from the copy index. -/
theorem scalarCubeWorldCopyHiddenBinTestCount_eq_two_mul (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    scalarCubeWorldCopyHiddenBinTestCount seq depth n worldData =
      2 * (scalarCubeFiniteHiddenBins seq depth n).card := by
  unfold scalarCubeWorldCopyHiddenBinTestCount worldCopyFiniteHiddenBinTestCount
  rw [sum_worldCopyHiddenBinTags]
  simp [scalarCubeWorldCopyHiddenBinTests, scalarFiniteHiddenBinTestFamily,
    scalarCubeFiniteHiddenBins, worldDerivativeScale, two_mul]

/-- Two atoms per bin in each of two copies give the exact factor four. -/
theorem scalarCubeWorldCopyHiddenBinAtomCount_eq_four_mul (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    scalarCubeWorldCopyHiddenBinAtomCount seq depth n worldData =
      4 * (scalarCubeFiniteHiddenBins seq depth n).card := by
  unfold scalarCubeWorldCopyHiddenBinAtomCount worldCopyFiniteHiddenBinAtomCount
  change (∑ q : WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2),
    ∑ _j : Fin (scalarCubeWorldCopyHiddenBinTests seq depth n worldData q).testCount,
      (2 : ℕ)) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  change scalarCubeWorldCopyHiddenBinTestCount seq depth n worldData * 2 = _
  rw [scalarCubeWorldCopyHiddenBinTestCount_eq_two_mul]
  omega

/-- A produced all-index polynomial profile for the actual double-copy test total. -/
noncomputable def scalarCubeWorldCopyHiddenBinTestCount_polynomiallyBounded
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ℕ → ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      scalarCubeWorldCopyHiddenBinTestCount seq depth n (worldData n)) where
  coefficient := 16
  exponent := Nat.ceil seq.length
  bound n := by
    rw [scalarCubeWorldCopyHiddenBinTestCount_eq_two_mul, Nat.cast_mul]
    have h := scalarCubeFiniteHiddenBins_uniform_card_bound seq depth n
    norm_num only [Nat.cast_ofNat]
    linarith

/-- Count every atom in both copies, with the same fixed length-ceiling exponent. -/
noncomputable def scalarCubeWorldCopyHiddenBinAtomCount_polynomiallyBounded
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ℕ → ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    PolynomiallyBoundedNatAlong seq (fun n =>
      scalarCubeWorldCopyHiddenBinAtomCount seq depth n (worldData n)) where
  coefficient := 32
  exponent := Nat.ceil seq.length
  bound n := by
    rw [scalarCubeWorldCopyHiddenBinAtomCount_eq_four_mul, Nat.cast_mul]
    have h := scalarCubeFiniteHiddenBins_uniform_card_bound seq depth n
    norm_num only [Nat.cast_ofNat]
    linarith


/-- Lower-level world/copy/test envelopes produce a polynomial bound for the actual total,
with one profile before all varying world and copy indices. -/
noncomputable def worldCopyFiniteHiddenBinTestCount_polynomiallyBounded
    {seq : ExactSequence} {W : ℕ → ℕ} {count : ∀ n, Fin (W n) → ℕ}
    {bound : ∀ n, WorldTrajectoryCopyIndex (W n) (count n) → ℕ}
    {V D : ℕ} {A : ℕ → ℕ}
    (families : ∀ n q, BoundedPolynomialTestFamily (bound n q) V (A n) D)
    (copyEnvelope testEnvelope : ℕ → ℕ)
    (hW : PolynomiallyBoundedNatAlong seq W)
    (hC : PolynomiallyBoundedNatAlong seq copyEnvelope)
    (hT : PolynomiallyBoundedNatAlong seq testEnvelope)
    (hc : ∀ n γ, count n γ ≤ copyEnvelope n)
    (ht : ∀ n q, (families n q).testCount ≤ testEnvelope n) :
    PolynomiallyBoundedNatAlong seq (fun n => worldCopyFiniteHiddenBinTestCount (families n)) :=
  PolynomiallyBoundedNatAlong.of_le ((hW.mul hC).mul hT)
    (fun n => worldCopyFiniteHiddenBinTestCount_le_envelopes
      (families n) (copyEnvelope n) (testEnvelope n) (hc n) (ht n))

/-- Polynomial atom envelopes are paid after summing all actual world/copy tests. -/
noncomputable def worldCopyFiniteHiddenBinAtomCount_polynomiallyBounded
    {seq : ExactSequence} {W : ℕ → ℕ} {count : ∀ n, Fin (W n) → ℕ}
    {bound : ∀ n, WorldTrajectoryCopyIndex (W n) (count n) → ℕ}
    {V D : ℕ} {A : ℕ → ℕ}
    (families : ∀ n q, BoundedPolynomialTestFamily (bound n q) V (A n) D)
    (copyEnvelope testEnvelope : ℕ → ℕ)
    (hW : PolynomiallyBoundedNatAlong seq W)
    (hC : PolynomiallyBoundedNatAlong seq copyEnvelope)
    (hT : PolynomiallyBoundedNatAlong seq testEnvelope)
    (hA : PolynomiallyBoundedNatAlong seq A)
    (hc : ∀ n γ, count n γ ≤ copyEnvelope n)
    (ht : ∀ n q, (families n q).testCount ≤ testEnvelope n) :
    PolynomiallyBoundedNatAlong seq (fun n => worldCopyFiniteHiddenBinAtomCount (families n)) :=
  PolynomiallyBoundedNatAlong.of_le
    ((worldCopyFiniteHiddenBinTestCount_polynomiallyBounded
      families copyEnvelope testEnvelope hW hC hT hc ht).mul hA)
    (fun n => worldCopyFiniteHiddenBinAtomCount_le_testCount_mul (families n))

/-- The actual global cube-test index keeps the world/copy tag beside every local test. -/
abbrev ScalarCubeWorldCopyHiddenBinTestIndex (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :=
  WorldCopyFiniteHiddenBinTestIndex (scalarCubeWorldCopyHiddenBinTests seq depth n worldData)

/-- Its actual cardinality counts both copies even when all widths and formulas coincide. -/
theorem scalarCubeWorldCopyHiddenBinTestIndex_card (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    Fintype.card (ScalarCubeWorldCopyHiddenBinTestIndex seq depth n worldData) =
      2 * (scalarCubeFiniteHiddenBins seq depth n).card := by
  rw [worldCopyFiniteHiddenBinTestIndex_card]
  exact scalarCubeWorldCopyHiddenBinTestCount_eq_two_mul seq depth n worldData

/-- Model sets live on the actual tagged coordinate space: copies are not extra real variables
and equal tests belonging to different copies remain disjoint by their genuine tags. -/
def scalarCubeWorldCopyHiddenBinTestModels (seq : ExactSequence) (depth : Depth seq)
    (n : ℕ) (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar)
    (index : ScalarCubeWorldCopyHiddenBinTestIndex seq depth n worldData) :
    Set (WorldTrajectoryCopyIndex 1 (fun _ : Fin 1 => 2) ×
      (ObservedBase .scalar × UnobservedFiber .scalar)) :=
  {p | p.1 = index.1 ∧ p.2 ∈ scalarFiniteHiddenBinTestModels 3 (dyadicRoundedWidth
    (seq.depthScale depth n / worldDerivativeScale .scalar
      (worldData index.1.world index.1.copy))) index.2}

/-- The actual global tagged models are disjoint across copies and across local bin labels. -/
theorem scalarCubeWorldCopyHiddenBinTestModels_pairwiseDisjoint
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar) :
    Set.PairwiseDisjoint Set.univ (scalarCubeWorldCopyHiddenBinTestModels seq depth n worldData) := by
  intro s _ t _ hst
  apply Set.disjoint_left.mpr
  intro p hs ht
  rcases s with ⟨q,i⟩
  rcases t with ⟨r,j⟩
  have hqr : q = r := hs.1.symm.trans ht.1
  subst r
  have hw := observation_bin_width_pos .scalar seq depth n
    (fun _ : Fin 1 => worldData q.world q.copy) (0 : Fin 1)
  have hi := (scalarFiniteHiddenBinTestModels_mem_iff 3 _ hw i p.2).mp hs.2
  have hj := (scalarFiniteHiddenBinTestModels_mem_iff 3 _ hw j p.2).mp ht.2
  have hij : i = j := finiteHiddenBinLabel_injective _ (hi.symm.trans hj)
  subst j
  exact hst rfl

/-- Each real selected half-time copy is covered on its own genuine global tag. This consumer
cannot satisfy the statement by assigning another copy's test to the incidence. -/
theorem scalarCubeTwoCopyHalfTimeSelection_ae_taggedFiniteHiddenBinTests_cover
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ _γ : Fin 1, ∀ _i : Fin 2, VersionWorldData .scalar)
    (γ : Fin 1) (i : Fin 2) :
    ∀ᵐ p ∂(scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i).measure
      (scalarCubeTwoCopyHalfTimeSelection.singletonWorldIndex γ i),
      (⟨γ,i⟩, observedCoordinateEquiv .scalar p) ∈
        ⋃ index, scalarCubeWorldCopyHiddenBinTestModels seq depth n worldData index := by
  filter_upwards [scalarCubeTwoCopyHalfTimeSelection_ae_finiteHiddenBinTests_cover
    seq depth n worldData γ i] with p hp
  rcases Set.mem_iUnion.mp hp with ⟨j,hj⟩
  exact Set.mem_iUnion.mpr ⟨⟨⟨γ,i⟩,j⟩,rfl,hj⟩

end Kakeya4.Framework
