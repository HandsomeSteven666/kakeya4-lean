import Experiments.FiniteBins.FiniteHiddenBinTests

/-!
# The actual scalar cube and half-time source in observed coordinates

The inverse shear is polynomial of degree two. The closed time endpoints are retained.
This isolated module does not alter the frozen production acceptance batch.
-/
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace Kakeya4.Framework

/-- The original five coefficients as polynomials in `(t,y,V,w0,w1,w2)`. -/
noncomputable def scalarObservedSourceCoefficient (i : Fin 5) : MvPolynomial (Fin 6) ℝ :=
  ![MvPolynomial.X 1 - MvPolynomial.X 0 * MvPolynomial.X 2,
    MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4, MvPolynomial.X 5] i

/-- The actual inverse shear has coefficient degree at most two. -/
theorem scalarObservedSourceCoefficient_degree (i : Fin 5) :
    (scalarObservedSourceCoefficient i).totalDegree ≤ 2 := by
  fin_cases i <;> simp only [scalarObservedSourceCoefficient]
  · rw [sub_eq_add_neg]
    apply (MvPolynomial.totalDegree_add _ _).trans
    simp only [MvPolynomial.totalDegree_neg, max_le_iff, MvPolynomial.totalDegree_X]
    exact ⟨by omega, (MvPolynomial.totalDegree_mul _ _).trans (by simp)⟩
  all_goals simp

/-- Two closed polynomial inequalities for membership in the unit coefficient interval. -/
noncomputable def scalarObservedSourceUnitFormula (i : Fin 5) : PolynomialBooleanFormula 6 :=
  .conjunction (.nonnegative (scalarObservedSourceCoefficient i + MvPolynomial.C 1))
    (.nonnegative (MvPolynomial.C 1 - scalarObservedSourceCoefficient i))

/-- The actual selected source, with ten cube atoms and two closed half-time atoms. -/
noncomputable def scalarObservedSelectedSourceFormula : PolynomialBooleanFormula 6 :=
  .conjunction (scalarObservedSourceUnitFormula 0)
    (.conjunction (scalarObservedSourceUnitFormula 1)
      (.conjunction (scalarObservedSourceUnitFormula 2)
        (.conjunction (scalarObservedSourceUnitFormula 3)
          (.conjunction (scalarObservedSourceUnitFormula 4)
            (.conjunction (.nonnegative (MvPolynomial.X 0))
              (.nonnegative (MvPolynomial.C (1/2 : ℝ) - MvPolynomial.X 0)))))))

/-- Exact atom count, including the two event endpoints. -/
theorem scalarObservedSelectedSourceFormula_atomCount :
    scalarObservedSelectedSourceFormula.atomCount = 12 := by rfl

private theorem scalarObservedSourceUnitFormula_degree (i : Fin 5) :
    (scalarObservedSourceUnitFormula i).maxAtomDegree ≤ 2 := by
  change max _ _ ≤ 2
  apply max_le
  · exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (scalarObservedSourceCoefficient_degree i) (by simp))
  · rw [sub_eq_add_neg]
    exact (MvPolynomial.totalDegree_add _ _).trans (by
      simpa using max_le (show (0:ℕ) ≤ 2 by omega)
        (scalarObservedSourceCoefficient_degree i))

/-- Uniform quadratic degree; no scale or world parameter enters this bound. -/
theorem scalarObservedSelectedSourceFormula_degree :
    scalarObservedSelectedSourceFormula.maxAtomDegree ≤ 2 := by
  simp only [scalarObservedSelectedSourceFormula, PolynomialBooleanFormula.maxAtomDegree,
    max_le_iff]
  refine ⟨scalarObservedSourceUnitFormula_degree 0,
    scalarObservedSourceUnitFormula_degree 1, scalarObservedSourceUnitFormula_degree 2,
    scalarObservedSourceUnitFormula_degree 3, scalarObservedSourceUnitFormula_degree 4,
    ?_, ?_⟩
  · simp
  · rw [sub_eq_add_neg]
    exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

/-- A produced six-variable, twelve-atom, degree-two bounded test. -/
noncomputable def scalarObservedSelectedSourceBoundedTest : BoundedPolynomialTest 6 12 2 where
  variableCount := 6
  variableCount_le := le_rfl
  formula := scalarObservedSelectedSourceFormula
  atomCount_le := scalarObservedSelectedSourceFormula_atomCount.le
  degree_le := scalarObservedSelectedSourceFormula_degree

/-- Evaluation recovers the original trajectory coefficients under the true inverse chart. -/
theorem scalarObservedSourceCoefficient_eval
    (p : ObservedBase .scalar × UnobservedFiber .scalar) (i : Fin 5) :
    MvPolynomial.eval (scalarObservedHiddenBinCoordinates p)
      (scalarObservedSourceCoefficient i) =
    scalarTrajectoryFinMeasurableEquiv (((observedCoordinateEquiv .scalar).symm p).1) i := by
  rcases p with ⟨⟨t,y⟩, ⟨v,w0,w1,w2⟩⟩
  fin_cases i <;> simp [scalarObservedSourceCoefficient, scalarObservedHiddenBinCoordinates,
    scalarTrajectoryFinMeasurableEquiv, scalarTrajectoryCoords,
    observedCoordinateEquiv, scalarObservedFiberEquiv] <;> rfl

/-- The polynomial formula describes exactly the original cube and original selected event. -/
theorem scalarObservedSelectedSourceFormula_mem_iff
    (p : ObservedBase .scalar × UnobservedFiber .scalar) :
    scalarObservedHiddenBinCoordinates p ∈ scalarObservedSelectedSourceFormula.models ↔
      scalarTrajectoryFinMeasurableEquiv (((observedCoordinateEquiv .scalar).symm p).1)
        ∈ scalarCoefficientCube ∧
      (observedCoordinateEquiv .scalar).symm p ∈ scalarHalfTimeEvent := by
  have hevent : (observedCoordinateEquiv .scalar).symm p ∈ scalarHalfTimeEvent ↔
      0 ≤ p.1.1 ∧ p.1.1 ≤ 1/2 := by
    rcases p with ⟨⟨t,y⟩, ⟨v,w0,w1,w2⟩⟩
    change (True ∧ 0 ≤ t ∧ t ≤ 1/2) ↔ _
    simp
  rw [hevent]
  simp only [PolynomialBooleanFormula.models, Set.mem_ofPred_eq,
    scalarObservedSelectedSourceFormula, scalarObservedSourceUnitFormula,
    PolynomialBooleanFormula.Holds, map_add, map_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X, scalarObservedSourceCoefficient_eval]
  simp only [scalarCoefficientCube, Set.mem_Icc, Pi.le_def]
  have hcoord : scalarObservedHiddenBinCoordinates p 0 = p.1.1 := rfl
  rw [hcoord]
  constructor
  · rintro ⟨⟨a,b⟩,⟨c,d⟩,⟨e,f⟩,⟨g,h⟩,⟨i,j⟩,k,l⟩
    refine ⟨⟨?_, ?_⟩, k, ?_⟩
    · intro z; fin_cases z <;> simp at * <;> linarith
    · intro z; fin_cases z <;> simp at * <;> linarith
    · linarith
  · rintro ⟨⟨hl,hu⟩,ht,ht'⟩
    exact ⟨⟨by linarith [hl 0], by linarith [hu 0]⟩,
      ⟨by linarith [hl 1], by linarith [hu 1]⟩,
      ⟨by linarith [hl 2], by linarith [hu 2]⟩,
      ⟨by linarith [hl 3], by linarith [hu 3]⟩,
      ⟨by linarith [hl 4], by linarith [hu 4]⟩, ht, by linarith⟩

/-- The true selected support in observed/fiber coordinates. -/
def scalarObservedSelectedSource : Set (ObservedBase .scalar × UnobservedFiber .scalar) :=
  scalarObservedHiddenBinCoordinates ⁻¹' scalarObservedSelectedSourceFormula.models

/-- The actual selected coordinate density, using the existing internally produced cube certificate,
is exactly `1/32` on this polynomial source and zero elsewhere. -/
theorem scalarCubeHalfTimeSelection_selectedObservedCoordinateDensity
    (γ : Fin 1) :
    selectedObservedCoordinateDensity scalarCubeHalfTimeSelection
      (trajectoryPriorDensityCertificates_of_standardSemialgebraic .scalar
        scalarCubeHalfTimeSelection.priors 2 5 10 1 (ENNReal.ofReal (1/32 : ℝ))
        (fun _ => scalarCubeStandardDensityCertificate)) γ =
      scalarObservedSelectedSource.indicator (fun _ => ENNReal.ofReal (1/32 : ℝ)) := by
  funext p
  have hevent : p ∈ (observedCoordinateEquiv .scalar) '' scalarHalfTimeEvent ↔
      (observedCoordinateEquiv .scalar).symm p ∈ scalarHalfTimeEvent :=
    by
      constructor
      · rintro ⟨q,hq,rfl⟩
        erw [(observedCoordinateEquiv .scalar).symm_apply_apply]
        exact hq
      · intro hp
        exact ⟨_,hp,(observedCoordinateEquiv .scalar).apply_symm_apply p⟩
  have hsource : p ∈ scalarObservedSelectedSource ↔
      scalarTrajectoryFinMeasurableEquiv (((observedCoordinateEquiv .scalar).symm p).1)
        ∈ scalarCoefficientCube ∧
      (observedCoordinateEquiv .scalar).symm p ∈ scalarHalfTimeEvent :=
    scalarObservedSelectedSourceFormula_mem_iff p
  change ((observedCoordinateEquiv .scalar) '' scalarHalfTimeEvent).indicator
    (fun p => scalarCubeDensity
      (scalarTrajectoryFinMeasurableEquiv (((observedCoordinateEquiv .scalar).symm p).1))) p = _
  by_cases ht : (observedCoordinateEquiv .scalar).symm p ∈ scalarHalfTimeEvent
  · rw [Set.indicator_of_mem (hevent.mpr ht)]
    by_cases hc : scalarTrajectoryFinMeasurableEquiv
        (((observedCoordinateEquiv .scalar).symm p).1) ∈ scalarCoefficientCube
    · rw [Set.indicator_of_mem (hsource.mpr ⟨hc,ht⟩)]
      exact Set.indicator_of_mem hc _
    · rw [Set.indicator_of_notMem (fun h => hc (hsource.mp h).1)]
      exact Set.indicator_of_notMem hc _
  · rw [Set.indicator_of_notMem (fun h => ht (hevent.mp h)),
      Set.indicator_of_notMem (fun h => ht (hsource.mp h).2)]

/-- The actual source-bin pieces combine the produced source test and genuine half-open bin. -/
noncomputable def scalarSelectedSourceBinFormula (width : ℝ) (j : ℤ) :
    PolynomialBooleanFormula 6 :=
  .conjunction scalarObservedSelectedSourceFormula (scalarObservedHiddenBinFormula width j)

/-- Exact per-piece atom count; source atoms are not omitted from complexity accounting. -/
theorem scalarSelectedSourceBinFormula_atomCount (width : ℝ) (j : ℤ) :
    (scalarSelectedSourceBinFormula width j).atomCount = 14 := by rfl

/-- The genuine cubic hidden bin controls the combined degree. -/
theorem scalarSelectedSourceBinFormula_degree (width : ℝ) (j : ℤ) :
    (scalarSelectedSourceBinFormula width j).maxAtomDegree ≤ 3 := by
  exact max_le (scalarObservedSelectedSourceFormula_degree.trans (by omega))
    (scalarObservedHiddenBinFormula_degree width j)

/-- A bounded test produced from both actual predicates. -/
noncomputable def scalarSelectedSourceBinBoundedTest (width : ℝ) (j : ℤ) :
    BoundedPolynomialTest 6 14 3 where
  variableCount := 6
  variableCount_le := le_rfl
  formula := scalarSelectedSourceBinFormula width j
  atomCount_le := (scalarSelectedSourceBinFormula_atomCount width j).le
  degree_le := scalarSelectedSourceBinFormula_degree width j

/-- The combined formula retains the actual source and exact original integer bin. -/
theorem scalarSelectedSourceBinFormula_mem_iff (width : ℝ) (hw : 0 < width) (j : ℤ)
    (p : ObservedBase .scalar × UnobservedFiber .scalar) :
    scalarObservedHiddenBinCoordinates p ∈ (scalarSelectedSourceBinFormula width j).models ↔
      p ∈ scalarObservedSelectedSource ∧ observedFiberHiddenBin .scalar p.1 p.2 width = j := by
  exact and_congr Iff.rfl (scalarObservedHiddenBinFormula_mem_iff width hw j p)

/-- Each real copy of the accepted two-copy selection has the same explicit source indicator,
using the actual internally produced certificate at every index. Copy weights remain external. -/
theorem scalarCubeTwoCopyHalfTimeSelection_selectedObservedCoordinateDensity
    (seq : ExactSequence) (n : ℕ) (γ : Fin 1) (i : Fin 2) :
    selectedObservedCoordinateDensity (scalarCubeTwoCopyHalfTimeSelection.singletonSelection γ i)
      (scalarCubeTwoCopyActualDensityCertificates seq n γ i) (0 : Fin 1) =
      scalarObservedSelectedSource.indicator (fun _ => ENNReal.ofReal (1/32 : ℝ)) := by
  exact scalarCubeHalfTimeSelection_selectedObservedCoordinateDensity (0 : Fin 1)

/-- On the actual polynomial selected source the hidden bin is in the internally bounded family,
pointwise, rather than merely almost everywhere for a chosen law. -/
theorem scalarObservedSelectedSource_hiddenBin_mem (width : ℝ) (hw : 0 < width)
    (p : ObservedBase .scalar × UnobservedFiber .scalar)
    (hp : p ∈ scalarObservedSelectedSource) :
    observedFiberHiddenBin .scalar p.1 p.2 width ∈ boundedScalarHiddenBins 3 width := by
  rcases (scalarObservedSelectedSourceFormula_mem_iff p).mp hp with ⟨hc,ht⟩
  have ht' : ((observedCoordinateEquiv .scalar).symm p).2 ∈ Set.Icc (0 : ℝ) 1 := by
    have ht'' : ((observedCoordinateEquiv .scalar).symm p).2 ∈
        Set.Icc (0 : ℝ) (1/2) := ht.2
    exact ⟨ht''.1, ht''.2.trans (by norm_num)⟩
  have hbin := scalarCube_hiddenBin_mem_boundedScalarHiddenBins _ _ width hw hc ht'
  have heq := observedFiberHiddenBin_observedCoordinateEquiv .scalar
    ((observedCoordinateEquiv .scalar).symm p) width
  simpa only [MeasurableEquiv.apply_symm_apply] using heq.symm ▸ hbin

/-- Actual finite source-bin family; its count and labels are produced from the true range. -/
noncomputable def scalarSelectedSourceBinTestFamily (width : ℝ) :
    BoundedPolynomialTestFamily (boundedScalarHiddenBins 3 width).card 6 14 3 where
  testCount := (boundedScalarHiddenBins 3 width).card
  testCount_le := le_rfl
  test i := scalarSelectedSourceBinBoundedTest width
    (finiteHiddenBinLabel (boundedScalarHiddenBins 3 width) i)

/-- Read the actual test formula through the real observed/fiber coordinates. -/
def scalarSelectedSourceBinTestModels (width : ℝ)
    (i : Fin (boundedScalarHiddenBins 3 width).card) :
    Set (ObservedBase .scalar × UnobservedFiber .scalar) :=
  {p | scalarObservedHiddenBinCoordinates p ∈
    ((scalarSelectedSourceBinTestFamily width).test i).formula.models}

/-- The finite positive-density pieces cover exactly the actual selected source. -/
theorem scalarSelectedSourceBinTestModels_cover (width : ℝ) (hw : 0 < width) :
    (⋃ i, scalarSelectedSourceBinTestModels width i) = scalarObservedSelectedSource := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨i,hi⟩
    exact ((scalarSelectedSourceBinFormula_mem_iff width hw _ p).mp hi).1
  · intro hp
    rcases exists_finiteHiddenBinLabel_eq (boundedScalarHiddenBins 3 width) _
      (scalarObservedSelectedSource_hiddenBin_mem width hw p hp) with ⟨i,hi⟩
    exact Set.mem_iUnion.mpr ⟨i,
      (scalarSelectedSourceBinFormula_mem_iff width hw _ p).mpr ⟨hp,hi.symm⟩⟩

/-- Distinct positive-density pieces remain disjoint, including all half-open boundaries. -/
theorem scalarSelectedSourceBinTestModels_pairwiseDisjoint (width : ℝ) (hw : 0 < width) :
    Set.PairwiseDisjoint Set.univ (scalarSelectedSourceBinTestModels width) := by
  intro i _ j _ hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have hi' := ((scalarSelectedSourceBinFormula_mem_iff width hw _ p).mp hi).2
  have hj' := ((scalarSelectedSourceBinFormula_mem_iff width hw _ p).mp hj).2
  exact hij (finiteHiddenBinLabel_injective _ (hi'.symm.trans hj'))

/-- The actual six-coordinate map is measurable, not an assumed source chart. -/
theorem scalarObservedHiddenBinCoordinates_measurable : Measurable scalarObservedHiddenBinCoordinates := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i <;> dsimp [scalarObservedHiddenBinCoordinates] <;> fun_prop

/-- The produced polynomial source is measurable in the genuine observed/fiber space. -/
theorem scalarObservedSelectedSource_measurable : MeasurableSet scalarObservedSelectedSource :=
  scalarObservedSelectedSourceFormula.measurableSet_models.preimage
    scalarObservedHiddenBinCoordinates_measurable

/-- Exact atom accounting across every positive-density source-bin piece. -/
theorem scalarSelectedSourceBinTestFamily_totalAtomCount (width : ℝ) :
    (∑ i : Fin (scalarSelectedSourceBinTestFamily width).testCount,
      ((scalarSelectedSourceBinTestFamily width).test i).formula.atomCount) =
      14 * (boundedScalarHiddenBins 3 width).card := by
  change (∑ _i : Fin (boundedScalarHiddenBins 3 width).card, (14 : ℕ)) = _
  simp [mul_comm]

/-- The actual selected law has an explicit source-indicator density over `dt dy × fiber`.
The unit-time base and the closed half-time event remain the original ones. -/
theorem scalarCubeHalfTimeSelection_observedCoordinateLaw_sourceIndicator (γ : Fin 1) :
    (scalarCubeHalfTimeSelection.measure γ).map (observedCoordinateEquiv .scalar) =
      (observedCoordinateProductReference .scalar).withDensity
        (scalarObservedSelectedSource.indicator (fun _ => ENNReal.ofReal (1/32 : ℝ))) := by
  rw [scalarCubeHalfTimeSelection.observedCoordinateMeasure_eq_withDensity
    (trajectoryPriorDensityCertificates_of_standardSemialgebraic .scalar
      scalarCubeHalfTimeSelection.priors 2 5 10 1 (ENNReal.ofReal (1/32 : ℝ))
      (fun _ => scalarCubeStandardDensityCertificate)) γ]
  exact congrArg (fun f => (observedCoordinateProductReference .scalar).withDensity f)
    (scalarCubeHalfTimeSelection_selectedObservedCoordinateDensity γ)

/-- A real two-piece density certificate is produced for the selected observed-coordinate law,
relative to the unrestricted base/fiber product reference. Its pieces are the proved polynomial
source and its complement; no caller supplies a source-density certificate. -/
noncomputable def scalarCubeHalfTimeSelectedSourceDensityCertificate (γ : Fin 1) :
    FinitePiecewiseDensityCertificate (observedCoordinateProductReference .scalar)
      ((scalarCubeHalfTimeSelection.measure γ).map (observedCoordinateEquiv .scalar)) where
  pieceCount := 2
  pieces i := if i.val = 0 then scalarObservedSelectedSource else scalarObservedSelectedSourceᶜ
  pieces_measurable i := by
    split_ifs
    · exact scalarObservedSelectedSource_measurable
    · exact scalarObservedSelectedSource_measurable.compl
  pieces_pairwise_disjoint := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp_all [Function.onFun]
    all_goals
      apply Set.disjoint_left.mpr
      intro p hp hn
      first | exact hn hp | exact hp hn
  pieces_cover := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hp : p ∈ scalarObservedSelectedSource
    · exact ⟨0, by simpa using hp⟩
    · exact ⟨1, by simpa using hp⟩
  density := scalarObservedSelectedSource.indicator (fun _ => ENNReal.ofReal (1/32 : ℝ))
  density_measurable := measurable_const.indicator scalarObservedSelectedSource_measurable
  value i := if i.val = 0 then ENNReal.ofReal (1/32 : ℝ) else 0
  density_eq_value := by
    intro i p hp
    by_cases hi : i.val = 0
    · simp only [hi, ite_true] at hp ⊢
      exact Set.indicator_of_mem hp _
    · simp only [hi, ite_false] at hp ⊢
      exact Set.indicator_of_notMem hp _
  prior_eq_withDensity := scalarCubeHalfTimeSelection_observedCoordinateLaw_sourceIndicator γ

end Kakeya4.Framework
