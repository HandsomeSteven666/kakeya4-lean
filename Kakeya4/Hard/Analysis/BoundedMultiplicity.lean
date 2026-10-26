import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Compactness.Lindelof

/-!
# Jacobian estimates with bounded overlap of injective branches

Analytic component of the slope-volume argument in manuscript §2
(`02-framework.tex`, equation `a01:selector-volume`).

We reuse Mathlib's injective change-of-variables theorem on each measurable branch.
We construct the measurable injective partition using local inversion and second countability,
then bound image overlaps by actual fiber cardinality. The parameter-uniform fiber bound
remains explicit; no semialgebraic selection or finiteness theorem is assumed implicitly.
-/

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal

namespace Kakeya4.Hard

variable {E : Type*} [MeasurableSpace E]

/-- A countable family of measurable sets with pointwise overlap at most `N`
has total measure at most `N` times the measure of a common measurable target. -/
theorem tsum_measure_le_of_overlap (μ : Measure E) (S : ℕ → Set E)
    (hS : ∀ i, MeasurableSet (S i)) (T : Set E) (hT : MeasurableSet T)
    (N : ℝ≥0∞)
    (hoverlap : ∀ y, (∑' i, (S i).indicator (fun _ => (1 : ℝ≥0∞)) y) ≤
      T.indicator (fun _ => N) y) :
    (∑' i, μ (S i)) ≤ N * μ T := by
  calc
    (∑' i, μ (S i)) =
        ∫⁻ y, ∑' i, (S i).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ := by
      rw [lintegral_tsum (fun i => (measurable_const.indicator (hS i)).aemeasurable)]
      simp only [lintegral_indicator, hS, setLIntegral_const, one_mul]
    _ ≤ ∫⁻ y, T.indicator (fun _ => N) y ∂μ := lintegral_mono hoverlap
    _ = N * μ T := lintegral_indicator_const hT N

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

omit [MeasurableSpace E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Disjoint source branches cannot contribute more image overlaps than actual preimages.
This counts fibers themselves, rather than bounding the total number of branches. -/
theorem tsum_image_indicator_le_fiber (f : E → E) (s : Set E) (S : ℕ → Set E)
    (hsub : ∀ i, S i ⊆ s)
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j))) (y : E) :
    (∑' i, (f '' S i).indicator (fun _ => (1 : ℝ≥0∞)) y) ≤
      ({x ∈ s | f x = y}.encard : ℝ≥0∞) := by
  classical
  let I : Set ℕ := {i | y ∈ f '' S i}
  let pick : ℕ → E := fun i => if hi : i ∈ I then Classical.choose hi else 0
  have hpick (i : ℕ) (hi : i ∈ I) : pick i ∈ S i ∧ f (pick i) = y := by
    simpa only [pick, dite_eq_left hi] using Classical.choose_spec hi
  have hmaps : MapsTo pick I {x ∈ s | f x = y} := by
    intro i hi
    exact ⟨hsub i (hpick i hi).1, (hpick i hi).2⟩
  have hinj : InjOn pick I := by
    intro i hi j hj heq
    by_contra hij
    exact Set.disjoint_left.mp (hdisj hij) (hpick i hi).1 (heq ▸ (hpick j hj).1)
  calc
    (∑' i, (f '' S i).indicator (fun _ => (1 : ℝ≥0∞)) y) =
        ∑' i, I.indicator (fun _ => (1 : ℝ≥0∞)) i := by
      apply tsum_congr
      intro i
      by_cases hi : i ∈ I
      · simp only [Set.indicator_of_mem hi, Set.indicator_of_mem (show y ∈ f '' S i from hi)]
      · simp only [Set.indicator_of_notMem hi,
          Set.indicator_of_notMem (show y ∉ f '' S i from hi)]
    _ = ∑' _i : I, (1 : ℝ≥0∞) := (tsum_subtype I (fun _ => (1 : ℝ≥0∞))).symm
    _ = (I.encard : ℝ≥0∞) := ENNReal.tsum_set_one I
    _ ≤ ({x ∈ s | f x = y}.encard : ℝ≥0∞) :=
      ENat.toENNReal_mono (Set.encard_le_encard_of_injOn hmaps hinj)

/-- Noninjective Jacobian upper bound on a countable disjoint branch decomposition.
Only the injective formula is imported from Mathlib; all branch-overlap losses are explicit. -/
theorem lintegral_abs_det_le_of_branches (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E)
    (S : ℕ → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hderiv : ∀ i, ∀ x ∈ S i, HasFDerivWithinAt f (f' x) (S i) x)
    (hinj : ∀ i, InjOn f (S i))
    (T : Set E) (hT : MeasurableSet T) (N : ℝ≥0∞)
    (hoverlap : ∀ y, (∑' i, (f '' S i).indicator (fun _ => (1 : ℝ≥0∞)) y) ≤
      T.indicator (fun _ => N) y) :
    (∫⁻ x in ⋃ i, S i, ENNReal.ofReal |(f' x).det| ∂μ) ≤ N * μ T := by
  rw [lintegral_iUnion hS hdisj]
  simp_rw [lintegral_abs_det_fderiv_eq_addHaar_image μ (hS _) (hderiv _) (hinj _)]
  exact tsum_measure_le_of_overlap μ (fun i => f '' S i)
    (fun i => measurable_image_of_fderivWithin (hS i) (hderiv i) (hinj i)) T hT N hoverlap

/-- A Jacobian lower bound turns the branch estimate into the volume comparison
used in the slope-volume argument. No finiteness of the source measure is required. -/
theorem mul_measure_le_of_branches (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E)
    (S : ℕ → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hderiv : ∀ i, ∀ x ∈ S i, HasFDerivWithinAt f (f' x) (S i) x)
    (hinj : ∀ i, InjOn f (S i))
    (T : Set E) (hT : MeasurableSet T) (N a : ℝ≥0∞)
    (hlower : ∀ x ∈ ⋃ i, S i, a ≤ ENNReal.ofReal |(f' x).det|)
    (hoverlap : ∀ y, (∑' i, (f '' S i).indicator (fun _ => (1 : ℝ≥0∞)) y) ≤
      T.indicator (fun _ => N) y) :
    a * μ (⋃ i, S i) ≤ N * μ T := by
  calc
    a * μ (⋃ i, S i) = ∫⁻ _x in ⋃ i, S i, a ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in ⋃ i, S i, ENNReal.ofReal |(f' x).det| ∂μ := by
      exact setLIntegral_mono' (MeasurableSet.iUnion hS) hlower
    _ ≤ N * μ T := lintegral_abs_det_le_of_branches μ f f' S hS hdisj hderiv hinj T hT N hoverlap

/-- Bounded-fiber volume comparison, given a countable measurable injective partition.
The loss is the fiber bound `N`, independent of the number of partition pieces. -/
theorem mul_measure_le_of_fiber_bound (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E)
    (S : ℕ → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hderiv : ∀ i, ∀ x ∈ S i, HasFDerivWithinAt f (f' x) (S i) x)
    (hinj : ∀ i, InjOn f (S i))
    (T : Set E) (hT : MeasurableSet T) (N : ℕ) (a : ℝ≥0∞)
    (hmap : MapsTo f (⋃ i, S i) T)
    (hfiber : ∀ y, {x ∈ ⋃ i, S i | f x = y}.encard ≤ N)
    (hlower : ∀ x ∈ ⋃ i, S i, a ≤ ENNReal.ofReal |(f' x).det|) :
    a * μ (⋃ i, S i) ≤ (N : ℝ≥0∞) * μ T := by
  classical
  apply mul_measure_le_of_branches μ f f' S hS hdisj hderiv hinj T hT N a hlower
  intro y
  by_cases hy : y ∈ T
  · rw [Set.indicator_of_mem hy]
    exact (tsum_image_indicator_le_fiber f (⋃ i, S i) S (fun i => subset_iUnion S i)
      hdisj y).trans (by exact_mod_cast ENat.toENNReal_mono (hfiber y))
  · rw [Set.indicator_of_notMem hy]
    have hnot (i : ℕ) : y ∉ f '' S i := by
      rintro ⟨x, hx, rfl⟩
      exact hy (hmap (mem_iUnion.mpr ⟨i, hx⟩))
    simp only [Set.indicator_of_notMem (hnot _), tsum_zero, le_refl]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A locally injective map on a measurable set admits a countable disjoint measurable
partition into injective sets. This is a topological decomposition, with no semialgebraic input. -/
theorem exists_injective_partition [SecondCountableTopology E] (f : E → E)
    (s : Set E) (hs : MeasurableSet s)
    (hlocal : ∀ x ∈ s, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ InjOn f (s ∩ U)) :
    ∃ S : ℕ → Set E, (∀ i, MeasurableSet (S i)) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧ (⋃ i, S i) = s ∧
      ∀ i, InjOn f (S i) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => ∅, fun _ => MeasurableSet.empty,
      by intro i j hij; simp, by simp, fun _ => injOn_empty f⟩
  have : Nonempty s := hne.to_subtype
  choose U hopen hmem hinj using (fun x : s => hlocal x x.property)
  have hcover : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  obtain ⟨v, hv⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
    U hopen hcover
  let A : ℕ → Set E := fun n => s ∩ U (v n)
  have hA : (⋃ n, A n) = s := by
    apply Subset.antisymm
    · exact iUnion_subset (fun _ => inter_subset_left)
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hv hx)
      exact mem_iUnion.mpr ⟨n, hx, hn⟩
  refine ⟨disjointed A, MeasurableSet.disjointed (fun n => hs.inter (hopen (v n)).measurableSet),
    disjoint_disjointed A, ?_, ?_⟩
  · rw [iUnion_disjointed, hA]
  · intro n
    exact (hinj (v n)).mono (disjointed_subset A n)

/-- The finite-multiplicity volume estimate on any measurable locally injective domain.
In particular the constant does not grow with the size of a countable branch cover. -/
theorem mul_measure_le_of_locally_injective [SecondCountableTopology E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E) (s : Set E) (hs : MeasurableSet s)
    (hlocal : ∀ x ∈ s, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ InjOn f (s ∩ U))
    (hderiv : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (T : Set E) (hT : MeasurableSet T) (N : ℕ) (a : ℝ≥0∞)
    (hmap : MapsTo f s T) (hfiber : ∀ y, {x ∈ s | f x = y}.encard ≤ N)
    (hlower : ∀ x ∈ s, a ≤ ENNReal.ofReal |(f' x).det|) :
    a * μ s ≤ (N : ℝ≥0∞) * μ T := by
  obtain ⟨S, hS, hdisj, hcover, hinj⟩ := exists_injective_partition f s hs hlocal
  have hsub (i : ℕ) : S i ⊆ s := hcover ▸ subset_iUnion S i
  have hderiv' : ∀ i, ∀ x ∈ S i, HasFDerivWithinAt f (f' x) (S i) x := by
    intro i x hx
    exact (hderiv x (hsub i hx)).mono (hsub i)
  have h := mul_measure_le_of_fiber_bound μ f f' S hS hdisj hderiv' hinj T hT N a
  rw [hcover] at h
  exact h hmap hfiber hlower

omit [MeasurableSpace E] [BorelSpace E] in
/-- A nonzero Jacobian of a `C¹` map provides the local injectivity needed above.
Only pointwise `C¹` regularity is needed; the measured subset need not be open. -/
theorem locally_injective_of_contDiffAt (f : E → E) (f' : E → E →L[ℝ] E)
    (s : Set E) (hC : ∀ x ∈ s, ContDiffAt ℝ 1 f x)
    (hderiv : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0) :
    ∀ x ∈ s, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ InjOn f (s ∩ U) := by
  intro x hx
  let A := (f' x).toContinuousLinearEquivOfDetNeZero (hdet x hx)
  have hA : HasFDerivAt f (A : E →L[ℝ] E) x := by
    simpa only [A, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
      using hderiv x hx
  let e := (hC x hx).toOpenPartialHomeomorph f hA one_ne_zero
  exact ⟨e.source, e.open_source,
    (hC x hx).mem_toOpenPartialHomeomorph_source hA one_ne_zero,
    e.injOn.mono inter_subset_right⟩

/-- Analytic finite-multiplicity estimate needed for the eligible-slope-volume bound.
All semialgebraic information is confined to the explicit regular-fiber bound `hfiber`. -/
theorem mul_measure_le_of_regular_fibers [SecondCountableTopology E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E) (s : Set E) (hs : MeasurableSet s)
    (hC : ∀ x ∈ s, ContDiffAt ℝ 1 f x)
    (hderiv : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0)
    (T : Set E) (hT : MeasurableSet T) (N : ℕ) (a : ℝ≥0∞)
    (hmap : MapsTo f s T) (hfiber : ∀ y, {x ∈ s | f x = y}.encard ≤ N)
    (hlower : ∀ x ∈ s, a ≤ ENNReal.ofReal |(f' x).det|) :
    a * μ s ≤ (N : ℝ≥0∞) * μ T :=
  mul_measure_le_of_locally_injective μ f f' s hs
    (locally_injective_of_contDiffAt f f' s hC hderiv hdet)
    (fun x hx => (hderiv x hx).hasFDerivWithinAt) T hT N a hmap hfiber hlower

end Kakeya4.Hard
