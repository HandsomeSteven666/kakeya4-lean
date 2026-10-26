import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Basic.NNReal.Basic

/-!
# Finite disjoint-union mass aggregation

The local finite-scale Kakeya estimate is applied to separate spatial cells. When a fixed
geometric coloring makes their shaded unions pairwise disjoint, this lemma sums their local
volume lower bounds without introducing a factor depending on the number of cells.
-/

set_option autoImplicit false

namespace Kakeya4.Construction

open scoped ENNReal
open scoped NNReal

/-- Sum common-factor local mass bounds over a finite family of measurable, pairwise disjoint
shaded regions. The result is a lower bound for the measure of their union, with no cell-count
loss. -/
theorem measure_biUnion_ge_const_mul_sum {α ι : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (cells : Finset ι) (shade : ι → Set α)
    (mass : ι → ℝ≥0∞) (c : ℝ≥0∞)
    (hdisjoint : Set.PairwiseDisjoint (↑cells) shade)
    (hmeas : ∀ i ∈ cells, MeasurableSet (shade i))
    (hlocal : ∀ i ∈ cells, c * mass i ≤ μ (shade i)) :
    c * ∑ i ∈ cells, mass i ≤ μ (⋃ i ∈ cells, shade i) := by
  calc
    c * ∑ i ∈ cells, mass i = ∑ i ∈ cells, c * mass i := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ cells, μ (shade i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hlocal i hi
    _ = μ (⋃ i ∈ cells, shade i) := (MeasureTheory.measure_biUnion_finset hdisjoint hmeas).symm

/-- A finite weighted family of local estimates has one phase whose pairwise-disjoint shades
carry a prescribed share of the total mass. The geometric phase assignment and local bounds are
explicit inputs; this theorem only performs finite weighted selection and measure aggregation. -/
theorem exists_phase_union_measure_ge_const_mul_mass_of_fintype
    {α ι γ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype γ] [DecidableEq γ]
    [Nonempty γ]
    (μ : MeasureTheory.Measure α)
    (cells : Finset ι) (phase : ι → γ) (shade : ι → Set α)
    (mass : ι → ℝ≥0) (c b : ℝ≥0)
    (hphaseMass : (Fintype.card γ : ℕ) • b ≤ ∑ i ∈ cells, mass i)
    (hdisjoint : ∀ j, Set.PairwiseDisjoint
      (↑(cells.filter fun i => phase i = j)) shade)
    (hmeas : ∀ i ∈ cells, MeasurableSet (shade i))
    (hlocal : ∀ i ∈ cells,
      (c : ℝ≥0∞) * (mass i : ℝ≥0∞) ≤ μ (shade i)) :
    ∃ j, (c : ℝ≥0∞) * b ≤ μ (⋃ i ∈ cells.filter (fun i => phase i = j), shade i) := by
  classical
  let phaseWeight : ι → ℝ≥0 := fun i => if i ∈ cells then mass i else 0
  let phaseCells : γ → Finset ι := fun j => cells.filter fun i => phase i = j
  have htotal : Fintype.card γ • b ≤ ∑ i, phaseWeight i := by
    simpa [phaseWeight, Finset.sum_ite_mem] using hphaseMass
  obtain ⟨j, hj⟩ := Fintype.exists_le_sum_fiber_of_nsmul_le_sum
    (f := phase) (w := phaseWeight) htotal
  have hphaseSet : phaseCells j =
      (Finset.univ.filter (fun i : ι => phase i = j)).filter (fun i => i ∈ cells) := by
    ext i
    simp [phaseCells, and_comm]
  have hfiber : (∑ i with phase i = j, phaseWeight i) =
      ∑ i ∈ phaseCells j, mass i := by
    calc
      (∑ i with phase i = j, phaseWeight i) =
          ∑ i ∈ Finset.univ.filter (fun i : ι => phase i = j),
            if i ∈ cells then mass i else 0 := by
        simp [phaseWeight]
      _ = ∑ i ∈ phaseCells j, mass i := by
        rw [← Finset.sum_filter, ← hphaseSet]
  have hselected : b ≤ ∑ i ∈ phaseCells j, mass i := by
    rw [← hfiber]
    exact hj
  have hsubset : phaseCells j ⊆ cells := Finset.filter_subset _ _
  let massENN : ι → ℝ≥0∞ := fun i => mass i
  have hselectedENN : (b : ℝ≥0∞) ≤ ∑ i ∈ phaseCells j, massENN i := by
    have hcast : (b : ℝ≥0∞) ≤ ∑ i ∈ phaseCells j, (mass i : ℝ≥0∞) := by
      exact_mod_cast hselected
    simpa [massENN] using hcast
  have hunion := measure_biUnion_ge_const_mul_sum μ (phaseCells j) shade massENN c
    (hdisjoint j)
    (fun i hi => hmeas i (hsubset hi))
    (fun i hi => hlocal i (hsubset hi))
  refine ⟨j, ?_⟩
  calc
    (c : ℝ≥0∞) * b ≤ (c : ℝ≥0∞) * ∑ i ∈ phaseCells j, massENN i :=
      by gcongr
    _ ≤ μ (⋃ i ∈ phaseCells j, shade i) := hunion

/-- `Fin k` wrapper for `exists_phase_union_measure_ge_const_mul_mass_of_fintype`.
This keeps the original API while allowing concrete grid color types to use the general theorem. -/
theorem exists_phase_union_measure_ge_const_mul_mass
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {k : ℕ} (hk : 0 < k)
    (μ : MeasureTheory.Measure α)
    (cells : Finset ι) (phase : ι → Fin k) (shade : ι → Set α)
    (mass : ι → ℝ≥0) (c b : ℝ≥0)
    (hphaseMass : (Fintype.card (Fin k) : ℕ) • b ≤ ∑ i ∈ cells, mass i)
    (hdisjoint : ∀ j, Set.PairwiseDisjoint
      (↑(cells.filter fun i => phase i = j)) shade)
    (hmeas : ∀ i ∈ cells, MeasurableSet (shade i))
    (hlocal : ∀ i ∈ cells,
      (c : ℝ≥0∞) * (mass i : ℝ≥0∞) ≤ μ (shade i)) :
    ∃ j, (c : ℝ≥0∞) * b ≤ μ (⋃ i ∈ cells.filter (fun i => phase i = j), shade i) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact exists_phase_union_measure_ge_const_mul_mass_of_fintype μ cells phase shade mass c b
    hphaseMass hdisjoint hmeas hlocal

end Kakeya4.Construction
