import Kakeya4.Hard.MultiplicativeConvolution.ExtractedSetTransport

/-!
# Joint original mass through coordinatewise actual probability restrictions

The same original product law is restricted to the good rectangle. Exact
normalization retains independence, and the discarded joint mass is paid once
by the sum of the actual marginal losses. Test sets may be nonmeasurable.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Actual rectangle on which every coordinate is retained. -/
def coordinateGoodSet {ι : Type*} (A : ι → Set ℝ) : Set (ι → ℝ) := Set.univ.pi A

/-- The simultaneous good rectangle is Borel. -/
theorem measurableSet_coordinateGoodSet {ι : Type*} [Fintype ι] (A : ι → Set ℝ)
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (coordinateGoodSet A) :=
  MeasurableSet.univ_pi hA

/-- The actual joint discarded mass is no larger than the sum of marginal discarded masses. -/
theorem coordinateGoodSet_compl_mass {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) :
    Measure.pi μ (coordinateGoodSet A)ᶜ ≤ ∑ i, μ i (A i)ᶜ := by
  classical
  have heq : (coordinateGoodSet A)ᶜ = ⋃ i, (Function.eval i) ⁻¹' (A i)ᶜ := by
    ext x
    simp [coordinateGoodSet]
  rw [heq]
  apply (measure_iUnion_fintype_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun ν : Measure ℝ ↦ ν (A i)ᶜ) (measurePreserving_eval μ i).map_eq
  rw [Measure.map_apply (measurable_pi_apply i) (hA i).compl] at h
  exact h

/-- Exact scalar identity between the restricted product and the product of normalized restrictions. -/
theorem pi_restriction_eq_mass_smul_normalized {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA0 : ∀ i, μ i (A i) ≠ 0) :
    Measure.pi (fun i ↦ (μ i).restrict (A i)) =
      (∏ i, μ i (A i)) • Measure.pi (fun i ↦ normalizedRestriction (μ i) (A i)) := by
  classical
  letI (i : ι) : IsProbabilityMeasure (normalizedRestriction (μ i) (A i)) :=
    isProbabilityMeasure_normalizedRestriction (μ i) (A i) (hA0 i)
  apply Measure.pi_eq
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [normalizedRestriction, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (hA0 i) (measure_ne_top (μ i) (A i)), one_mul]

/-- The actual simultaneous restriction is dominated by the independent normalized law. -/
theorem pi_restrict_good_le_normalized {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA0 : ∀ i, μ i (A i) ≠ 0) (E : Set (ι → ℝ)) :
    ((Measure.pi μ).restrict (coordinateGoodSet A)) E ≤
      Measure.pi (fun i ↦ normalizedRestriction (μ i) (A i)) E := by
  have hm : (∏ i, μ i (A i)) ≤ 1 := by
    rw [← Measure.pi_pi μ A]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ : Measure.pi μ univ = 1)
  rw [coordinateGoodSet, Measure.restrict_pi_pi, pi_restriction_eq_mass_smul_normalized μ A hA0,
    Measure.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left bot_le hm

/-- Any original joint outer mass reaches the independent normalized product with the summed marginal loss. -/
theorem original_pi_mass_le_normalized_add_loss {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (hA0 : ∀ i, μ i (A i) ≠ 0)
    (E : Set (ι → ℝ)) :
    Measure.pi μ E ≤ Measure.pi (fun i ↦ normalizedRestriction (μ i) (A i)) E + ∑ i, μ i (A i)ᶜ := by
  have hbase : Measure.pi μ E ≤ ((Measure.pi μ).restrict (coordinateGoodSet A)) E +
      Measure.pi μ (coordinateGoodSet A)ᶜ := by
    calc
      _ ≤ Measure.pi μ ((E ∩ coordinateGoodSet A) ∪ (coordinateGoodSet A)ᶜ) :=
        measure_mono (by intro x hx; by_cases h : x ∈ coordinateGoodSet A; exact Or.inl ⟨hx,h⟩; exact Or.inr h)
      _ ≤ Measure.pi μ (E ∩ coordinateGoodSet A) + Measure.pi μ (coordinateGoodSet A)ᶜ := measure_union_le _ _
      _ = _ := by rw [Measure.restrict_apply' (measurableSet_coordinateGoodSet A hA)]
  exact hbase.trans (add_le_add (pi_restrict_good_le_normalized μ A hA0 E) (coordinateGoodSet_compl_mass μ A hA))

end Kakeya4.Hard.MultiplicativeConvolution
