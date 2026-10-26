import Kakeya4.Hard.MultiplicativeConvolution.NoisyGoodWitness

/-! # Joint good noisy witnesses from original mass after the actual summed restriction loss -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Original mass reaches the normalized law inside the actual good rectangle, retaining set membership. -/
theorem original_pi_mass_le_normalized_good_inter {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (hA0 : ∀ i, μ i (A i) ≠ 0)
    (E : Set (ι → ℝ)) :
    Measure.pi μ E ≤ Measure.pi (fun i ↦ normalizedRestriction (μ i) (A i))
      (E ∩ coordinateGoodSet A) + ∑ i, μ i (A i)ᶜ := by
  have hsub : Measure.pi μ (E \ coordinateGoodSet A) ≤ Measure.pi μ (coordinateGoodSet A)ᶜ :=
    measure_mono (by intro x hx; exact hx.2)
  have hret : Measure.pi μ (E ∩ coordinateGoodSet A) ≤
      Measure.pi (fun i ↦ normalizedRestriction (μ i) (A i)) (E ∩ coordinateGoodSet A) := by
    have h := pi_restrict_good_le_normalized μ A hA0 (E ∩ coordinateGoodSet A)
    rw [Measure.restrict_apply' (measurableSet_coordinateGoodSet A hA)] at h
    simpa only [inter_assoc, inter_self] using h
  exact (measure_le_inter_add_sdiff (Measure.pi μ) E (coordinateGoodSet A)).trans
    (add_le_add hret (hsub.trans (coordinateGoodSet_compl_mass μ A hA)))

/-- A genuine original point and admissible noise avoid a small measurable output bad set after all losses. -/
theorem exists_extracted_noisy_good_witness {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (hA0 : ∀ i, μ i (A i) ≠ 0)
    (r : ℝ) (E Bad : Set (ι → ℝ)) (hBad : MeasurableSet Bad)
    (hmass : Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i))) Bad +
      (∑ i, μ i (A i)ᶜ) < Measure.pi μ E) :
    ∃ x ∈ E, (∀ i, x i ∈ A i) ∧ ∃ u : ι → ℝ, (∀ i, |u i| ≤ 1) ∧ coordinateNoisyHalf r (x,u) ∉ Bad := by
  letI (i : ι) : IsProbabilityMeasure (normalizedRestriction (μ i) (A i)) :=
    isProbabilityMeasure_normalizedRestriction (μ i) (A i) (hA0 i)
  have hcomp : Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i))) Bad <
      Measure.pi (fun i ↦ normalizedRestriction (μ i) (A i)) (E ∩ coordinateGoodSet A) := by
    by_contra hn
    have hle := le_of_not_gt hn
    have hb := (original_pi_mass_le_normalized_good_inter μ A hA hA0 E).trans (add_le_add hle le_rfl)
    exact (not_lt_of_ge hb) hmass
  obtain ⟨x,hx,u,hu,hgood⟩ := exists_noisy_good_witness κ
    (fun i ↦ normalizedRestriction (μ i) (A i)) r (E ∩ coordinateGoodSet A) Bad hBad hcomp
  refine ⟨x,hx.1,?_,u,hu,hgood⟩
  simpa only [coordinateGoodSet, mem_univ_pi] using hx.2

end Kakeya4.Hard.MultiplicativeConvolution
