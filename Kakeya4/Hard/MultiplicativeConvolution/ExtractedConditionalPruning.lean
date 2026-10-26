import Kakeya4.Hard.MultiplicativeConvolution.ConditionalNoisePruning
import Kakeya4.Hard.MultiplicativeConvolution.ExtractedGoodWitness

/-! # A common original good set with many admissible noises after actual extraction -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Actual extraction and conditional Markov pruning produce one Borel good set before all test sets. -/
theorem exists_extracted_conditional_good_set {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (hA0 : ∀ i, μ i (A i) ≠ 0)
    (r : ℝ) {Bad : Set (ι → ℝ)} (hBad : MeasurableSet Bad) {θ b : ℝ≥0∞}
    (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hbad : Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r
      (normalizedRestriction (μ i) (A i))) Bad ≤ θ*b) :
    ∃ G : Set (ι → ℝ), MeasurableSet G ∧ G ⊆ coordinateGoodSet A ∧
      Measure.pi μ Gᶜ ≤ b + ∑ i, μ i (A i)ᶜ ∧
      ∀ x ∈ G, 1-θ ≤ Measure.pi (fun _ : ι ↦ κ.law)
        {u | (∀ i, |u i| ≤ 1) ∧ coordinateNoisyHalf r (x,u) ∉ Bad} := by
  letI (i : ι) : IsProbabilityMeasure (normalizedRestriction (μ i) (A i)) :=
    isProbabilityMeasure_normalizedRestriction (μ i) (A i) (hA0 i)
  obtain ⟨G,hG,hGc,hnoise⟩ := exists_conditional_noise_good_set κ
    (fun i ↦ normalizedRestriction (μ i) (A i)) r hBad hθ0 hθtop hbad
  refine ⟨coordinateGoodSet A ∩ G,(measurableSet_coordinateGoodSet A hA).inter hG,
    inter_subset_left,?_,fun x hx ↦ hnoise x hx.2⟩
  have hsub : (coordinateGoodSet A ∩ G)ᶜ ∩ coordinateGoodSet A ⊆ Gᶜ := by
    intro x hx hxG
    exact hx.1 ⟨hx.2,hxG⟩
  exact (original_pi_mass_le_normalized_good_inter μ A hA hA0 _).trans
    (add_le_add ((measure_mono hsub).trans hGc) le_rfl)

/-- Any sufficiently large original test set meets a retained fiber with many actual good noises. -/
theorem exists_extracted_original_good_noise_fiber {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (hA0 : ∀ i, μ i (A i) ≠ 0)
    (r : ℝ) {Bad : Set (ι → ℝ)} (hBad : MeasurableSet Bad) {θ b : ℝ≥0∞}
    (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hbad : Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r
      (normalizedRestriction (μ i) (A i))) Bad ≤ θ*b)
    (E : Set (ι → ℝ)) (hE : b + (∑ i, μ i (A i)ᶜ) < Measure.pi μ E) :
    ∃ x ∈ E, (∀ i, x i ∈ A i) ∧
      1-θ ≤ Measure.pi (fun _ : ι ↦ κ.law)
        {u | (∀ i, |u i| ≤ 1) ∧ coordinateNoisyHalf r (x,u) ∉ Bad} := by
  classical
  obtain ⟨G,_,hGA,hGc,hnoise⟩ :=
    exists_extracted_conditional_good_set κ μ A hA hA0 r hBad hθ0 hθtop hbad
  have hmeet : (E ∩ G).Nonempty := by
    by_contra hn
    have hsub : E ⊆ Gᶜ := by
      intro x hx hxG
      exact hn ⟨x,hx,hxG⟩
    exact (not_lt_of_ge ((measure_mono hsub).trans hGc)) hE
  obtain ⟨x,hx,hxG⟩ := hmeet
  refine ⟨x,hx,?_,hnoise x hxG⟩
  simpa only [coordinateGoodSet, mem_univ_pi] using hGA hxG

end Kakeya4.Hard.MultiplicativeConvolution
