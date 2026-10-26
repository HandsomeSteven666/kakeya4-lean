






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.EnergyExtractedOSSProjection
import Kakeya4.Hard.MultiplicativeConvolution.PlanarProjectionNeighborhood

/-! Direct three-law averaging outside a fixed measurable parameter bad set. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem triple_relation_mass_le_bad_add_fiber
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (Bad : Set α) (hBad : MeasurableSet Bad) (S : Set (α × (β × γ))) (hS : MeasurableSet S)
    (q : ℝ≥0∞) (hfiber : ∀ a ∉ Bad, ∀ b, ρ {c | (a,(b,c)) ∈ S} ≤ q) :
    (μ.prod (ν.prod ρ)) S ≤ μ Bad+q := by
  have hpoint (a : α) : (ν.prod ρ) (Prod.mk a ⁻¹' S) ≤
      (Bad.indicator (fun _ ↦ (1:ℝ≥0∞)) a)+q := by
    by_cases ha : a ∈ Bad
    · calc
        _ ≤ 1 := prob_le_one
        _ ≤ _ := by rw [indicator_of_mem ha]; exact le_add_right le_rfl
    · rw [indicator_of_notMem ha,zero_add]
      have hSa : MeasurableSet (Prod.mk a ⁻¹' S) := hS.preimage (measurable_const.prodMk measurable_id)
      rw [Measure.prod_apply hSa]
      calc
        _ ≤ ∫⁻ _b, q ∂ν := lintegral_mono (fun b ↦ hfiber a ha b)
        _ = _ := by simp
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ a, Bad.indicator (fun _ ↦ (1:ℝ≥0∞)) a+q ∂μ := lintegral_mono hpoint
    _ = _ := by rw [lintegral_add_left (measurable_const.indicator hBad),lintegral_indicator_const hBad]; simp

theorem exists_good_parameter_large_fiber
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (Bad : Set α) (hBad : MeasurableSet Bad) (S : Set (α × (β × γ))) (hS : MeasurableSet S)
    (q : ℝ≥0∞) (hmass : μ Bad+q < (μ.prod (ν.prod ρ)) S) :
    ∃ a ∉ Bad, ∃ b, q < ρ {c | (a,(b,c)) ∈ S} := by
  by_contra hn
  push_neg at hn
  exact (not_le_of_gt hmass) (triple_relation_mass_le_bad_add_fiber μ ν ρ Bad hBad S hS q hn)

#print axioms triple_relation_mass_le_bad_add_fiber
#print axioms exists_good_parameter_large_fiber
end OAI.Falconer
