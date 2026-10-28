import OAI.MeasureTheory.Falconer.ConditionalCellRecombination
import OAI.MeasureTheory.Falconer.FineDyadicPruning
import OAI.MeasureTheory.Falconer.CellZoomUniformBudget

/-! The support filter needed by actual conditional cell recombination costs
zero original conditional product mass and preserves both radial cap bounds. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set MeasureTheory
open scoped ENNReal

theorem exists_radial_support_core {d N : ℕ}
    (μ ν : ProbabilityMeasure (Space d))
    (H : Set (Space d × Space d)) (hH : MeasurableSet H)
    {e p : ℝ} (hcap : RadialCapBound μ ν H N e p) :
    ∃ K : Set (Space d × Space d), MeasurableSet K ∧ K ⊆ H ∧
      K ⊆ (μ : Measure (Space d)).support ×ˢ (ν : Measure (Space d)).support ∧
      ((μ : Measure (Space d)).prod ν) (H \ K) = 0 ∧ RadialCapBound μ ν K N e p := by
  let S := (μ : Measure (Space d)).support ×ˢ (ν : Measure (Space d)).support
  have hS : MeasurableSet S :=
    Measure.isClosed_support.measurableSet.prod Measure.isClosed_support.measurableSet
  refine ⟨H ∩ S,hH.inter hS,inter_subset_left,inter_subset_right,?_,hcap.mono inter_subset_left⟩
  apply measure_mono_null (show H \ (H ∩ S) ⊆ Sᶜ from ?_)
    (product_core_compl_null (μ : Measure (Space d)) (ν : Measure (Space d))
      (μ : Measure (Space d)).support (ν : Measure (Space d)).support
      (μ : Measure (Space d)).measure_compl_support (ν : Measure (Space d)).measure_compl_support)
  intro z hz hmem
  exact hz.2 ⟨hz.1,hmem⟩

#print axioms exists_radial_support_core
end OAI.Falconer
