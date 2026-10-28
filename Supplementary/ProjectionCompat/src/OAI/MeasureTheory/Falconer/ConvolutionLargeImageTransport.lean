import OAI.MeasureTheory.Falconer.EnergyDifferenceConvolutionSquare

/-! Arbitrary-target large-image bounds survive convolution with a probability law.
Only a finite cover's Borel upper set enters Tonelli. -/
set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem exists_large_convolution_fiber (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (V : Set ℝ) (hV : MeasurableSet V) (q : ℝ≥0∞) (hm : q < (μ ∗ ν) V) :
    ∃ y : ℝ, q < μ {x | y+x ∈ V} := by
  by_contra hn
  push_neg at hn
  rw [Measure.conv_comm,Measure.conv,Measure.map_apply (by fun_prop) hV,
    Measure.prod_apply (hV.preimage (show Measurable (fun z : ℝ × ℝ ↦ z.1+z.2) by fun_prop))] at hm
  have hb : (∫⁻ y, μ {x | y+x ∈ V} ∂ν) ≤ q := by
    calc
      _ ≤ ∫⁻ _y, q ∂ν := lintegral_mono hn
      _ = q := by simp
  exact (not_le_of_gt hm) hb

theorem convolution_large_image_of_base (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (δ : ℝ≥0) (q : ℝ≥0∞) (n : ℕ∞)
    (hbase : ∀ B : Set ℝ, q < μ B → n ≤ externalCoveringNumber δ B)
    (E : Set ℝ) (hE : q < (μ ∗ ν) E) :
    n ≤ externalCoveringNumber δ E := by
  classical
  simp only [externalCoveringNumber,le_iInf_iff]
  intro C hC
  by_cases hfin : C.Finite
  · let : Fintype C := hfin.fintype
    let V : Set ℝ := ⋃ c : C, closedBall (c:ℝ) (δ:ℝ)
    have hV : MeasurableSet V := MeasurableSet.iUnion (fun _ ↦ measurableSet_closedBall)
    have hEV : E ⊆ V := by
      intro x hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp (hC.subset_iUnion_closedBall hx)
      obtain ⟨hcC,hxc⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨⟨c,hcC⟩,hxc⟩
    obtain ⟨y,hy⟩ := exists_large_convolution_fiber μ ν V hV q (hE.trans_le (measure_mono hEV))
    let B : Set ℝ := {x | y+x ∈ V}
    have hlarge := hbase B hy
    let D : Set ℝ := (fun c : ℝ ↦ c-y) '' C
    have hD : IsCover δ B D := by
      apply IsCover.of_subset_iUnion_closedBall
      intro x hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨(c:ℝ)-y,mem_iUnion.mpr ⟨?_,?_⟩⟩
      · exact mem_image_of_mem _ c.property
      · rw [mem_closedBall,Real.dist_eq] at hc ⊢
        have he : x-((c:ℝ)-y) = y+x-(c:ℝ) := by ring
        rwa [he]
    exact hlarge.trans (hD.externalCoveringNumber_le_encard.trans (encard_image_le _ C))
  · rw [Set.encard_eq_top hfin]
    exact le_top

#print axioms exists_large_convolution_fiber
#print axioms convolution_large_image_of_base
end OAI.Falconer
