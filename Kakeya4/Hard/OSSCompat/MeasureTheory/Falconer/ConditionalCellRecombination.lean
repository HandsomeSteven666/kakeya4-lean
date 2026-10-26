






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.WeightedCellRecombination

/-! Actual conditional-law caps reassemble into original-law caps, with
support filtering at half-open cell boundaries and original mass weights. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem conditional_radial_weighted_fibers {d N : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (A B : Set (Space d))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμ : ((μ : Measure (Space d)).restrict A) univ ≠ 0)
    (hν : ((ν : Measure (Space d)).restrict B) univ ≠ 0)
    (F : Set (Space d × Space d)) (hF : F ⊆ A ×ˢ B)
    (hSup : F ⊆ (normalizedSliceLaw ((μ : Measure (Space d)).restrict A) hμ : Measure (Space d)).support ×ˢ
      (normalizedSliceLaw ((ν : Measure (Space d)).restrict B) hν : Measure (Space d)).support)
    {e p : ℝ}
    (hcap : RadialCapBound (normalizedSliceLaw ((μ : Measure (Space d)).restrict A) hμ)
      (normalizedSliceLaw ((ν : Measure (Space d)).restrict B) hν) F N e p) :
    (∀ z w : Space d, ‖w‖ = 1 → ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      (ν : Measure (Space d)) {y | (z,y) ∈ F ∧ dist (radialDirection z y) w < r} ≤
        (ν : Measure (Space d)) B*ENNReal.ofReal (((2:ℝ)^N)^e*r^p)) ∧
    (∀ x w : Space d, ‖w‖ = 1 → ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      (μ : Measure (Space d)) {z | (z,x) ∈ F ∧ dist (radialDirection x z) w < r} ≤
        (μ : Measure (Space d)) A*ENNReal.ofReal (((2:ℝ)^N)^e*r^p)) := by
  constructor
  · intro z w hw r hr hr1
    by_cases hz : z ∈ (normalizedSliceLaw ((μ : Measure (Space d)).restrict A) hμ : Measure (Space d)).support
    · rw [original_restriction_denormalize (ν : Measure (Space d)) B hB hν _
        (fun y hy => (hF hy.1).2)]
      exact mul_le_mul' le_rfl (hcap.1 z hz w hw r hr hr1)
    · have hzero : {y | (z,y) ∈ F ∧ dist (radialDirection z y) w < r} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hz (hSup hy.1).1
      rw [hzero,measure_empty]
      exact zero_le
  · intro x w hw r hr hr1
    by_cases hx : x ∈ (normalizedSliceLaw ((ν : Measure (Space d)).restrict B) hν : Measure (Space d)).support
    · rw [original_restriction_denormalize (μ : Measure (Space d)) A hA hμ _
        (fun z hz => (hF hz.1).1)]
      exact mul_le_mul' le_rfl (hcap.2 x hx w hw r hr hr1)
    · have hzero : {z | (z,x) ∈ F ∧ dist (radialDirection x z) w < r} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hx (hSup hz.1).2
      rw [hzero,measure_empty]
      exact zero_le

theorem finite_conditional_cells_radial_bound {d N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ ν : ProbabilityMeasure (Space d)) (A : ι → Set (Space d)) (B : κ → Set (Space d))
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ j, MeasurableSet (B j))
    (hAdis : Pairwise fun i k => Disjoint (A i) (A k))
    (hBdis : Pairwise fun j k => Disjoint (B j) (B k))
    (hμ : ∀ i, ((μ : Measure (Space d)).restrict (A i)) univ ≠ 0)
    (hν : ∀ j, ((ν : Measure (Space d)).restrict (B j)) univ ≠ 0)
    (F : ι → κ → Set (Space d × Space d)) (hFm : ∀ i j, MeasurableSet (F i j))
    (hF : ∀ i j, F i j ⊆ A i ×ˢ B j)
    (hSup : ∀ i j, F i j ⊆
      (normalizedSliceLaw ((μ : Measure (Space d)).restrict (A i)) (hμ i) : Measure (Space d)).support ×ˢ
      (normalizedSliceLaw ((ν : Measure (Space d)).restrict (B j)) (hν j) : Measure (Space d)).support)
    {e p : ℝ}
    (hcap : ∀ i j, RadialCapBound
      (normalizedSliceLaw ((μ : Measure (Space d)).restrict (A i)) (hμ i))
      (normalizedSliceLaw ((ν : Measure (Space d)).restrict (B j)) (hν j)) (F i j) N e p) :
    MeasurableSet (⋃ i, ⋃ j, F i j) ∧ RadialCapBound μ ν (⋃ i, ⋃ j, F i j) N e p := by
  have hweights := fun i j => conditional_radial_weighted_fibers μ ν (A i) (B j)
    (hA i) (hB j) (hμ i) (hν j) (F i j) (hF i j) (hSup i j) (hcap i j)
  refine ⟨MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (hFm i)),?_,?_⟩
  · intro z hz w hw r hr hr1
    have hswap (j : κ) (i : ι) : Prod.swap ⁻¹' F i j ⊆ B j ×ˢ A i := by
      intro y hy
      exact ⟨(hF i j hy).2,(hF i j hy).1⟩
    have hb := finite_relation_fiber_weighted_bound (ν : Measure (Space d)) B A hB hBdis hAdis
      (fun j i => Prod.swap ⁻¹' F i j) hswap (fun y x => dist (radialDirection x y) w < r)
      (ENNReal.ofReal (((2:ℝ)^N)^e*r^p))
      (fun j i x _ => (hweights i j).1 x w hw r hr hr1) z
    have he : {y | (y,z) ∈ ⋃ j, ⋃ i, Prod.swap ⁻¹' F i j ∧ dist (radialDirection z y) w < r} =
        {y | (z,y) ∈ ⋃ i, ⋃ j, F i j ∧ dist (radialDirection z y) w < r} := by
      ext y
      simp only [mem_setOf_eq,mem_iUnion,mem_preimage,Prod.swap_prod_mk]
      constructor
      · rintro ⟨⟨j,i,hij⟩,hdir⟩
        exact ⟨⟨i,j,hij⟩,hdir⟩
      · rintro ⟨⟨i,j,hij⟩,hdir⟩
        exact ⟨⟨j,i,hij⟩,hdir⟩
    rwa [he] at hb
  · intro x hx w hw r hr hr1
    exact finite_relation_fiber_weighted_bound (μ : Measure (Space d)) A B hA hAdis hBdis F hF
      (fun z y => dist (radialDirection y z) w < r) (ENNReal.ofReal (((2:ℝ)^N)^e*r^p))
      (fun i j y _ => (hweights i j).2 y w hw r hr hr1) x

#print axioms conditional_radial_weighted_fibers
#print axioms finite_conditional_cells_radial_bound
end OAI.Falconer
