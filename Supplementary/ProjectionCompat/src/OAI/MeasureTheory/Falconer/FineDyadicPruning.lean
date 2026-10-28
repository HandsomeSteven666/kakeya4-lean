import OAI.MeasureTheory.Falconer.FineDyadicSeparation

/-! Actual Borel far-cell pruning and its cost in the original product law.
Small marginal cells and neighboring pairs are paid separately, using actual
dyadic cardinalities and the original second marginal's Frostman bound. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

noncomputable def farRetainedDyadicPairs (Q : DyadicCube 2) (μ ν : Measure (Space 2))
    (J : ℕ) (L : ℝ≥0∞) : Finset (List (Fin 2 → Bool) × List (Fin 2 → Bool)) :=
  ((retainedDyadicPaths Q μ J L).product (retainedDyadicPaths Q ν J L)).filter
    fun pq => 16/(2:ℝ)^J ≤ dist (Q.descendant pq.1).center (Q.descendant pq.2).center

noncomputable def fineDyadicFarRegion (Q : DyadicCube 2) (μ ν : Measure (Space 2))
    (J : ℕ) (L : ℝ≥0∞) : Set (Space 2 × Space 2) :=
  ⋃ pq ∈ farRetainedDyadicPairs Q μ ν J L,
    (Q.descendant pq.1).carrier ×ˢ (Q.descendant pq.2).carrier

theorem fineDyadicFarRegion_measurable (Q : DyadicCube 2) (μ ν : Measure (Space 2))
    (J : ℕ) (L : ℝ≥0∞) : MeasurableSet (fineDyadicFarRegion Q μ ν J L) := by
  classical
  exact Finset.measurableSet_biUnion _ (fun pq _ =>
    (Q.descendant pq.1).measurable.prod (Q.descendant pq.2).measurable)

theorem retainedDyadicPaths_positive (Q : DyadicCube 2) (μ : Measure (Space 2))
    (J : ℕ) {L : ℝ≥0∞} (hL : 0 < L)
    {p : List (Fin 2 → Bool)} (hp : p ∈ retainedDyadicPaths Q μ J L) :
    (μ.restrict (Q.descendant p).carrier) univ ≠ 0 := by
  have hpos : 0 < μ (Q.descendant p).carrier := hL.trans_le (Finset.mem_filter.mp hp).2
  simpa only [Measure.restrict_apply_univ] using hpos.ne'

theorem fineDyadicFarRegion_complement_mass (Q : DyadicCube 2) (hQ : Q.side = 1)
    (μ ν : Measure (Space 2)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ Q.carrierᶜ = 0) (hν : ν Q.carrierᶜ = 0)
    (J : ℕ) (L : ℝ≥0∞) {α C : ℝ} (hfrost : FrostmanBallBound ν α C) :
    (μ.prod ν) (fineDyadicFarRegion Q μ ν J L)ᶜ ≤
      2*((cubePaths 2 J).card : ℝ≥0∞)*L+ENNReal.ofReal (C*(20/(2:ℝ)^J)^α) := by
  classical
  let U := ⋃ p ∈ retainedDyadicPaths Q μ J L, (Q.descendant p).carrier
  let V := ⋃ p ∈ retainedDyadicPaths Q ν J L, (Q.descendant p).carrier
  let Near := {z : Space 2 × Space 2 | dist z.1 z.2 < 20/(2:ℝ)^J}
  have hsub : (fineDyadicFarRegion Q μ ν J L)ᶜ ⊆
      ((Uᶜ ×ˢ univ) ∪ (univ ×ˢ Vᶜ)) ∪ Near := by
    intro z hz
    by_cases hU : z.1 ∈ U
    · by_cases hV : z.2 ∈ V
      · obtain ⟨p,hp,hzp⟩ := mem_iUnion₂.mp hU
        obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hV
        have hnear : dist (Q.descendant p).center (Q.descendant q).center < 16/(2:ℝ)^J := by
          by_contra hn
          apply hz
          exact mem_iUnion₂.mpr ⟨(p,q),Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hp,hq⟩,le_of_not_gt hn⟩,hzp,hzq⟩
        exact Or.inr (dyadic_near_cells_point_distance Q hQ J p q
          (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 hnear hzp hzq)
      · exact Or.inl (Or.inr ⟨mem_univ _,hV⟩)
    · exact Or.inl (Or.inl ⟨hU,mem_univ _⟩)
  have hNear : (μ.prod ν) Near ≤ ENNReal.ofReal (C*(20/(2:ℝ)^J)^α) :=
    original_two_law_close_pair_mass μ ν _ _ (fun x => hfrost x _ (by positivity))
  have hUcost := retained_dyadic_complement_mass Q μ J L hμ
  have hVcost := retained_dyadic_complement_mass Q ν J L hν
  calc
    _ ≤ (μ.prod ν) (((Uᶜ ×ˢ univ) ∪ (univ ×ˢ Vᶜ)) ∪ Near) := measure_mono hsub
    _ ≤ (μ.prod ν) ((Uᶜ ×ˢ univ) ∪ (univ ×ˢ Vᶜ))+(μ.prod ν) Near := measure_union_le _ _
    _ ≤ ((μ.prod ν) (Uᶜ ×ˢ univ)+(μ.prod ν) (univ ×ˢ Vᶜ))+(μ.prod ν) Near :=
      add_le_add (measure_union_le _ _) le_rfl
    _ = (μ Uᶜ+ν Vᶜ)+(μ.prod ν) Near := by rw [Measure.prod_prod,Measure.prod_prod]; simp
    _ ≤ (((cubePaths 2 J).card : ℝ≥0∞)*L+((cubePaths 2 J).card : ℝ≥0∞)*L)+
        ENNReal.ofReal (C*(20/(2:ℝ)^J)^α) := add_le_add (add_le_add hUcost hVcost) hNear
    _ = _ := by rw [two_mul,add_mul]

theorem exists_fine_dyadic_far_pruning (Q : DyadicCube 2) (hQ : Q.side = 1)
    (μ ν : Measure (Space 2)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ Q.carrierᶜ = 0) (hν : ν Q.carrierᶜ = 0)
    (J : ℕ) (L : ℝ≥0∞) {α C : ℝ} (hfrost : FrostmanBallBound ν α C)
    (G : Set (Space 2 × Space 2)) (hG : MeasurableSet G) :
    ∃ H : Set (Space 2 × Space 2), MeasurableSet H ∧ H ⊆ G ∧
      H ⊆ fineDyadicFarRegion Q μ ν J L ∧
      (μ.prod ν) (G \ H) ≤ 2*((cubePaths 2 J).card : ℝ≥0∞)*L+
        ENNReal.ofReal (C*(20/(2:ℝ)^J)^α) := by
  refine ⟨G ∩ fineDyadicFarRegion Q μ ν J L,
    hG.inter (fineDyadicFarRegion_measurable Q μ ν J L),inter_subset_left,inter_subset_right,?_⟩
  apply (measure_mono (show G \ (G ∩ fineDyadicFarRegion Q μ ν J L) ⊆
      (fineDyadicFarRegion Q μ ν J L)ᶜ from ?_)).trans
    (fineDyadicFarRegion_complement_mass Q hQ μ ν hμ hν J L hfrost)
  intro z hz hn
  exact hz.2 ⟨hz.1,hn⟩

#print axioms fineDyadicFarRegion_measurable
#print axioms retainedDyadicPaths_positive
#print axioms fineDyadicFarRegion_complement_mass
#print axioms exists_fine_dyadic_far_pruning
end OAI.Falconer
