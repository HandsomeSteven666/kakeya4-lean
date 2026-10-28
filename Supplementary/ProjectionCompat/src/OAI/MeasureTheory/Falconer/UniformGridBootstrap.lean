import OAI.MeasureTheory.Falconer.FarCellBootstrapConsumer

/-! Actual finite selection of far-cell bootstrap relations and original-law
recombination. The grid depth is still free; its exact deletion cost is kept
for the subsequent law-uniform power-budget choice. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem radialCapBound_empty_relation {d N : ℕ} (μ ν : ProbabilityMeasure (Space d)) (e p : ℝ) :
    RadialCapBound μ ν ∅ N e p := by
  constructor <;> intros <;> simp

theorem retained_dyadic_carriers_pairwise (Q : DyadicCube 2) (μ : Measure (Space 2)) (J : ℕ) (L : ℝ≥0∞) :
    Pairwise fun i j : retainedDyadicPaths Q μ J L =>
      Disjoint (Q.descendant i.val).carrier (Q.descendant j.val).carrier := by
  intro i j hij
  have hi := (mem_cubePaths 2 J i.val).mp (Finset.mem_filter.mp i.property).1
  have hj := (mem_cubePaths 2 J j.val).mp (Finset.mem_filter.mp j.property).1
  exact Q.descendants_disjoint (hi.trans hj.symm) (fun h => hij (Subtype.ext h))

namespace Regularization

theorem uniform_grid_bootstrap_raw_cost
    {a b α t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbt : b < t)
    (ht : t < 1) (htα : t < α) (hα1 : α ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ ε κ c : ℝ, 0 < ε ∧ 0 < κ ∧ 0 < c ∧ ∃ N₀ : ℕ,
    ∀ p ∈ Icc a b, ∀ N ≥ N₀, ∀ (J : ℕ) (C : ℝ), 0 ≤ C → C ≤ ((2:ℝ)^N)^ε →
    ∀ μ ν : ProbabilityMeasure (Space 2),
      FrostmanBallBound (μ : Measure (Space 2)) α C →
      FrostmanBallBound (ν : Measure (Space 2)) α C →
    ∀ Q : DyadicCube 2, Q.side = 1 →
      (μ : Measure (Space 2)) Q.carrierᶜ = 0 → (ν : Measure (Space 2)) Q.carrierᶜ = 0 →
    ∀ G : Set (Space 2 × Space 2), MeasurableSet G → RadialCapBound μ ν G N ε p →
    ∃ H : Set (Space 2 × Space 2), MeasurableSet H ∧ H ⊆ G ∧
      ((μ : Measure (Space 2)).prod ν) (G \ H) ≤
        2*((cubePaths 2 J).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^N)^(-κ))+
        ENNReal.ofReal (C*(20/(2:ℝ)^J)^α)+ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
      RadialCapBound μ ν H N η b := by
  classical
  obtain ⟨ε,κ,c,hε,hκ,hc,N₀,hN₀⟩ := uniform_far_cell_bootstrap ha hab hbt ht htα hα1 η hη
  refine ⟨ε,κ,c,hε,hκ,hc,N₀,?_⟩
  intro p hp N hN J C hC hCbudget μ ν hfμ hfν Q hQ hμroot hνroot G hG hcap
  let L := ENNReal.ofReal (((2:ℝ)^N)^(-κ))
  have hL : 0 < L := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  let I := retainedDyadicPaths Q (μ : Measure (Space 2)) J L
  let T := retainedDyadicPaths Q (ν : Measure (Space 2)) J L
  let A : I → Set (Space 2) := fun i => (Q.descendant i.val).carrier
  let B : T → Set (Space 2) := fun j => (Q.descendant j.val).carrier
  have hA (i : I) : MeasurableSet (A i) := (Q.descendant i.val).measurable
  have hB (j : T) : MeasurableSet (B j) := (Q.descendant j.val).measurable
  have hμpos (i : I) : ((μ : Measure (Space 2)).restrict (A i)) univ ≠ 0 :=
    retainedDyadicPaths_positive Q (μ : Measure (Space 2)) J hL i.property
  have hνpos (j : T) : ((ν : Measure (Space 2)).restrict (B j)) univ ≠ 0 :=
    retainedDyadicPaths_positive Q (ν : Measure (Space 2)) J hL j.property
  let F : I → T → Set (Space 2 × Space 2) := fun i j =>
    if 16/(2:ℝ)^J ≤ dist (Q.descendant i.val).center (Q.descendant j.val).center then G ∩ (A i ×ˢ B j) else ∅
  have hFsub (i : I) (j : T) : F i j ⊆ A i ×ˢ B j := by
    dsimp [F]
    split_ifs
    · exact inter_subset_right
    · exact empty_subset _
  have hlocal (i : I) (j : T) : ∃ H : Set (Space 2 × Space 2), MeasurableSet H ∧ H ⊆ F i j ∧
      H ⊆ (normalizedSliceLaw ((μ : Measure (Space 2)).restrict (A i)) (hμpos i) : Measure (Space 2)).support ×ˢ
        (normalizedSliceLaw ((ν : Measure (Space 2)).restrict (B j)) (hνpos j) : Measure (Space 2)).support ∧
      ((normalizedSliceLaw ((μ : Measure (Space 2)).restrict (A i)) (hμpos i) : Measure (Space 2)).prod
        (normalizedSliceLaw ((ν : Measure (Space 2)).restrict (B j)) (hνpos j))) (F i j \ H) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
      RadialCapBound (normalizedSliceLaw ((μ : Measure (Space 2)).restrict (A i)) (hμpos i))
        (normalizedSliceLaw ((ν : Measure (Space 2)).restrict (B j)) (hνpos j)) H N η b := by
    by_cases hfar : 16/(2:ℝ)^J ≤ dist (Q.descendant i.val).center (Q.descendant j.val).center
    · have hd : 0 < dist (Q.descendant i.val).center (Q.descendant j.val).center :=
        (by positivity : (0:ℝ) < 16/(2:ℝ)^J).trans_le hfar
      have hi := (Finset.mem_filter.mp i.property).1
      have hj := (Finset.mem_filter.mp j.property).1
      have hcellA : ∀ z ∈ A i, dist z (Q.descendant i.val).center ≤
          dist (Q.descendant i.val).center (Q.descendant j.val).center/8 := by
        intro z hz
        apply (dyadic_depth_point_center_bound Q hQ J i.val hi hz).trans
        calc
          2/(2:ℝ)^J = (16/(2:ℝ)^J)/8 := by ring
          _ ≤ _ := div_le_div_of_nonneg_right hfar (by norm_num)
      have hcellB : ∀ x ∈ B j, dist x (Q.descendant j.val).center ≤
          dist (Q.descendant i.val).center (Q.descendant j.val).center/8 := by
        intro x hx
        apply (dyadic_depth_point_center_bound Q hQ J j.val hj hx).trans
        calc
          2/(2:ℝ)^J = (16/(2:ℝ)^J)/8 := by ring
          _ ≤ _ := div_le_div_of_nonneg_right hfar (by norm_num)
      obtain ⟨H,hH,hsub,hSup,hdel,hcaps⟩ := hN₀ p hp N hN C hC hCbudget μ ν hfμ hfν
        (A i) (B j) (hA i) (hB j) (hμpos i) (hνpos j)
        (Finset.mem_filter.mp i.property).2 (Finset.mem_filter.mp j.property).2
        (Q.descendant i.val).center (Q.descendant j.val).center hd
        (dyadic_depth_centers_distance_bound Q hQ i.val j.val) hcellA hcellB G hG hcap
      exact ⟨H,hH,by simpa only [F,ite_eq_left hfar] using hsub,hSup,
        by simpa only [F,ite_eq_left hfar] using hdel,hcaps⟩
    · refine ⟨∅,MeasurableSet.empty,empty_subset _,empty_subset _,?_,radialCapBound_empty_relation _ _ _ _⟩
      simp only [F,ite_eq_right hfar,empty_sdiff,measure_empty]
      exact zero_le
  choose H hHm hHsub hHsup hHdel hHcap using hlocal
  have hAdis := retained_dyadic_carriers_pairwise Q (μ : Measure (Space 2)) J L
  have hBdis := retained_dyadic_carriers_pairwise Q (ν : Measure (Space 2)) J L
  have hHcell (i : I) (j : T) : H i j ⊆ A i ×ˢ B j := (hHsub i j).trans (hFsub i j)
  obtain ⟨hUnion,hUnionCap⟩ := finite_conditional_cells_radial_bound μ ν A B hA hB hAdis hBdis
    hμpos hνpos H hHm hHcell hHsup hHcap
  have hUnionDel := finite_product_relation_weighted_deletion (μ : Measure (Space 2)) (ν : Measure (Space 2))
    A B hA hB hAdis hBdis hμpos hνpos F H hFsub (ENNReal.ofReal (((2:ℝ)^N)^(-c))) hHdel
  have hFUnion : (⋃ i, ⋃ j, F i j) = G ∩ fineDyadicFarRegion Q (μ : Measure (Space 2)) (ν : Measure (Space 2)) J L := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,j,hzij⟩ := mem_iUnion₂.mp hz
      by_cases hfar : 16/(2:ℝ)^J ≤ dist (Q.descendant i.val).center (Q.descendant j.val).center
      · have hz' : z ∈ G ∩ (A i ×ˢ B j) := by simpa only [F,ite_eq_left hfar] using hzij
        exact ⟨hz'.1,mem_iUnion₂.mpr ⟨(i.val,j.val),
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨i.property,j.property⟩,hfar⟩,hz'.2⟩⟩
      · simpa only [F,ite_eq_right hfar,notMem_empty] using hzij
    · rintro ⟨hGz,hz⟩
      obtain ⟨pq,hpq,hzp,hzq⟩ := mem_iUnion₂.mp hz
      obtain ⟨hpq,hfar⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
      let i : I := ⟨pq.1,hp⟩
      let j : T := ⟨pq.2,hq⟩
      refine mem_iUnion₂.mpr ⟨i,j,?_⟩
      dsimp only [F,i,j,A,B]
      rw [ite_eq_left hfar]
      exact ⟨hGz,hzp,hzq⟩
  have hUnionSub : (⋃ i, ⋃ j, H i j) ⊆ (⋃ i, ⋃ j, F i j) := by
    intro z hz
    obtain ⟨i,j,hzij⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨i,j,hHsub i j hzij⟩
  refine ⟨⋃ i, ⋃ j, H i j,hUnion,?_,?_,hUnionCap⟩
  · intro z hz
    have := hUnionSub hz
    rw [hFUnion] at this
    exact this.1
  · have hprune : ((μ : Measure (Space 2)).prod ν)
        (G \ (G ∩ fineDyadicFarRegion Q (μ : Measure (Space 2)) (ν : Measure (Space 2)) J L)) ≤
        2*((cubePaths 2 J).card : ℝ≥0∞)*L+ENNReal.ofReal (C*(20/(2:ℝ)^J)^α) :=
      (measure_mono (fun z hz hn => hz.2 ⟨hz.1,hn⟩)).trans
        (fineDyadicFarRegion_complement_mass Q hQ (μ : Measure (Space 2)) (ν : Measure (Space 2)) hμroot hνroot J L hfν)
    rw [hFUnion] at hUnionDel
    exact relative_pruning_cost_trans ((μ : Measure (Space 2)).prod ν) G
      (G ∩ fineDyadicFarRegion Q (μ : Measure (Space 2)) (ν : Measure (Space 2)) J L)
      (⋃ i, ⋃ j, H i j) hprune hUnionDel

#print axioms OAI.Falconer.radialCapBound_empty_relation
#print axioms OAI.Falconer.retained_dyadic_carriers_pairwise
#print axioms uniform_grid_bootstrap_raw_cost
end Regularization
end OAI.Falconer
