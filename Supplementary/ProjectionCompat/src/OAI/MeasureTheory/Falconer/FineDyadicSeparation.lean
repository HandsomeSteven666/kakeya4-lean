import OAI.MeasureTheory.Falconer.SeparatedCellNormalization

/-! Concrete half-open dyadic cells for removing scale-dependent separation.
The exact tree partition/cardinality APIs are reused from the audited OpenAI
Apache-2.0 closure. These results do not yet assert global cap recombination. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem dyadic_depth_point_center_bound (Q : DyadicCube 2) (hQ : Q.side = 1)
    (J : ℕ) (p : List (Fin 2 → Bool)) (hp : p ∈ cubePaths 2 J)
    {x : Space 2} (hx : x ∈ (Q.descendant p).carrier) :
    dist x (Q.descendant p).center ≤ 2/(2:ℝ)^J := by
  have hs : 0 < (Q.descendant p).side := Q.descendant_side_pos (by rw [hQ]; norm_num) p
  have hroot : Real.sqrt (2:ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
  have hb := (Q.descendant p).dist_le hs.le hx ((Q.descendant p).center_mem hs)
  have hside : (Q.descendant p).side = 1/(2:ℝ)^J := by
    rw [Q.descendant_side,hQ,(mem_cubePaths 2 J p).mp hp]
  rw [hside] at hb
  norm_num only [Nat.cast_ofNat] at hb
  calc
    _ ≤ Real.sqrt (2:ℝ)*(1/(2:ℝ)^J) := hb
    _ ≤ 2*(1/(2:ℝ)^J) := mul_le_mul_of_nonneg_right hroot (by positivity)
    _ = _ := by ring

theorem dyadic_depth_centers_distance_bound (Q : DyadicCube 2) (hQ : Q.side = 1)
    (p q : List (Fin 2 → Bool)) :
    dist (Q.descendant p).center (Q.descendant q).center ≤ 4 := by
  have hs : 0 < Q.side := by rw [hQ]; norm_num
  have hp := Q.descendant_subset p ((Q.descendant p).center_mem (Q.descendant_side_pos hs p))
  have hq := Q.descendant_subset q ((Q.descendant q).center_mem (Q.descendant_side_pos hs q))
  have hb := Q.dist_le hs.le hp hq
  rw [hQ,mul_one] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have hroot : Real.sqrt (2:ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
  linarith

theorem dyadic_far_cells_uniform_normalization (Q : DyadicCube 2) (hQ : Q.side = 1)
    (J : ℕ) (p q : List (Fin 2 → Bool))
    (hp : p ∈ cubePaths 2 J) (hq : q ∈ cubePaths 2 J)
    (hfar : 16/(2:ℝ)^J ≤ dist (Q.descendant p).center (Q.descendant q).center) :
    ∃ (a : ℝ) (ha : 0 < a), 1/16 ≤ a ∧ ∃ center : Space 2,
      (∀ z ∈ (Q.descendant p).carrier,
        radialZoom a ha.ne' center z ∈ (centeredUnitCube 2).carrier) ∧
      (∀ x ∈ (Q.descendant q).carrier,
        radialZoom a ha.ne' center x ∈ (centeredUnitCube 2).carrier) ∧
      (∀ z ∈ (Q.descendant p).carrier, ∀ x ∈ (Q.descendant q).carrier,
        1/8 ≤ dist (radialZoom a ha.ne' center z) (radialZoom a ha.ne' center x)) := by
  have hd : 0 < dist (Q.descendant p).center (Q.descendant q).center :=
    (by positivity : (0:ℝ) < 16/(2:ℝ)^J).trans_le hfar
  obtain ⟨a,ha,haLower,c,hpRoot,hqRoot,hsep⟩ := separated_cell_pair_normalization
    (Q.descendant p).center (Q.descendant q).center hd (dyadic_depth_centers_distance_bound Q hQ p q)
  have hballp (z : Space 2) (hz : z ∈ (Q.descendant p).carrier) :
      z ∈ closedBall (Q.descendant p).center
        (dist (Q.descendant p).center (Q.descendant q).center/8) := by
    have hh := dyadic_depth_point_center_bound Q hQ J p hp hz
    change dist z (Q.descendant p).center ≤ _
    apply hh.trans
    calc
      2/(2:ℝ)^J = (16/(2:ℝ)^J)/8 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hfar (by norm_num)
  have hballq (x : Space 2) (hx : x ∈ (Q.descendant q).carrier) :
      x ∈ closedBall (Q.descendant q).center
        (dist (Q.descendant p).center (Q.descendant q).center/8) := by
    have hh := dyadic_depth_point_center_bound Q hQ J q hq hx
    change dist x (Q.descendant q).center ≤ _
    apply hh.trans
    calc
      2/(2:ℝ)^J = (16/(2:ℝ)^J)/8 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hfar (by norm_num)
  exact ⟨a,ha,haLower,c,fun z hz => hpRoot z (hballp z hz),
    fun x hx => hqRoot x (hballq x hx),fun z hz x hx => hsep z (hballp z hz) x (hballq x hx)⟩

theorem dyadic_near_cells_point_distance (Q : DyadicCube 2) (hQ : Q.side = 1)
    (J : ℕ) (p q : List (Fin 2 → Bool))
    (hp : p ∈ cubePaths 2 J) (hq : q ∈ cubePaths 2 J)
    (hnear : dist (Q.descendant p).center (Q.descendant q).center < 16/(2:ℝ)^J)
    {z x : Space 2} (hz : z ∈ (Q.descendant p).carrier) (hx : x ∈ (Q.descendant q).carrier) :
    dist z x < 20/(2:ℝ)^J := by
  have hbz := dyadic_depth_point_center_bound Q hQ J p hp hz
  have hbx := dyadic_depth_point_center_bound Q hQ J q hq hx
  have ht₁ := dist_triangle z (Q.descendant p).center x
  have ht₂ := dist_triangle (Q.descendant p).center (Q.descendant q).center x
  rw [dist_comm (Q.descendant q).center x] at ht₂
  have he : 2/(2:ℝ)^J+16/(2:ℝ)^J+2/(2:ℝ)^J = 20/(2:ℝ)^J := by ring
  linarith

noncomputable def retainedDyadicPaths (Q : DyadicCube 2) (μ : Measure (Space 2))
    (J : ℕ) (L : ℝ≥0∞) : Finset (List (Fin 2 → Bool)) :=
  (cubePaths 2 J).filter fun p => L ≤ μ (Q.descendant p).carrier

theorem retained_dyadic_complement_mass (Q : DyadicCube 2) (μ : Measure (Space 2))
    (J : ℕ) (L : ℝ≥0∞) (hroot : μ Q.carrierᶜ = 0) :
    μ (⋃ p ∈ retainedDyadicPaths Q μ J L, (Q.descendant p).carrier)ᶜ ≤
      ((cubePaths 2 J).card : ℝ≥0∞)*L := by
  classical
  let I := cubePaths 2 J
  let B := I.filter fun p => μ (Q.descendant p).carrier < L
  have hcover : (⋃ p ∈ retainedDyadicPaths Q μ J L, (Q.descendant p).carrier)ᶜ ⊆
      Q.carrierᶜ ∪ ⋃ p ∈ B, (Q.descendant p).carrier := by
    intro x hx
    by_cases hQx : x ∈ Q.carrier
    · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth J hQx
      have hsmall : μ (Q.descendant p).carrier < L := by
        by_contra hn
        exact hx (mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,le_of_not_gt hn⟩,hxp⟩)
      exact Or.inr (mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hsmall⟩,hxp⟩)
    · exact Or.inl hQx
  apply (measure_mono hcover).trans
  apply (measure_union_le _ _).trans
  rw [hroot,zero_add]
  calc
    _ ≤ ∑ p ∈ B, μ (Q.descendant p).carrier := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ B, L := Finset.sum_le_sum (fun p hp => (Finset.mem_filter.mp hp).2.le)
    _ = (B.card : ℝ≥0∞)*L := by simp
    _ ≤ (I.card : ℝ≥0∞)*L := by
      have hc : B.card ≤ I.card := Finset.card_filter_le I _
      exact mul_le_mul' (by exact_mod_cast hc) le_rfl

#print axioms dyadic_depth_point_center_bound
#print axioms dyadic_depth_centers_distance_bound
#print axioms dyadic_far_cells_uniform_normalization
#print axioms dyadic_near_cells_point_distance
#print axioms retained_dyadic_complement_mass
end OAI.Falconer
