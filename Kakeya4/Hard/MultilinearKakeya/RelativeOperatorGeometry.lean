import Kakeya4.Hard.MultilinearKakeya.JohnEllipsoid

/-! Relative neighborhoods in the finite-dimensional space of actual Euclidean
endomorphisms. All neighborhood constants are independent of the conditioning
of their invertible centers. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

abbrev Operator (n : ℕ) := E n →L[ℝ] E n

def operatorLeftEquiv {n : ℕ} (T : E n ≃L[ℝ] E n) : Operator n ≃L[ℝ] Operator n :=
  (ContinuousLinearEquiv.refl ℝ (E n)).arrowCongr T

theorem operatorLeftEquiv_apply {n : ℕ} (T : E n ≃L[ℝ] E n) (A : Operator n) :
    operatorLeftEquiv T A = T.toContinuousLinearMap.comp A := by
  ext x
  rfl

def relativeOperatorBall {n : ℕ} (T : E n ≃L[ℝ] E n) (δ : ℝ) : Set (Operator n) :=
  {A | ‖T.symm.toContinuousLinearMap.comp A - ContinuousLinearMap.id ℝ (E n)‖ < δ}

theorem isOpen_relativeOperatorBall {n : ℕ} (T : E n ≃L[ℝ] E n) (δ : ℝ) :
    IsOpen (relativeOperatorBall T δ) :=
  isOpen_lt (((continuous_const.clm_comp continuous_id).sub continuous_const).norm) continuous_const

theorem center_mem_relativeOperatorBall {n : ℕ} (T : E n ≃L[ℝ] E n) {δ : ℝ}
    (hδ : 0 < δ) : T.toContinuousLinearMap ∈ relativeOperatorBall T δ := by
  have hi : T.symm.toContinuousLinearMap.comp T.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (E n) := by ext x; simp
  change ‖_ - _‖ < δ
  rw [hi, sub_self, norm_zero]
  exact hδ

theorem normalize_relativeOperatorBall_iff {n : ℕ} (T₀ T : E n ≃L[ℝ] E n)
    (A : Operator n) (δ : ℝ) :
    T₀.symm.toContinuousLinearMap.comp A ∈ relativeOperatorBall (T.trans T₀.symm) δ ↔
      A ∈ relativeOperatorBall T δ := by
  have he : (T.trans T₀.symm).symm.toContinuousLinearMap.comp
      (T₀.symm.toContinuousLinearMap.comp A) = T.symm.toContinuousLinearMap.comp A := by
    ext x
    simp
  change ‖_ - _‖ < δ ↔ ‖_ - _‖ < δ
  rw [he]

theorem ordinary_ball_subset_relativeOperatorBall {n : ℕ} (T : E n ≃L[ℝ] E n)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hinv : ‖T.symm.toContinuousLinearMap‖ ≤ C) :
    Metric.ball T.toContinuousLinearMap (δ/C) ⊆ relativeOperatorBall T δ := by
  intro A hA
  have hnorm : ‖A-T.toContinuousLinearMap‖ < δ/C := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hA
  have he : T.symm.toContinuousLinearMap.comp A - ContinuousLinearMap.id ℝ (E n) =
      T.symm.toContinuousLinearMap.comp (A-T.toContinuousLinearMap) := by
    ext x
    simp
  change ‖_‖ < δ
  rw [he]
  calc
    _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖A-T.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * ‖A-T.toContinuousLinearMap‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ < C * (δ/C) := mul_lt_mul_of_pos_left hnorm hC
    _ = δ := by field_simp

theorem relativeOperatorBall_subset_ordinary_ball {n : ℕ} (T : E n ≃L[ℝ] E n)
    {C δ : ℝ} (hC : 0 < C) (hT : ‖T.toContinuousLinearMap‖ ≤ C) :
    relativeOperatorBall T δ ⊆ Metric.ball (0 : Operator n) (C*(1+δ)) := by
  intro A hA
  change ‖T.symm.toContinuousLinearMap.comp A - ContinuousLinearMap.id ℝ (E n)‖ < δ at hA
  have he : T.toContinuousLinearMap.comp (T.symm.toContinuousLinearMap.comp A) = A := by
    ext x
    simp
  have hb : ‖T.symm.toContinuousLinearMap.comp A‖ < 1+δ := by
    calc
      _ ≤ ‖T.symm.toContinuousLinearMap.comp A - ContinuousLinearMap.id ℝ (E n)‖ +
          ‖ContinuousLinearMap.id ℝ (E n)‖ := norm_le_norm_sub_add _ _
      _ < δ+1 := add_lt_add_of_lt_of_le hA ContinuousLinearMap.norm_id_le
      _ = _ := add_comm _ _
  rw [Metric.mem_ball, dist_zero_right]
  calc
    ‖A‖ = ‖T.toContinuousLinearMap.comp (T.symm.toContinuousLinearMap.comp A)‖ := congrArg norm he.symm
    _ ≤ ‖T.toContinuousLinearMap‖ * ‖T.symm.toContinuousLinearMap.comp A‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * ‖T.symm.toContinuousLinearMap.comp A‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ < C*(1+δ) := mul_lt_mul_of_pos_left hb hC

theorem relativeOperatorBall_intersection_norm_bound {n : ℕ} (T S : E n ≃L[ℝ] E n)
    {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hinter : (relativeOperatorBall T δ ∩ relativeOperatorBall S δ).Nonempty) :
    ‖T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap‖ ≤ (1+δ)/(1-δ) := by
  obtain ⟨A, hA, hB⟩ := hinter
  let G := T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap
  let V := T.symm.toContinuousLinearMap.comp A - ContinuousLinearMap.id ℝ (E n)
  let W := S.symm.toContinuousLinearMap.comp A - ContinuousLinearMap.id ℝ (E n)
  have hV : ‖V‖ ≤ δ := hA.le
  have hW : ‖W‖ ≤ δ := hB.le
  have he : G = ContinuousLinearMap.id ℝ (E n) + V - G.comp W := by
    ext x
    simp [G, V, W]
  have hn : ‖G‖ ≤ 1+δ+‖G‖*δ := by
    calc
      ‖G‖ = ‖ContinuousLinearMap.id ℝ (E n) + V - G.comp W‖ := congrArg norm he
      _ ≤ ‖ContinuousLinearMap.id ℝ (E n) + V‖ + ‖G.comp W‖ := norm_sub_le _ _
      _ ≤ (‖ContinuousLinearMap.id ℝ (E n)‖ + ‖V‖) + ‖G‖*‖W‖ :=
        add_le_add (norm_add_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ 1+δ+‖G‖*δ :=
        add_le_add (add_le_add ContinuousLinearMap.norm_id_le hV)
          (mul_le_mul_of_nonneg_left hW (norm_nonneg _))
  apply (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr
  change ‖G‖ * (1-δ) ≤ 1+δ
  nlinarith

theorem relativeOperatorBall_intersection_bounds {n : ℕ} (T S : E n ≃L[ℝ] E n)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hinter : (relativeOperatorBall T δ ∩ relativeOperatorBall S δ).Nonempty) :
    ‖T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap‖ ≤ (1+δ)/(1-δ) ∧
      ‖S.symm.toContinuousLinearMap.comp T.toContinuousLinearMap‖ ≤ (1+δ)/(1-δ) :=
  ⟨relativeOperatorBall_intersection_norm_bound T S hδ0 hδ1 hinter,
    relativeOperatorBall_intersection_norm_bound S T hδ0 hδ1 (by simpa only [inter_comm] using hinter)⟩

theorem relativeOperator_disjoint_refinement {n : ℕ}
    (s : Finset (E n ≃L[ℝ] E n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : Finset (E n ≃L[ℝ] E n), t ⊆ s ∧
      Set.Pairwise (t : Set (E n ≃L[ℝ] E n))
        (fun T S => Disjoint (relativeOperatorBall T δ) (relativeOperatorBall S δ)) ∧
      ∀ T ∈ s, ∃ S ∈ t, (relativeOperatorBall T δ ∩ relativeOperatorBall S δ).Nonempty := by
  classical
  obtain ⟨u, hus, hd, hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun T : E n ≃L[ℝ] E n => relativeOperatorBall T δ) (↑s) (fun _ => (1 : ℝ))
    2 (by norm_num) (by intros; norm_num) 1 (by intros; norm_num)
    (fun T _ => ⟨T.toContinuousLinearMap, center_mem_relativeOperatorBall T hδ⟩)
  have huf : u.Finite := s.finite_toSet.subset hus
  refine ⟨huf.toFinset, ?_, ?_, ?_⟩
  · intro T hT
    exact hus (huf.mem_toFinset.mp hT)
  · intro T hT S hS hTS
    exact hd (huf.mem_toFinset.mp hT) (huf.mem_toFinset.mp hS) hTS
  · intro T hT
    obtain ⟨S, hS, hi, _⟩ := hcover T hT
    exact ⟨S, huf.mem_toFinset.mpr hS, hi⟩

end Kakeya4.Hard.MultilinearKakeya
