import Kakeya4.Hard.MultilinearKakeya.EuclideanBisectionEnergy

/-! Actual translated open parallelepipeds in Euclidean space, parameterized
by an invertible chart from the native Pi/sup reference space. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

def spatialTestCell {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n) (c : E n) (r : ℝ) : Set (E n) :=
  {x | ‖L.symm (x-c)‖ < r}

theorem isOpen_spatialTestCell {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (c : E n) (r : ℝ) : IsOpen (spatialTestCell L c r) :=
  isOpen_lt ((L.symm.continuous.comp (continuous_id.sub continuous_const)).norm) continuous_const

theorem center_mem_spatialTestCell {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (c : E n) {r : ℝ} (hr : 0 < r) : c ∈ spatialTestCell L c r := by
  simpa only [spatialTestCell, mem_ofPred_eq, sub_self, map_zero, norm_zero] using hr

theorem spatialTestCell_eq_image {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (c : E n) (r : ℝ) :
    spatialTestCell L c r = (fun y => c+L y) '' Metric.ball 0 r := by
  ext x
  constructor
  · intro hx
    refine ⟨L.symm (x-c), ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, spatialTestCell, mem_ofPred_eq] using hx
    · simp
  · rintro ⟨y,hy,rfl⟩
    simpa only [spatialTestCell, mem_ofPred_eq, add_sub_cancel_left,
      L.symm_apply_apply, Metric.mem_ball, dist_zero_right] using hy

theorem spatialTestCell_subset_triple_of_inter {n : ℕ}
    (L : (Fin n → ℝ) ≃L[ℝ] E n) (c d : E n) (r : ℝ)
    (hi : (spatialTestCell L c r ∩ spatialTestCell L d r).Nonempty) :
    spatialTestCell L c r ⊆ spatialTestCell L d (3*r) := by
  obtain ⟨z,hzc,hzd⟩ := hi
  intro x hx
  change ‖L.symm (z-c)‖ < r at hzc
  change ‖L.symm (z-d)‖ < r at hzd
  change ‖L.symm (x-c)‖ < r at hx
  change ‖L.symm (x-d)‖ < 3*r
  have he : L.symm (x-d) = L.symm (x-c) - L.symm (z-c) + L.symm (z-d) := by
    rw [← map_sub, ← map_add]
    congr 1
    module
  rw [he]
  have hnorm := (norm_add_le (L.symm (x-c)-L.symm (z-c)) (L.symm (z-d))).trans
    (add_le_add (norm_sub_le (L.symm (x-c)) (L.symm (z-c))) le_rfl)
  linarith

theorem spatialTestCell_subset_closedBall {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    {C : ℝ} (hC : 0 < C) (hL : ‖L.toContinuousLinearMap‖ ≤ C)
    {c b : E n} {R r : ℝ} (hc : c ∈ Metric.closedBall b R) :
    spatialTestCell L c r ⊆ Metric.closedBall b (R+C*r) := by
  intro x hx
  change ‖L.symm (x-c)‖ < r at hx
  have hdist : dist x c < C*r := by
    calc
      dist x c = ‖L (L.symm (x-c))‖ := by simp only [L.apply_symm_apply, dist_eq_norm]
      _ ≤ ‖L.toContinuousLinearMap‖ * ‖L.symm (x-c)‖ := L.toContinuousLinearMap.le_opNorm _
      _ ≤ C * ‖L.symm (x-c)‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ < C*r := mul_lt_mul_of_pos_left hx hC
  have hcb : dist c b ≤ R := hc
  have ht := dist_triangle x c b
  change dist x b ≤ R+C*r
  linarith

theorem volume_spatialTestCell_translation {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (c : E n) (r : ℝ) : volume (spatialTestCell L c r) = volume (spatialTestCell L 0 r) := by
  have he : spatialTestCell L c r = (fun x : E n => -c+x) ⁻¹' spatialTestCell L 0 r := by
    ext x
    simp only [spatialTestCell, mem_ofPred_eq, mem_preimage, sub_zero]
    rw [add_comm (-c) x, ← sub_eq_add_neg]
  rw [he]
  exact (measurePreserving_add_left volume (-c)).measure_preimage
    (isOpen_spatialTestCell L 0 r).measurableSet.nullMeasurableSet

theorem volume_spatialTestCell_scaled {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    {a : ℝ} (ha : 0 < a) (r : ℝ) :
    volume (spatialTestCell L 0 (a*r)) = ENNReal.ofReal (a^n) * volume (spatialTestCell L 0 r) := by
  have he : spatialTestCell L 0 (a*r) = (fun x : E n => a⁻¹ • x) ⁻¹' spatialTestCell L 0 r := by
    ext x
    simp only [spatialTestCell, mem_ofPred_eq, mem_preimage, sub_zero, map_smul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr ha.le), inv_mul_eq_div]
    exact (by simpa only [mul_comm] using (div_lt_iff₀ ha).symm)
  rw [he, Measure.addHaar_preimage_smul volume (inv_ne_zero ha.ne')]
  simp only [E, finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv,
    abs_of_nonneg (pow_nonneg ha.le _)]

theorem volume_spatialTestCell_ne_top {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (c : E n) (r : ℝ) : volume (spatialTestCell L c r) ≠ ⊤ := by
  let C := max 1 ‖L.toContinuousLinearMap‖
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hs := spatialTestCell_subset_closedBall L hC (le_max_right _ _)
    (r := r) (by simp : c ∈ Metric.closedBall c (0 : ℝ))
  exact ne_of_lt ((measure_mono hs).trans_lt (isCompact_closedBall c (0+C*r)).measure_lt_top)

theorem volume_spatialTestCell_pos {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (c : E n) {r : ℝ} (hr : 0 < r) : 0 < volume (spatialTestCell L c r) :=
  (isOpen_spatialTestCell L c r).measure_pos volume ⟨c,center_mem_spatialTestCell L c hr⟩

theorem volume_spatialTestCell_toReal_pos {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (c : E n) {r : ℝ} (hr : 0 < r) : 0 < (volume (spatialTestCell L c r)).toReal :=
  ENNReal.toReal_pos (ne_of_gt (volume_spatialTestCell_pos L c hr)) (volume_spatialTestCell_ne_top L c r)

theorem exists_finite_spatialTest_cover {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    {K : Set (E n)} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset (E n), (∀ c ∈ s, c ∈ K) ∧ K ⊆ ⋃ c ∈ s, spatialTestCell L c r := by
  classical
  have hcover : K ⊆ ⋃ c : K, spatialTestCell L c.val r := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,center_mem_spatialTestCell L x hr⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : K => spatialTestCell L c.val r)
    (fun c => isOpen_spatialTestCell L c.val r) hcover
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro c hc
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hc
    exact a.property
  · intro x hx
    obtain ⟨a,ha⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hat,hcell⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨a.val,mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨a,hat,rfl⟩,hcell⟩⟩

theorem exists_disjoint_spatialTest_cover_triple {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    {K : Set (E n)} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset (E n), (∀ c ∈ s, c ∈ K) ∧
      Set.Pairwise (s : Set (E n)) (fun c d => Disjoint (spatialTestCell L c r) (spatialTestCell L d r)) ∧
      K ⊆ ⋃ c ∈ s, spatialTestCell L c (3*r) := by
  classical
  obtain ⟨t,ht,hcover⟩ := exists_finite_spatialTest_cover L hK hr
  obtain ⟨u, hut, hd, hmeet⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun c : E n => spatialTestCell L c r) (↑t) (fun _ => (1 : ℝ))
    2 (by norm_num) (by intros; norm_num) 1 (by intros; norm_num)
    (fun c _ => ⟨c,center_mem_spatialTestCell L c hr⟩)
  have huf : u.Finite := t.finite_toSet.subset hut
  refine ⟨huf.toFinset, ?_, ?_, ?_⟩
  · intro c hc
    exact ht c (hut (huf.mem_toFinset.mp hc))
  · intro c hc d hd' hcd
    exact hd (huf.mem_toFinset.mp hc) (huf.mem_toFinset.mp hd') hcd
  · intro x hx
    obtain ⟨c,hc⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨hct,hxc⟩ := mem_iUnion.mp hc
    obtain ⟨d,hdu,hi,_⟩ := hmeet c hct
    exact mem_iUnion.mpr ⟨d,mem_iUnion.mpr ⟨huf.mem_toFinset.mpr hdu,
      spatialTestCell_subset_triple_of_inter L c d r hi hxc⟩⟩

end Kakeya4.Hard.MultilinearKakeya
