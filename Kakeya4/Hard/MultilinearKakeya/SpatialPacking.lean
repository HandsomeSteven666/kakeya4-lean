import Kakeya4.Hard.MultilinearKakeya.SpatialTestGeometry

/-! Quantitative volume payments for actual disjoint translated test cells.
The enlarged cells cover a prescribed compact set, while the small cells stay
inside the prescribed spatial container. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem spatialTest_card_volume_le_of_disjoint {n : ℕ}
    (L : (Fin n → ℝ) ≃L[ℝ] E n) (r : ℝ) (s : Finset (E n))
    (hd : Set.Pairwise (s : Set (E n)) (fun c d => Disjoint (spatialTestCell L c r) (spatialTestCell L d r)))
    {Q : Set (E n)} (hsub : ∀ c ∈ s, spatialTestCell L c r ⊆ Q) :
    (s.card : ℝ≥0∞) * volume (spatialTestCell L 0 r) ≤ volume Q := by
  have hm := measure_biUnion_finset (μ := volume) hd
    (fun c _ => (isOpen_spatialTestCell L c r).measurableSet)
  have hs : (s.card : ℝ≥0∞) * volume (spatialTestCell L 0 r) =
      ∑ c ∈ s, volume (spatialTestCell L c r) := by
    simp only [volume_spatialTestCell_translation, Finset.sum_const, nsmul_eq_mul]
  rw [hs, ← hm]
  exact measure_mono (iUnion₂_subset hsub)

theorem spatialTest_card_volume_lower_of_triple_cover {n : ℕ}
    (L : (Fin n → ℝ) ≃L[ℝ] E n) (r : ℝ) (s : Finset (E n))
    {K : Set (E n)} (hcover : K ⊆ ⋃ c ∈ s, spatialTestCell L c (3*r)) :
    volume K ≤ ENNReal.ofReal ((3 : ℝ)^n) * (s.card : ℝ≥0∞) * volume (spatialTestCell L 0 r) := by
  calc
    _ ≤ volume (⋃ c ∈ s, spatialTestCell L c (3*r)) := measure_mono hcover
    _ ≤ ∑ c ∈ s, volume (spatialTestCell L c (3*r)) := measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [volume_spatialTestCell_translation,
        volume_spatialTestCell_scaled L (by norm_num : (0 : ℝ) < 3), Finset.sum_const, nsmul_eq_mul]
      ac_rfl

theorem spatialTest_card_realVolume_le_of_disjoint {n : ℕ}
    (L : (Fin n → ℝ) ≃L[ℝ] E n) (r : ℝ) (s : Finset (E n))
    (hd : Set.Pairwise (s : Set (E n)) (fun c d => Disjoint (spatialTestCell L c r) (spatialTestCell L d r)))
    {Q : Set (E n)} (hQ : volume Q ≠ ⊤) (hsub : ∀ c ∈ s, spatialTestCell L c r ⊆ Q) :
    (s.card : ℝ) * (volume (spatialTestCell L 0 r)).toReal ≤ (volume Q).toReal := by
  have h := ENNReal.toReal_mono hQ (spatialTest_card_volume_le_of_disjoint L r s hd hsub)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h

theorem spatialTest_card_realVolume_lower_of_triple_cover {n : ℕ}
    (L : (Fin n → ℝ) ≃L[ℝ] E n) (r : ℝ) (s : Finset (E n))
    {K : Set (E n)} (hcover : K ⊆ ⋃ c ∈ s, spatialTestCell L c (3*r)) :
    (volume K).toReal ≤ (3 : ℝ)^n * (s.card : ℝ) * (volume (spatialTestCell L 0 r)).toReal := by
  have hfin : ENNReal.ofReal ((3 : ℝ)^n) * (s.card : ℝ≥0∞) * volume (spatialTestCell L 0 r) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _))
      (volume_spatialTestCell_ne_top L 0 r)
  have h := ENNReal.toReal_mono hfin (spatialTest_card_volume_lower_of_triple_cover L r s hcover)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3^n)] using h

theorem exists_spatialTest_packing {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    {C : ℝ} (hC : 0 < C) (hL : ‖L.toContinuousLinearMap‖ ≤ C)
    (b : E n) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ s : Finset (E n), s.Nonempty ∧
      (∀ c ∈ s, c ∈ Metric.closedBall b R) ∧
      Set.Pairwise (s : Set (E n)) (fun c d => Disjoint (spatialTestCell L c r) (spatialTestCell L d r)) ∧
      (∀ c ∈ s, spatialTestCell L c r ⊆ Metric.closedBall b (R+C*r)) ∧
      (volume (Metric.closedBall b R)).toReal ≤
        (3 : ℝ)^n * (s.card : ℝ) * (volume (spatialTestCell L 0 r)).toReal ∧
      (s.card : ℝ) * (volume (spatialTestCell L 0 r)).toReal ≤
        (volume (Metric.closedBall b (R+C*r))).toReal := by
  classical
  obtain ⟨s,hs,hd,hcover⟩ := exists_disjoint_spatialTest_cover_triple L (isCompact_closedBall b R) hr
  have hsub (c : E n) (hc : c ∈ s) : spatialTestCell L c r ⊆ Metric.closedBall b (R+C*r) :=
    spatialTestCell_subset_closedBall L hC hL (hs c hc)
  have hne : s.Nonempty := by
    obtain ⟨c,hc⟩ := mem_iUnion.mp (hcover (by simpa using hR : b ∈ Metric.closedBall b R))
    obtain ⟨hcs,_⟩ := mem_iUnion.mp hc
    exact ⟨c,hcs⟩
  exact ⟨s,hne,hs,hd,hsub,spatialTest_card_realVolume_lower_of_triple_cover L r s hcover,
    spatialTest_card_realVolume_le_of_disjoint L r s hd (isCompact_closedBall _ _).measure_ne_top hsub⟩

end Kakeya4.Hard.MultilinearKakeya
