import Kakeya4.Hard.MultilinearKakeya.BoundedSpatialPacking

/-! Actual finite half-radius-ball covers of compact sets, with a unit-ball
overlap bound depending only on dimension. Disjoint small reference cells from
the existing Vitali construction pay the overlap by their positive volume. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators

namespace Kakeya4.Hard.MultilinearKakeya

def spatialCoverCellRadius (n : ℕ) : ℝ := 1/(10*spatialReferenceRadius n)

theorem spatialCoverCellRadius_pos (n : ℕ) : 0 < spatialCoverCellRadius n :=
  div_pos zero_lt_one (mul_pos (by norm_num) (spatialReferenceRadius_pos n))

theorem spatialCoverCellRadius_payment (n : ℕ) :
    spatialReferenceRadius n*spatialCoverCellRadius n = 1/10 := by
  unfold spatialCoverCellRadius
  field_simp [(spatialReferenceRadius_pos n).ne']

def spatialBallOverlapBound (n : ℕ) : ℕ :=
  ⌈(volume (Metric.closedBall (0 : E n) (1+spatialReferenceRadius n*spatialCoverCellRadius n))).toReal /
    (volume (spatialTestCell (spatialReferenceChart n) 0 (spatialCoverCellRadius n))).toReal⌉₊

theorem exists_finite_halfBall_cover_with_uniform_unit_overlap {n : ℕ}
    {K : Set (E n)} (hK : IsCompact K) :
    ∃ s : Finset (E n), (∀ c ∈ s, c ∈ K) ∧
      (K ⊆ ⋃ c ∈ s, Metric.closedBall c (1/2 : ℝ)) ∧
      (∀ x : E n, (s.filter (fun c => x ∈ Metric.closedBall c 1)).card ≤ spatialBallOverlapBound n) := by
  let L := spatialReferenceChart n
  let C := spatialReferenceRadius n
  let r := spatialCoverCellRadius n
  have hC : 0 < C := spatialReferenceRadius_pos n
  have hr : 0 < r := spatialCoverCellRadius_pos n
  have hL : ‖L.toContinuousLinearMap‖ ≤ C := le_max_right _ _
  obtain ⟨s,hcentres,hd,hcover⟩ := exists_disjoint_spatialTest_cover_triple L hK hr
  have htriple (c : E n) : spatialTestCell L c (3*r) ⊆ Metric.closedBall c (1/2 : ℝ) := by
    have h := spatialTestCell_subset_closedBall L hC hL (r := 3*r)
      (by simp : c ∈ Metric.closedBall c (0 : ℝ))
    apply h.trans
    apply Metric.closedBall_subset_closedBall
    have he : C*r = 1/10 := spatialCoverCellRadius_payment n
    nlinarith
  refine ⟨s,hcentres,hcover.trans (iUnion₂_mono (fun c _ => htriple c)),fun x => ?_⟩
  let t := s.filter (fun c => x ∈ Metric.closedBall c 1)
  have ht (c : E n) (hc : c ∈ t) : c ∈ s := (Finset.mem_filter.mp hc).1
  have hdt : Set.Pairwise (t : Set (E n)) (fun c d => Disjoint (spatialTestCell L c r) (spatialTestCell L d r)) :=
    fun c hc d hd' hcd => hd (ht c hc) (ht d hd') hcd
  have hsub (c : E n) (hc : c ∈ t) : spatialTestCell L c r ⊆ Metric.closedBall x (1+C*r) := by
    have hcx : c ∈ Metric.closedBall x 1 := by
      have he := (Finset.mem_filter.mp hc).2
      simpa only [Metric.mem_closedBall,dist_comm] using he
    exact spatialTestCell_subset_closedBall L hC hL hcx
  have hmass := spatialTest_card_realVolume_le_of_disjoint L r t hdt
    (isCompact_closedBall x (1+C*r)).measure_ne_top hsub
  rw [Measure.addHaar_closedBall_center volume x] at hmass
  have hpos := volume_spatialTestCell_toReal_pos L 0 hr
  have hcard := (le_div_iff₀ hpos).mpr hmass
  exact_mod_cast hcard.trans (Nat.le_ceil _)

theorem card_filter_subtype_centres_le {n : ℕ} (s : Finset (E n)) {C : ℕ}
    (hC : ∀ x : E n, (s.filter (fun c => x ∈ Metric.closedBall c 1)).card ≤ C) :
    ∀ x : E n, (Finset.univ.filter (fun c : s => x ∈ Metric.closedBall c.val 1)).card ≤ C := by
  intro x
  have he := Finset.filter_attach (fun c : E n => x ∈ Metric.closedBall c 1) s
  have hc := congrArg Finset.card he
  simp only [Finset.card_map,Finset.card_attach] at hc
  exact hc.trans_le (hC x)

end Kakeya4.Hard.MultilinearKakeya
