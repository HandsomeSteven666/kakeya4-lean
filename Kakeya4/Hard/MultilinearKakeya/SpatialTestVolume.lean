import Kakeya4.Hard.MultilinearKakeya.BoundedSpatialPacking

/-! Exact dimensional comparison of actual test-cell and shape-ellipsoid
volumes, followed by the real index payment for a lower volume layer. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem spatialTestCell_shape_eq_image {n : ℕ} (T : E n ≃L[ℝ] E n) (r : ℝ) :
    spatialTestCell (chartOfShape T) 0 r = T '' spatialTestCell (spatialReferenceChart n) 0 r := by
  ext x
  constructor
  · intro hx
    refine ⟨T.symm x,?_,T.apply_symm_apply x⟩
    change ‖(spatialReferenceChart n).symm (T.symm (x-0))‖ < r at hx
    change ‖(spatialReferenceChart n).symm (T.symm x-0)‖ < r
    simpa only [sub_zero] using hx
  · rintro ⟨y,hy,rfl⟩
    change ‖(spatialReferenceChart n).symm (T.symm (T y-0))‖ < r
    simpa only [sub_zero,T.symm_apply_apply,spatialTestCell,mem_ofPred_eq] using hy

def spatialTestVolumeFactor (n : ℕ) : ℝ :=
  (volume (spatialTestCell (spatialReferenceChart n) 0 (spatialTestScale n))).toReal /
    (volume (Metric.closedBall (0 : E n) 1)).toReal

theorem volume_unitClosedBall_toReal_pos (n : ℕ) :
    0 < (volume (Metric.closedBall (0 : E n) 1)).toReal := by
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((Metric.measure_ball_pos volume (0 : E n) zero_lt_one).trans_le
      (measure_mono Metric.ball_subset_closedBall))
  · exact (isCompact_closedBall _ _).measure_ne_top

theorem spatialTestVolumeFactor_pos (n : ℕ) : 0 < spatialTestVolumeFactor n :=
  div_pos (volume_spatialTestCell_toReal_pos (spatialReferenceChart n) 0 (spatialTestScale_spec n).1)
    (volume_unitClosedBall_toReal_pos n)

theorem volume_spatialTestCell_shape_toReal {n : ℕ} (T : E n ≃L[ℝ] E n) (c : E n) :
    (volume (spatialTestCell (chartOfShape T) c (spatialTestScale n))).toReal =
      spatialTestVolumeFactor n * (volume (T '' Metric.closedBall 0 1)).toReal := by
  rw [volume_spatialTestCell_translation,spatialTestCell_shape_eq_image,
    Measure.addHaar_image_continuousLinearEquiv,Measure.addHaar_image_continuousLinearEquiv]
  simp only [ENNReal.toReal_mul]
  dsimp [spatialTestVolumeFactor]
  field_simp [(volume_unitClosedBall_toReal_pos n).ne']

theorem volume_spatialTestCell_shape_pos {n : ℕ} (T : E n ≃L[ℝ] E n) :
    0 < (volume (T '' Metric.closedBall 0 1)).toReal := by
  have h := volume_spatialTestCell_toReal_pos (chartOfShape T) 0 (spatialTestScale_spec n).1
  rw [volume_spatialTestCell_shape_toReal] at h
  exact (mul_pos_iff_of_pos_left (spatialTestVolumeFactor_pos n)).mp h

theorem spatialTest_card_le_of_ellipsoid_volume_lower {n : ℕ}
    (T : E n ≃L[ℝ] E n) (s : Finset (E n)) {ρ V : ℝ} (hρ : 0 < ρ)
    (hlower : ρ ≤ (volume (T '' Metric.closedBall 0 1)).toReal)
    (hupper : (s.card : ℝ)*(volume (spatialTestCell (chartOfShape T) 0 (spatialTestScale n))).toReal ≤ V) :
    (s.card : ℝ) ≤ V/(spatialTestVolumeFactor n*ρ) := by
  apply (le_div_iff₀ (mul_pos (spatialTestVolumeFactor_pos n) hρ)).mpr
  rw [volume_spatialTestCell_shape_toReal] at hupper
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hlower (spatialTestVolumeFactor_pos n).le) (Nat.cast_nonneg s.card)).trans hupper

theorem visibilityBody_realVolume_le_of_bodyShapeComparison {n : ℕ}
    (p : Seminorm ℝ (E n)) (T : E n ≃L[ℝ] E n) (hT : bodyShapeComparison p T) :
    (volume (visibilityBody p)).toReal ≤ (2*Real.sqrt n)^n *
      (volume (T '' Metric.closedBall 0 1)).toReal := by
  have hfin : volume (T '' Metric.closedBall 0 1) ≠ ⊤ :=
    ((isCompact_closedBall (0 : E n) 1).image T.continuous).measure_ne_top
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
    (volume_bounds_of_bodyShapeComparison p T hT).2
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (2*Real.sqrt n)^n)] using h

theorem spatialTest_card_volume_layer_payment {n : ℕ}
    (p : Seminorm ℝ (E n)) (T : E n ≃L[ℝ] E n) (hT : bodyShapeComparison p T)
    (s : Finset (E n)) {ρ V : ℝ}
    (hlower : ρ ≤ (volume (visibilityBody p)).toReal)
    (hupper : (s.card : ℝ)*(volume (spatialTestCell (chartOfShape T) 0 (spatialTestScale n))).toReal ≤ V) :
    (s.card : ℝ)*ρ ≤ V*(2*Real.sqrt n)^n/spatialTestVolumeFactor n := by
  apply (le_div_iff₀ (spatialTestVolumeFactor_pos n)).mpr
  have hK := hlower.trans (visibilityBody_realVolume_le_of_bodyShapeComparison p T hT)
  rw [volume_spatialTestCell_shape_toReal] at hupper
  have h1 := mul_le_mul_of_nonneg_left hK
    (mul_nonneg (Nat.cast_nonneg s.card) (spatialTestVolumeFactor_pos n).le)
  have h2 := mul_le_mul_of_nonneg_left hupper (by positivity : (0 : ℝ) ≤ (2*Real.sqrt n)^n)
  nlinarith

end Kakeya4.Hard.MultilinearKakeya
