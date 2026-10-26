import Kakeya4.Hard.MultilinearKakeya.SpatialPacking
import Kakeya4.Hard.MultilinearKakeya.SpatialTestCoordinates

/-! Actual test packings in a unit spatial ball, with a positive dimension-only
mass and scale chosen to defeat the shape-class directional energy budget. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

def spatialTestMass (n : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : E n) (1/2 : ℝ))).toReal / (3 : ℝ)^n

theorem spatialTestMass_pos (n : ℕ) : 0 < spatialTestMass n := by
  apply div_pos _ (by positivity)
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((Metric.measure_ball_pos volume (0 : E n) (by norm_num : (0 : ℝ) < 1/2)).trans_le
      (measure_mono Metric.ball_subset_closedBall))
  · exact (isCompact_closedBall _ _).measure_ne_top

theorem exists_spatialTest_scale (n : ℕ) : ∃ η : ℝ, 0 < η ∧
    spatialReferenceRadius n * η ≤ 1/2 ∧
    referencePoincareConstant n * (n : ℝ) * (2*η) < (Real.pi/10)*spatialTestMass n := by
  let A := (Real.pi/10)*spatialTestMass n
  let D := 2*referencePoincareConstant n*(n : ℝ)
  have hA : 0 < A := mul_pos (by positivity) (spatialTestMass_pos n)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (by norm_num) (referencePoincareConstant_pos n).le) (Nat.cast_nonneg n)
  have hc := spatialReferenceRadius_pos n
  have hmin : 0 < min ((1/2)/spatialReferenceRadius n) (A/(D+1)) :=
    lt_min (div_pos (by norm_num) hc) (div_pos hA (by linarith))
  obtain ⟨η,hη,hηmin⟩ := exists_between hmin
  have hηc := (lt_min_iff.mp hηmin).1
  have hηD := (lt_min_iff.mp hηmin).2
  have hc' : spatialReferenceRadius n * η < 1/2 := by
    have := (lt_div_iff₀ hc).mp hηc
    simpa only [mul_comm] using this
  have hd' := (lt_div_iff₀ (by linarith : 0 < D+1)).mp hηD
  refine ⟨η,hη,hc'.le,?_⟩
  change referencePoincareConstant n * (n : ℝ) * (2*η) < A
  nlinarith

def spatialTestScale (n : ℕ) : ℝ := Classical.choose (exists_spatialTest_scale n)

theorem spatialTestScale_spec (n : ℕ) : 0 < spatialTestScale n ∧
    spatialReferenceRadius n * spatialTestScale n ≤ 1/2 ∧
    referencePoincareConstant n * (n : ℝ) * (2*spatialTestScale n) <
      (Real.pi/10)*spatialTestMass n := Classical.choose_spec (exists_spatialTest_scale n)

theorem exists_unitBall_spatialTest_packing {n : ℕ} (T : E n ≃L[ℝ] E n)
    (hT : ‖T.toContinuousLinearMap‖ ≤ 1) (b : E n) :
    ∃ s : Finset (E n), s.Nonempty ∧
      (∀ c ∈ s, c ∈ Metric.closedBall b (1/2 : ℝ)) ∧
      Set.Pairwise (s : Set (E n)) (fun c d =>
        Disjoint (spatialTestCell (chartOfShape T) c (spatialTestScale n))
          (spatialTestCell (chartOfShape T) d (spatialTestScale n))) ∧
      (∀ c ∈ s, spatialTestCell (chartOfShape T) c (spatialTestScale n) ⊆ Metric.closedBall b 1) ∧
      spatialTestMass n ≤ (s.card : ℝ) *
        (volume (spatialTestCell (chartOfShape T) 0 (spatialTestScale n))).toReal ∧
      (s.card : ℝ) * (volume (spatialTestCell (chartOfShape T) 0 (spatialTestScale n))).toReal ≤
        (volume (Metric.closedBall (0 : E n) 1)).toReal := by
  obtain ⟨s,hne,hcentres,hd,hsub,hlower,hupper⟩ := exists_spatialTest_packing (chartOfShape T)
    (spatialReferenceRadius_pos n) (norm_chartOfShape_le T hT) b (by norm_num : (0 : ℝ) ≤ 1/2)
    (spatialTestScale_spec n).1
  have hsub' (c : E n) (hc : c ∈ s) :
      spatialTestCell (chartOfShape T) c (spatialTestScale n) ⊆ Metric.closedBall b 1 :=
    (hsub c hc).trans (Metric.closedBall_subset_closedBall (by linarith [(spatialTestScale_spec n).2.1]))
  refine ⟨s,hne,hcentres,hd,hsub',?_,?_⟩
  · dsimp [spatialTestMass]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3^n)).mpr
    rw [Measure.addHaar_closedBall_center volume b] at hlower
    nlinarith [hlower]
  · have h := spatialTest_card_realVolume_le_of_disjoint (chartOfShape T) (spatialTestScale n) s hd
      (isCompact_closedBall b 1).measure_ne_top hsub'
    simpa only [Measure.addHaar_closedBall_center volume b] using h

end Kakeya4.Hard.MultilinearKakeya
