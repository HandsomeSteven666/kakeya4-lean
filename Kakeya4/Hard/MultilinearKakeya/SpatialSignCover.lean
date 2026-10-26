import Kakeya4.Hard.MultilinearKakeya.SpatialTestPadding
import Kakeya4.Hard.MultilinearKakeya.SpatialVisibilityTests

/-! The actual coloured sign bad sets produced by the spatial tests.
Their antipodal pairs cover the coefficient sphere, with a common finite test
index and true closure separation. The total index budget is a later step. -/

noncomputable section
open Set MeasureTheory
open scoped Topology Pointwise

namespace Kakeya4.Hard.MultilinearKakeya

def spatialSignBadSet {n m : ℕ} {ι γ : Type*}
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (ε : ℝ) (Q : Set (E n))
    (T : ι → E n ≃L[ℝ] E n) (colour : ι → γ) (tests : ι → Finset (E n))
    (j : ℕ) (θ : γ) : Set (UnitSphere m) :=
  colouredSignBadSet B ε Q T colour
    (fun i => paddedSpatialTest (chartOfShape (T i)) (tests i) (spatialTestScale n) j) θ

theorem disjoint_spatialSignBadSet_closure_neg {n m : ℕ} {ι γ : Type*} [Finite ι]
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q)
    (T : ι → E n ≃L[ℝ] E n) (colour : ι → γ) (tests : ι → Finset (E n))
    (hd : ∀ i l, i ≠ l → colour i = colour l →
      Disjoint (coefficientShapeClass B ε Q (T i)) (coefficientShapeClass B ε Q (T l)))
    (j : ℕ) (θ : γ) :
    Disjoint (spatialSignBadSet B ε Q T colour tests j θ)
      (closure (-spatialSignBadSet B ε Q T colour tests j θ)) :=
  disjoint_colouredSignBadSet_closure_neg B hB ε hQ T colour _
    (fun i => volume_paddedSpatialTest_ne_top _ _ _ _) hd θ

theorem spatialSignBadSets_cover_of_unbisected_tests {n m : ℕ} {ι γ : Type*} [Fintype ι]
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (ε : ℝ) (Q : Set (E n)) (T : ι → E n ≃L[ℝ] E n) (colour : ι → γ)
    (tests : ι → Finset (E n))
    (hunbisected : ∀ u : UnitSphere m, ∃ i, u ∈ sphereShapeClass B ε Q (T i) ∧
      ∃ c ∈ tests i, ¬ polynomialBisects (coefficientPolynomial B u)
        (spatialTestCell (chartOfShape (T i)) c (spatialTestScale n))) :
    ∀ u : UnitSphere m, ∃ j : Fin (spatialTestIndexBound tests), ∃ θ : γ,
      u ∈ spatialSignBadSet B ε Q T colour tests j.val θ ∨
        -u ∈ spatialSignBadSet B ε Q T colour tests j.val θ := by
  intro u
  obtain ⟨i,hi,c,hc,hnot⟩ := hunbisected u
  obtain ⟨j,he⟩ := exists_fin_paddedSpatialTest_eq (fun i => chartOfShape (T i)) tests
    (spatialTestScale n) i c hc
  refine ⟨j,colour i,?_⟩
  apply mem_colouredSignBadSet_or_neg_of_unbisected B hB ε Q T colour
    (fun i => paddedSpatialTest (chartOfShape (T i)) (tests i) (spatialTestScale n) j.val)
    i (volume_paddedSpatialTest_ne_top _ _ _ _) u hi
  rwa [he]

theorem exists_actual_coloured_spatial_sign_cover {n m d : ℕ} (hn : 2 ≤ n)
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (hdeg : ∀ i, (B i).totalDegree ≤ d) (b : E n) :
    ∃ s : Finset (E n ≃L[ℝ] E n), ∃ colour : s → Fin (shapeColourCount n),
      ∃ tests : s → Finset (E n), ∃ ε : ℝ, 0 < ε ∧
      (∀ T ∈ s, ‖T.toContinuousLinearMap‖ ≤ 1) ∧
      (∀ T U : s, T ≠ U → colour T = colour U →
        Disjoint (coefficientShapeClass B ε (Metric.closedBall b 1) T.val)
          (coefficientShapeClass B ε (Metric.closedBall b 1) U.val)) ∧
      (∀ T : s, Set.Pairwise (tests T : Set (E n)) (fun c e =>
        Disjoint (spatialTestCell (chartOfShape T.val) c (spatialTestScale n))
          (spatialTestCell (chartOfShape T.val) e (spatialTestScale n)))) ∧
      (∀ T : s, ∀ c ∈ tests T,
        spatialTestCell (chartOfShape T.val) c (spatialTestScale n) ⊆ Metric.closedBall b 1) ∧
      (∀ T : s, spatialTestMass n ≤ ((tests T).card : ℝ) *
        (volume (spatialTestCell (chartOfShape T.val) 0 (spatialTestScale n))).toReal) ∧
      (∀ T : s, ((tests T).card : ℝ) *
        (volume (spatialTestCell (chartOfShape T.val) 0 (spatialTestScale n))).toReal ≤
          (volume (Metric.closedBall (0 : E n) 1)).toReal) ∧
      (∀ j : Fin (spatialTestIndexBound tests), ∀ θ : Fin (shapeColourCount n),
        Disjoint (spatialSignBadSet B ε (Metric.closedBall b 1) (fun T : s => T.val) colour tests j.val θ)
          (closure (-spatialSignBadSet B ε (Metric.closedBall b 1) (fun T : s => T.val) colour tests j.val θ))) ∧
      (∀ u : UnitSphere m, ∃ j : Fin (spatialTestIndexBound tests), ∃ θ : Fin (shapeColourCount n),
        u ∈ spatialSignBadSet B ε (Metric.closedBall b 1) (fun T : s => T.val) colour tests j.val θ ∨
          -u ∈ spatialSignBadSet B ε (Metric.closedBall b 1) (fun T : s => T.val) colour tests j.val θ) := by
  classical
  have hz (u : E (m+1)) (hu : u ∈ Metric.sphere 0 1) : u ≠ 0 := by
    intro he
    have hn : ‖u‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hu
    rw [he,norm_zero] at hn
    norm_num at hn
  obtain ⟨s,colour,tests,ε,hε,hbounded,hclosed,hneg,hd,hcover,hne,htestdisjoint,hsub,hlower,hupper,hnot⟩ :=
    exists_coloured_spatial_visibility_tests hn B hB hdeg b (isCompact_sphere 0 1) hz
  refine ⟨s,colour,tests,ε,hε,hbounded,hd,htestdisjoint,hsub,hlower,hupper,
    (fun j θ => disjoint_spatialSignBadSet_closure_neg B hB ε (isCompact_closedBall b 1)
      (fun T : s => T.val) colour tests hd j.val θ),?_⟩
  apply spatialSignBadSets_cover_of_unbisected_tests B hB ε (Metric.closedBall b 1)
    (fun T : s => T.val) colour tests
  intro u
  have hucover : (u : E (m+1)) ∈ ⋃ T : s, coefficientShapeClass B ε (Metric.closedBall b 1) T.val := by
    rw [hcover]
    trivial
  obtain ⟨T,hT⟩ := mem_iUnion.mp hucover
  obtain ⟨c,hc,hunbisected⟩ := hnot u u.property T hT
  exact ⟨T,hT,c,hc,hunbisected⟩

end Kakeya4.Hard.MultilinearKakeya
