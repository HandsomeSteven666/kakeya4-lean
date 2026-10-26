import Kakeya4.Hard.MultilinearKakeya.SpatialBisectionEnergy

/-! A genuine finite coloured test system for every bounded-degree polynomial
coefficient space: actual compact shape classes and actual spatial packings,
all fixed before the common smoothing parameter and the coefficients. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

theorem exists_coloured_spatial_visibility_tests {n k d : ℕ} (hn : 2 ≤ n)
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (hdeg : ∀ i, (B i).totalDegree ≤ d) (b : E n)
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0) :
    ∃ s : Finset (E n ≃L[ℝ] E n), ∃ colour : s → Fin (shapeColourCount n),
      ∃ tests : s → Finset (E n), ∃ ε : ℝ, 0 < ε ∧
      (∀ T ∈ s, ‖T.toContinuousLinearMap‖ ≤ 1) ∧
      (∀ T : s, IsClosed (coefficientShapeClass B ε (Metric.closedBall b 1) T.val)) ∧
      (∀ T : s, ∀ u : E k, -u ∈ coefficientShapeClass B ε (Metric.closedBall b 1) T.val ↔
        u ∈ coefficientShapeClass B ε (Metric.closedBall b 1) T.val) ∧
      (∀ T U : s, T ≠ U → colour T = colour U →
        Disjoint (coefficientShapeClass B ε (Metric.closedBall b 1) T.val)
          (coefficientShapeClass B ε (Metric.closedBall b 1) U.val)) ∧
      (⋃ T : s, coefficientShapeClass B ε (Metric.closedBall b 1) T.val) = univ ∧
      (∀ T : s, (tests T).Nonempty) ∧
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
      (∀ u ∈ S, ∀ T : s, u ∈ coefficientShapeClass B ε (Metric.closedBall b 1) T.val →
        ∃ c ∈ tests T, ¬ polynomialBisects (coefficientPolynomial B u)
          (spatialTestCell (chartOfShape T.val) c (spatialTestScale n))) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨s,colour,hbounded,hclasses⟩ := exists_uniform_closed_shape_classes hn B hdeg
    (isCompact_closedBall b 1) (Subset.refl (Metric.closedBall b 1))
  obtain ⟨tests,hne,hd,hsub,hlower,hupper,ε,hε,hobstruction⟩ :=
    exists_finite_shapeClass_test_obstruction B hB (fun T : s => T.val)
      (fun T => hbounded T.val T.property) (fun _ => b) hS hzero
  obtain ⟨hclosed,hneg,hdisjoint,hcover⟩ := hclasses ε hε.ne'
  exact ⟨s,colour,tests,ε,hε,hbounded,hclosed,hneg,hdisjoint,hcover,hne,hd,hsub,hlower,hupper,
    fun u hu T hT => hobstruction T u hu hT⟩

end Kakeya4.Hard.MultilinearKakeya
