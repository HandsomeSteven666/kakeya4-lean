import Kakeya4.Hard.MultiplicativeConvolution.ProjectionCoverTransport

/-! # Closed-neighborhood covering transport, including nonmeasurable original sets -/

noncomputable section
open Set Metric
open scoped NNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Closed centers cover the entire closed neighborhood after the exact radius payment. -/
theorem isCover_cthickening_of_closed {X : Type*} [MetricSpace X] [ProperSpace X]
    {A N : Set X} {δ r : ℝ≥0} (hN : IsClosed N) (hcover : IsCover δ A N) :
    IsCover (δ+r) (cthickening (r:ℝ) A) N := by
  apply IsCover.of_subset_cthickening hN
  have h := (cthickening_subset_of_subset (r:ℝ)
    (hcover.subset_cthickening hN)).trans
      (cthickening_cthickening_subset r.zero_le_coe δ.zero_le_coe N)
  simpa only [NNReal.coe_add, add_comm (r:ℝ) (δ:ℝ)] using h

/-- The external covering number pays r even for the full closed neighborhood of arbitrary A. -/
theorem externalCoveringNumber_cthickening_le {X : Type*} [MetricSpace X] [ProperSpace X]
    (A : Set X) (δ r : ℝ≥0) :
    externalCoveringNumber (δ+r) (cthickening (r:ℝ) A) ≤ externalCoveringNumber δ A := by
  change externalCoveringNumber (δ+r) (cthickening (r:ℝ) A) ≤
    ⨅ (N : Set X) (_ : IsCover δ A N), N.encard
  apply le_iInf
  intro N
  apply le_iInf
  intro hN
  by_cases hfinite : N.Finite
  · exact (isCover_cthickening_of_closed hfinite.isClosed hN).externalCoveringNumber_le_encard
  · rw [Set.Infinite.encard_eq hfinite]
    exact le_top

/-- Switching to an internal cover costs the standard further factor two in radius. -/
theorem coveringNumber_cthickening_le {X : Type*} [MetricSpace X] [ProperSpace X]
    (A : Set X) (δ r : ℝ≥0) :
    coveringNumber (2*(δ+r)) (cthickening (r:ℝ) A) ≤ externalCoveringNumber δ A := by
  exact (coveringNumber_two_mul_le_externalCoveringNumber _ _).trans
    (externalCoveringNumber_cthickening_le A δ r)

end Kakeya4.Hard.MultiplicativeConvolution
