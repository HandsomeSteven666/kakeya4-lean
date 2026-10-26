import Kakeya4.Hard.MultiplicativeConvolution.ProjectionPerturbation
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-! # Nonmeasurable projection-value sets and actual covering-radius transport -/

noncomputable section
open Set Metric
open scoped NNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- All literal noisy projection values, with no measurability requirement on the original set. -/
def noisyProjectionValues (r : ℝ) (V : Set (Fin 6 → ℝ)) : Set ℝ :=
  {z | ∃ v ∈ V, ∃ u : Fin 6 → ℝ, (∀ i, |u i| ≤ 1) ∧
    z = projectionValue (fun i ↦ noisyHalf r (v i) (u i))}

/-- Projection values enter the actual closed 4r-neighborhood of their quarter image. -/
theorem noisyProjectionValues_subset_cthickening {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (V : Set (Fin 6 → ℝ)) (hV : ∀ v ∈ V, ∀ i, |v i| ≤ 1) :
    noisyProjectionValues r V ⊆ cthickening (4*r) ((fun v ↦ projectionValue v/4) '' V) := by
  rintro z ⟨v,hv,u,hu,rfl⟩
  apply mem_cthickening_of_dist_le _ (projectionValue v/4) _ _
    (show projectionValue v/4 ∈ (fun v ↦ projectionValue v/4) '' V from ⟨v,hv,rfl⟩)
  simpa only [Real.dist_eq] using projectionValue_noisyHalf_error v u hr hr1 (hV v hv) hu

/-- The same centers cover noisy values after exactly the 4r radius payment. -/
theorem isCover_noisyProjectionValues {r δ : ℝ≥0} (hr1 : (r:ℝ) ≤ 1)
    (V : Set (Fin 6 → ℝ)) (hV : ∀ v ∈ V, ∀ i, |v i| ≤ 1)
    {N : Set ℝ} (hN : IsCover δ ((fun v ↦ projectionValue v/4) '' V) N) :
    IsCover (δ+4*r) (noisyProjectionValues r V) N := by
  apply IsCover.of_subset_iUnion_closedBall
  rintro z ⟨v,hv,u,hu,rfl⟩
  obtain ⟨c,hc⟩ := mem_iUnion.mp (hN.subset_iUnion_closedBall
    (show projectionValue v/4 ∈ (fun v ↦ projectionValue v/4) '' V from ⟨v,hv,rfl⟩))
  obtain ⟨hcN,hcBall⟩ := mem_iUnion.mp hc
  apply mem_iUnion.mpr
  refine ⟨c,mem_iUnion.mpr ⟨hcN,?_⟩⟩
  rw [mem_closedBall, Real.dist_eq]
  have hdist : |projectionValue v/4-c| ≤ (δ:ℝ) := by
    simpa only [mem_closedBall, Real.dist_eq] using hcBall
  have he := projectionValue_noisyHalf_error v u r.zero_le_coe hr1 (hV v hv) hu
  have htri := abs_sub_le (projectionValue (fun i ↦ noisyHalf r (v i) (u i))) (projectionValue v/4) c
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
  linarith

/-- The covering witness keeps its cardinality; no measurability of V or its projection is imposed. -/
theorem externalCoveringNumber_noisyProjectionValues_le {r δ : ℝ≥0} (hr1 : (r:ℝ) ≤ 1)
    (V : Set (Fin 6 → ℝ)) (hV : ∀ v ∈ V, ∀ i, |v i| ≤ 1)
    {N : Set ℝ} (hN : IsCover δ ((fun v ↦ projectionValue v/4) '' V) N) :
    externalCoveringNumber (δ+4*r) (noisyProjectionValues r V) ≤ N.encard :=
  (isCover_noisyProjectionValues hr1 V hV hN).externalCoveringNumber_le_encard

/-- The actual external covering numbers satisfy the same uniform radius-payment inequality. -/
theorem externalCoveringNumber_noisyProjectionValues {r δ : ℝ≥0} (hr1 : (r:ℝ) ≤ 1)
    (V : Set (Fin 6 → ℝ)) (hV : ∀ v ∈ V, ∀ i, |v i| ≤ 1) :
    externalCoveringNumber (δ+4*r) (noisyProjectionValues r V) ≤
      externalCoveringNumber δ ((fun v ↦ projectionValue v/4) '' V) := by
  change externalCoveringNumber (δ+4*r) (noisyProjectionValues r V) ≤
    ⨅ (N : Set ℝ) (_ : IsCover δ ((fun v ↦ projectionValue v/4) '' V) N), N.encard
  apply le_iInf
  intro N
  apply le_iInf
  intro hN
  exact externalCoveringNumber_noisyProjectionValues_le hr1 V hV hN

end Kakeya4.Hard.MultiplicativeConvolution
