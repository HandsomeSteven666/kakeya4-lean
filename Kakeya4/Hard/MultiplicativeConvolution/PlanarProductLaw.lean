import Kakeya4.Hard.MultiplicativeConvolution.ExactFrostmanExtraction
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual planar product laws in the Euclidean metric

Coordinate projections are dominated by the Euclidean norm. No identification
of the product sup metric with the Euclidean metric is used.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual Euclidean two-dimensional realization of a real pair. -/
def pairToPlane (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![p.1,p.2]

/-- The fixed coordinate realization is continuous and thus Borel measurable. -/
theorem continuous_pairToPlane : Continuous pairToPlane := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp (by fun_prop)

/-- The independent pair law mapped into actual Euclidean coordinates. -/
def planarProductLaw (μ ν : Measure ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  (μ.prod ν).map pairToPlane

/-- Probability of the actual Euclidean pair law. -/
instance planarProductLaw_isProbabilityMeasure (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (planarProductLaw μ ν) := by
  unfold planarProductLaw
  infer_instance

/-- Every Euclidean ball pulls back inside the two coordinate balls. -/
theorem pairToPlane_preimage_closedBall_subset (z : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
    pairToPlane ⁻¹' closedBall z R ⊆ closedBall (z 0) R ×ˢ closedBall (z 1) R := by
  intro p hp
  have hn : ‖pairToPlane p-z‖ ≤ R := by simpa only [mem_preimage, mem_closedBall, dist_eq_norm] using hp
  have h0 := (PiLp.norm_apply_le (pairToPlane p-z) 0).trans hn
  have h1 := (PiLp.norm_apply_le (pairToPlane p-z) 1).trans hn
  constructor
  · simpa [mem_closedBall, Real.dist_eq, pairToPlane, Real.norm_eq_abs] using h0
  · simpa [mem_closedBall, Real.dist_eq, pairToPlane, Real.norm_eq_abs] using h1

/-- All-radius one-dimensional bounds multiply to the Euclidean (s+t)-bound. -/
theorem planarProductLaw_ball_le (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    {A B s t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : ∀ z R : ℝ, 0 < R → μ (closedBall z R) ≤ ENNReal.ofReal (A*R^s))
    (hν : ∀ z R : ℝ, 0 < R → ν (closedBall z R) ≤ ENNReal.ofReal (B*R^t))
    (z : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hR : 0 < R) :
    planarProductLaw μ ν (closedBall z R) ≤ ENNReal.ofReal (A*B*R^(s+t)) := by
  rw [planarProductLaw, Measure.map_apply continuous_pairToPlane.measurable measurableSet_closedBall]
  calc
    _ ≤ μ.prod ν (closedBall (z 0) R ×ˢ closedBall (z 1) R) :=
      measure_mono (pairToPlane_preimage_closedBall_subset z R)
    _ = μ (closedBall (z 0) R) * ν (closedBall (z 1) R) :=
      Measure.prod_prod _ _
    _ ≤ ENNReal.ofReal (A*R^s) * ENNReal.ofReal (B*R^t) := mul_le_mul' (hμ _ _ hR) (hν _ _ hR)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.rpow_nonneg hR.le _)), Real.rpow_add hR]
      congr 1
      ring

/-- Unit-supported real inputs give the actual closed unit cube in Euclidean coordinates. -/
theorem planarProductLaw_unitCube (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (hμ : UnitSupported μ) (hν : UnitSupported ν) :
    ∀ᵐ z ∂planarProductLaw μ ν, ∀ i : Fin 2, |z i| ≤ 1 := by
  have hcube : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | ∀ i : Fin 2, |z i| ≤ 1} := by
    have he : {z : EuclideanSpace ℝ (Fin 2) | ∀ i : Fin 2, |z i| ≤ 1} =
        {z | |z 0| ≤ 1} ∩ {z | |z 1| ≤ 1} := by ext z; simp [Fin.forall_fin_two]
    rw [he]
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  apply (ae_map_iff continuous_pairToPlane.measurable.aemeasurable hcube).2
  apply (Measure.ae_prod_iff_ae_ae (hcube.preimage continuous_pairToPlane.measurable)).2
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  intro i
  fin_cases i
  · simpa [pairToPlane] using hx
  · simpa [pairToPlane] using hy

end Kakeya4.Hard.MultiplicativeConvolution
