import Kakeya4.Hard.MultiplicativeConvolution.ProductRestriction

/-! # Exact finite-coordinate independent-noise coupling and arbitrary-set outer mass -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The literal coordinatewise noisy half map on independent vectors. -/
def coordinateNoisyHalf {ι : Type*} (r : ℝ) (p : (ι → ℝ) × (ι → ℝ)) : ι → ℝ :=
  fun i ↦ noisyHalf r (p.1 i) (p.2 i)

/-- The independent smoothed coordinate laws equal the actual two-vector coupling pushforward. -/
theorem pi_unitRescaledSmoothLaw_eq_map {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (r : ℝ) :
    Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i)) =
      ((Measure.pi μ).prod (Measure.pi (fun _ : ι ↦ κ.law))).map (coordinateNoisyHalf r) := by
  classical
  have hp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι μ (fun _ ↦ κ.law)
  have hm := Measure.pi_map_pi (μ := fun i ↦ (μ i).prod κ.law)
    (f := fun _ (p : ℝ × ℝ) ↦ noisyHalf r p.1 p.2) (by intro i; unfold noisyHalf; fun_prop)
  calc
    _ = Measure.pi (fun i ↦ ((μ i).prod κ.law).map (fun p ↦ noisyHalf r p.1 p.2)) := by
      congr 1
      funext i
      exact unitRescaledSmoothLaw_eq_pairMap κ (μ i) r
    _ = (Measure.pi (fun i ↦ (μ i).prod κ.law)).map (fun x i ↦ noisyHalf r (x i).1 (x i).2) := hm.symm
    _ = _ := by
      rw [← hp.map_eq, Measure.map_map (by unfold coordinateNoisyHalf noisyHalf; fun_prop) hp.measurable]
      rfl

/-- All admissible noise coordinates form a genuine full-mass rectangle. -/
theorem pi_kernel_unitCube_mass {ι : Type*} [Fintype ι] (κ : SmoothKernel) :
    Measure.pi (fun _ : ι ↦ κ.law) {u | ∀ i, |u i| ≤ 1} = 1 := by
  have he : {u : ι → ℝ | ∀ i, |u i| ≤ 1} = Set.univ.pi (fun _ ↦ {u : ℝ | |u| ≤ 1}) := by
    ext u
    simp
  rw [he, Measure.pi_pi]
  simp only [κ.law_unitSet_mass, Finset.prod_const_one]

/-- Original joint outer mass reaches the closed sup-metric neighborhood of its half image. -/
theorem pi_smoothed_thickening_mass {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {r : ℝ} (hr : 0 ≤ r) (E : Set (ι → ℝ)) :
    Measure.pi μ E ≤ Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i))
      (cthickening (r/2) ((fun x i ↦ x i/2) '' E)) := by
  rw [pi_unitRescaledSmoothLaw_eq_map,
    Measure.map_apply (by unfold coordinateNoisyHalf noisyHalf; fun_prop) isClosed_cthickening.measurableSet]
  calc
    _ = (Measure.pi μ).prod (Measure.pi (fun _ : ι ↦ κ.law))
        (E ×ˢ {u | ∀ i, |u i| ≤ 1}) := by rw [Measure.prod_prod, pi_kernel_unitCube_mass, mul_one]
    _ ≤ _ := by
      apply measure_mono
      intro p hp
      change coordinateNoisyHalf r p ∈ cthickening (r/2) ((fun x i ↦ x i/2) '' E)
      apply mem_cthickening_of_dist_le _ (fun i ↦ p.1 i/2) _ _
        (show (fun i ↦ p.1 i/2) ∈ (fun x i ↦ x i/2) '' E from ⟨p.1,hp.1,rfl⟩)
      apply (dist_pi_le_iff (by positivity : 0 ≤ r/2)).mpr
      intro i
      simpa only [coordinateNoisyHalf, Real.dist_eq] using noisyHalf_error (x := p.1 i) hr (hp.2 i)

end Kakeya4.Hard.MultiplicativeConvolution
