import Kakeya4.Hard.MultiplicativeConvolution.ProductSmoothingCoupling

/-!
# A genuine good noisy witness outside a small measurable output bad set

Bad-set neighborhoods need not have small mass. Instead use the exact coupling
and the original test set's outer mass to select an admissible noise sample.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The exact noisy coupling supplies a good witness when original mass exceeds output bad mass. -/
theorem exists_noisy_good_witness {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (r : ℝ)
    (E Bad : Set (ι → ℝ)) (hBad : MeasurableSet Bad)
    (hmass : Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i)) Bad < Measure.pi μ E) :
    ∃ x ∈ E, ∃ u : ι → ℝ, (∀ i, |u i| ≤ 1) ∧ coordinateNoisyHalf r (x,u) ∉ Bad := by
  classical
  by_contra hnone
  have hsub : E ×ˢ {u : ι → ℝ | ∀ i, |u i| ≤ 1} ⊆ coordinateNoisyHalf r ⁻¹' Bad := by
    rintro ⟨x,u⟩ hp
    change coordinateNoisyHalf r (x,u) ∈ Bad
    by_contra hb
    exact hnone ⟨x,hp.1,u,hp.2,hb⟩
  have hmass' : Measure.pi μ E ≤ Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i)) Bad := by
    rw [pi_unitRescaledSmoothLaw_eq_map,
      Measure.map_apply (by unfold coordinateNoisyHalf noisyHalf; fun_prop) hBad]
    calc
      _ = (Measure.pi μ).prod (Measure.pi (fun _ : ι ↦ κ.law))
          (E ×ˢ {u : ι → ℝ | ∀ i, |u i| ≤ 1}) := by
        rw [Measure.prod_prod, pi_kernel_unitCube_mass, mul_one]
      _ ≤ _ := measure_mono hsub
  exact (not_lt_of_ge hmass') hmass

/-- The good-witness criterion can use any certified bad-mass upper bound. -/
theorem exists_noisy_good_witness_of_bound {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (r : ℝ)
    (E Bad : Set (ι → ℝ)) (hBad : MeasurableSet Bad) {b : ℝ≥0∞}
    (hbad : Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i)) Bad ≤ b)
    (hE : b < Measure.pi μ E) :
    ∃ x ∈ E, ∃ u : ι → ℝ, (∀ i, |u i| ≤ 1) ∧ coordinateNoisyHalf r (x,u) ∉ Bad :=
  exists_noisy_good_witness κ μ r E Bad hBad (hbad.trans_lt hE)

end Kakeya4.Hard.MultiplicativeConvolution
