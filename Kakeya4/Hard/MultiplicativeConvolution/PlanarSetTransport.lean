import Kakeya4.Hard.MultiplicativeConvolution.PlanarProductLaw
import Kakeya4.Hard.MultiplicativeConvolution.JointExtractedTransport

/-!
# Arbitrary planar outer mass through the actual Euclidean noisy law

The coordinate realization is a measurable equivalence, not an isometry from
the product sup metric. The Euclidean perturbation is proved separately.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The coordinate realization preserves arbitrary-set outer mass under pushforward. -/
theorem measurableEmbedding_planeVector :
    MeasurableEmbedding (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).symm.toMeasurableEquiv.measurableEmbedding

/-- The genuine planar pair law equals the vector product law in Euclidean coordinates. -/
theorem planarProductLaw_eq_piMap (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν] :
    planarProductLaw μ ν = (Measure.pi ![μ,ν]).map (WithLp.toLp 2) := by
  have hp := measurePreserving_finTwoArrow_vec μ ν
  rw [planarProductLaw, ← hp.map_eq,
    Measure.map_map continuous_pairToPlane.measurable hp.measurable]
  congr 1
  funext x
  change WithLp.toLp 2 ![x 0,x 1] = WithLp.toLp 2 x
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Unit coordinate noise has Euclidean displacement at most r after the actual half map. -/
theorem plane_noisyHalf_error {r : ℝ} (hr : 0 ≤ r) (x u : Fin 2 → ℝ)
    (hu : ∀ i, |u i| ≤ 1) :
    dist (WithLp.toLp 2 (coordinateNoisyHalf r (x,u)))
      ((1/2 : ℝ) • WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 2)) ≤ r := by
  have h0 := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ r/2 by positivity)).2
    (noisyHalf_error (x := x 0) hr (hu 0))
  have h1 := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ r/2 by positivity)).2
    (noisyHalf_error (x := x 1) hr (hu 1))
  simp only [sq_abs] at h0 h1
  rw [dist_eq_norm]
  have hs := EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 (coordinateNoisyHalf r (x,u)) - (1/2 : ℝ) • WithLp.toLp 2 x)
  simp only [Fin.sum_univ_two, PiLp.sub_apply, PiLp.smul_apply,
    coordinateNoisyHalf, smul_eq_mul] at hs
  have hn := norm_nonneg
    (WithLp.toLp 2 (coordinateNoisyHalf r (x,u)) - (1/2 : ℝ) • WithLp.toLp 2 x)
  nlinarith [sq_nonneg r]

/-- Arbitrary planar outer mass reaches the radius-r Euclidean neighborhood of the half image. -/
theorem planar_smoothed_thickening_mass (κ : SmoothKernel) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 ≤ r)
    (E : Set (EuclideanSpace ℝ (Fin 2))) :
    planarProductLaw μ ν E ≤
      planarProductLaw (unitRescaledSmoothLaw κ r μ) (unitRescaledSmoothLaw κ r ν)
        (cthickening r ((fun z ↦ (1/2 : ℝ) • z) '' E)) := by
  let m : Fin 2 → Measure ℝ := ![μ,ν]
  letI (i : Fin 2) : IsProbabilityMeasure (m i) := by
    fin_cases i <;> dsimp [m] <;> infer_instance
  have he : ![unitRescaledSmoothLaw κ r μ,unitRescaledSmoothLaw κ r ν] =
      fun i ↦ unitRescaledSmoothLaw κ r (m i) := by
    funext i
    fin_cases i <;> rfl
  rw [planarProductLaw_eq_piMap,
    measurableEmbedding_planeVector.map_apply, planarProductLaw_eq_piMap, he,
    pi_unitRescaledSmoothLaw_eq_map,
    Measure.map_map measurableEmbedding_planeVector.measurable
      (show Measurable (coordinateNoisyHalf r) by unfold coordinateNoisyHalf noisyHalf; fun_prop),
    Measure.map_apply (measurableEmbedding_planeVector.measurable.comp
      (by unfold coordinateNoisyHalf noisyHalf; fun_prop)) isClosed_cthickening.measurableSet]
  calc
    _ = (Measure.pi m).prod (Measure.pi (fun _ : Fin 2 ↦ κ.law))
        ((WithLp.toLp 2 ⁻¹' E) ×ˢ {u | ∀ i, |u i| ≤ 1}) := by
      rw [Measure.prod_prod, pi_kernel_unitCube_mass, mul_one]
    _ ≤ _ := by
      apply measure_mono
      rintro ⟨x,u⟩ hp
      apply mem_cthickening_of_dist_le _ ((1/2 : ℝ) • WithLp.toLp 2 x) _ _
        (show (1/2 : ℝ) • WithLp.toLp 2 x ∈ (fun z ↦ (1/2 : ℝ) • z) '' E from
          ⟨WithLp.toLp 2 x,hp.1,rfl⟩)
      exact plane_noisyHalf_error hr x u hp.2

/-- Actual coordinate extraction costs only the two discarded masses in Euclidean test sets. -/
theorem original_planar_mass_le_smoothed_add_loss (κ : SmoothKernel) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hA0 : μ A ≠ 0) (hB0 : ν B ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (E : Set (EuclideanSpace ℝ (Fin 2))) :
    planarProductLaw μ ν E ≤
      planarProductLaw (unitRescaledSmoothLaw κ r (normalizedRestriction μ A))
        (unitRescaledSmoothLaw κ r (normalizedRestriction ν B))
        (cthickening r ((fun z ↦ (1/2 : ℝ) • z) '' E)) + μ Aᶜ + ν Bᶜ := by
  let m : Fin 2 → Measure ℝ := ![μ,ν]
  let S : Fin 2 → Set ℝ := ![A,B]
  letI (i : Fin 2) : IsProbabilityMeasure (m i) := by
    fin_cases i <;> dsimp [m] <;> infer_instance
  have hS : ∀ i, MeasurableSet (S i) := by intro i; fin_cases i; exact hA; exact hB
  have hS0 : ∀ i, m i (S i) ≠ 0 := by intro i; fin_cases i; exact hA0; exact hB0
  letI : IsProbabilityMeasure (normalizedRestriction μ A) :=
    isProbabilityMeasure_normalizedRestriction μ A hA0
  letI : IsProbabilityMeasure (normalizedRestriction ν B) :=
    isProbabilityMeasure_normalizedRestriction ν B hB0
  have he : ![normalizedRestriction μ A,normalizedRestriction ν B] =
      fun i ↦ normalizedRestriction (m i) (S i) := by
    funext i
    fin_cases i <;> rfl
  have hmass : planarProductLaw μ ν E ≤
      planarProductLaw (normalizedRestriction μ A) (normalizedRestriction ν B) E + μ Aᶜ + ν Bᶜ := by
    rw [planarProductLaw_eq_piMap, measurableEmbedding_planeVector.map_apply,
      planarProductLaw_eq_piMap, measurableEmbedding_planeVector.map_apply, he, add_assoc]
    simpa only [Fin.sum_univ_two, m, S, Matrix.cons_val_zero, Matrix.cons_val_one] using
      original_pi_mass_le_normalized_add_loss m S hS hS0 (WithLp.toLp 2 ⁻¹' E)
  exact hmass.trans (add_le_add (add_le_add
    (planar_smoothed_thickening_mass κ _ _ hr E) le_rfl) le_rfl)

end Kakeya4.Hard.MultiplicativeConvolution
