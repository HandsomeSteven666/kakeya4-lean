






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.EightVariableNoise

/-! Exact actual-noise transport of measurable polynomial target supersets. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem pi_eight_unit_cube_mass (μ : Fin 8 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, UnitSupported (μ i)) : Measure.pi μ {w | ∀ i, |w i| ≤ 1} = 1 := by
  have he : {w : Fin 8 → ℝ | ∀ i, |w i| ≤ 1} = univ.pi (fun _ ↦ {x : ℝ | |x| ≤ 1}) := by
    ext w; simp
  rw [he,Measure.pi_pi]
  apply Finset.prod_eq_one
  intro i _
  exact (mem_ae_iff_prob_eq_one (measurableSet_le (by fun_prop) measurable_const)).mp (hμ i)

theorem eight_value_noise_mass_transport (κ : SmoothKernel) (μ : Fin 8 → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, UnitSupported (μ i)) (r : ℝ)
    (V U : Set ℝ) (hV : MeasurableSet V) (hU : MeasurableSet U)
    (htransfer : ∀ w u : Fin 8 → ℝ, (∀ i, |w i| ≤ 1) → (∀ i, |u i| ≤ 1) →
      eightBilinearValue w ∈ V → eightBilinearValue (fun i ↦ noisyHalf r (w i) (u i)) ∈ U) :
    (Measure.pi μ).map eightBilinearValue V ≤
      (Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i))).map eightBilinearValue U := by
  let N := Measure.pi (fun _ : Fin 8 ↦ κ.law)
  let K : Set (Fin 8 → ℝ) := {w | ∀ i, |w i| ≤ 1}
  have hK : MeasurableSet K := by
    change MeasurableSet {w : Fin 8 → ℝ | ∀ i, w i ∈ {x : ℝ | |x| ≤ 1}}
    exact MeasurableSet.univ_pi' (fun _ : Fin 8 ↦
      (show MeasurableSet {x : ℝ | |x| ≤ 1} from measurableSet_le (by fun_prop) measurable_const))
  have hfull : ∀ᵐ p ∂((Measure.pi μ).prod N), p ∈ K ×ˢ K := by
    apply (mem_ae_iff_prob_eq_one (hK.prod hK)).mpr
    rw [Measure.prod_prod,pi_eight_unit_cube_mass μ hμ,pi_kernel_unitCube_mass κ,one_mul]
  have hcoord : Measurable (coordinateNoisyHalf (ι := Fin 8) r) := by
    unfold coordinateNoisyHalf noisyHalf; fun_prop
  rw [Measure.map_apply eight_bilinear_value_measurable hV,
    Measure.map_apply eight_bilinear_value_measurable hU,pi_unitRescaledSmoothLaw_eq_map,
    Measure.map_apply hcoord (hU.preimage eight_bilinear_value_measurable)]
  calc
    _ = ((Measure.pi μ).prod N) ((eightBilinearValue ⁻¹' V) ×ˢ univ) := by
      rw [Measure.prod_prod,measure_univ,mul_one]
    _ ≤ _ := measure_mono_ae (hfull.mono (fun p hp hsource ↦ htransfer p.1 p.2 hp.1 hp.2 hsource.1))

theorem original_eight_value_mass_le_smoothed_add_loss (κ : SmoothKernel)
    (μ : Fin 8 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, UnitSupported (μ i))
    (A : Fin 8 → Set ℝ) (hA : ∀ i, MeasurableSet (A i)) (hA0 : ∀ i, μ i (A i) ≠ 0)
    (r : ℝ) (V U : Set ℝ) (hV : MeasurableSet V) (hU : MeasurableSet U)
    (htransfer : ∀ w u : Fin 8 → ℝ, (∀ i, |w i| ≤ 1) → (∀ i, |u i| ≤ 1) →
      eightBilinearValue w ∈ V → eightBilinearValue (fun i ↦ noisyHalf r (w i) (u i)) ∈ U) :
    (Measure.pi μ).map eightBilinearValue V ≤
      (Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)))).map eightBilinearValue U +
        ∑ i, μ i (A i)ᶜ := by
  let (i : Fin 8) : IsProbabilityMeasure (normalizedRestriction (μ i) (A i)) :=
    isProbabilityMeasure_normalizedRestriction (μ i) (A i) (hA0 i)
  have hbase := original_pi_mass_le_normalized_add_loss μ A hA hA0 (eightBilinearValue ⁻¹' V)
  rw [← Measure.map_apply eight_bilinear_value_measurable hV,
    ← Measure.map_apply eight_bilinear_value_measurable hV] at hbase
  exact hbase.trans (add_le_add
    (eight_value_noise_mass_transport κ (fun i ↦ normalizedRestriction (μ i) (A i))
      (fun i ↦ normalizedRestriction_unitSupported (μ i) (hμ i)) r V U hV hU htransfer) le_rfl)

#print axioms pi_eight_unit_cube_mass
#print axioms eight_value_noise_mass_transport
#print axioms original_eight_value_mass_le_smoothed_add_loss
end OAI.Falconer
