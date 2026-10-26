






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningLayerProduct

/-! The large-image and energy-volume bounds refer to the same actual layer. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem OSS_original_energy_joint_layer_bounds (kernel : SmoothKernel) {s t η a : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t ≤ 1) (hη : 0 < η) (ha : 0 < a) :
    ∃ ε e M T P r₀ : ℝ,
    0 < ε ∧ 0 < e ∧ 0 < M ∧ 0 < T ∧ 0 < P ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ r : ℝ, 0 < r → r ≤ r₀ → ∃ L : ℕ,
      (2:ℝ)^L ≤ 2*max 1 (M/r) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ r → r ≤ δ^a →
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        UnitSupported μ → UnitSupported ν →
        smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
        smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
        ∀ k : ℕ, 2 ≤ k →
        let ρ := additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k
        ENNReal.ofReal (r^e)*densityL2 ρ (kernelProfile kernel r) ≤
          densityL2 (ρ ∗ ρ) (kernelProfile kernel r) →
        densityL2 (ρ ∗ ρ) (kernelProfile kernel r) ≤
          ENNReal.ofReal T * ((L+1:ℕ):ℝ≥0∞)^2 ∨
        ∃ j : ℕ, j < L ∧
          let V := volume (flatteningCellDyadicLevel (additiveDensity ρ (kernelProfile kernel r)) r j)
          (Nat.ceil ((5*r)^(-s-t+η)) : ℝ≥0∞)*ENNReal.ofReal r ≤ V ∧
          densityL2 (ρ ∗ ρ) (kernelProfile kernel r)*V ≤
            ENNReal.ofReal P * ((L+1:ℕ):ℝ≥0∞)^4 := by
  obtain ⟨ε,e,r₁,hε,he,hr₁,hr₁1,hlarge⟩ :=
    OSS_original_energy_intermediate_layer_volume kernel hs ht hst hη ha
  obtain ⟨M,T,Q,P,hM,hT,hQ,hP,hselect⟩ := exists_uniform_slow_layer_joint_bounds kernel
  obtain ⟨C,hC,hcomp⟩ := exists_actual_cell_layer_original_mass_bound kernel
  have hQC : 0 < Q*C^2 := by positivity
  obtain ⟨r₂,hr₂,hr₂1,hpay⟩ := exists_original_mass_threshold_payment hM hQC he (by linarith : e<2*e)
  refine ⟨ε,e,M,T,P,min r₁ r₂,hε,he,hM,hT,hP,lt_min hr₁ hr₂,
    (min_le_left _ _).trans hr₁1,?_⟩
  intro r hr hrr
  obtain ⟨L,hL,hchoose⟩ := hselect r hr
  refine ⟨L,hL,?_⟩
  intro δ hδ hδr hwindow μ ν _ _ hμU hνU hμE hνE k hk ρ hslow
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  rcases hchoose ρ (ENNReal.ofReal (r^e)) hslow with hlo | ⟨j,hj,hq,hprod⟩
  · exact Or.inl hlo
  let A := flatteningCellDyadicLevel (additiveDensity ρ (kernelProfile kernel r)) r j
  have hqmass : ENNReal.ofReal (r^e) ≤ ENNReal.ofReal (Q*C^2) *
      ((L+1:ℕ):ℝ≥0∞)^4 * (ρ (cthickening (4*r) A))^2 := by
    calc
      _ ≤ ENNReal.ofReal Q * ((L+1:ℕ):ℝ≥0∞)^4 *
          ((2:ℝ≥0∞)^j * volume A)^2 := hq
      _ ≤ ENNReal.ofReal Q * ((L+1:ℕ):ℝ≥0∞)^4 *
          (ENNReal.ofReal C * ρ (cthickening (4*r) A))^2 :=
        mul_le_mul_right (pow_le_pow_left' (hcomp ρ r hr j) 2) _
      _ = _ := by
        rw [ENNReal.ofReal_mul hQ.le,ENNReal.ofReal_pow hC.le]
        ring
  have hm := hpay r hr (hrr.trans (min_le_right _ _)) L hL _ hqmass
  exact Or.inr ⟨j,hj,hlarge δ r hδ hr hδr hwindow
    (hrr.trans (min_le_left _ _)) μ ν hμU hνU hμE hνE k hk j hm,hprod⟩

#print axioms OSS_original_energy_joint_layer_bounds
end OAI.Falconer
