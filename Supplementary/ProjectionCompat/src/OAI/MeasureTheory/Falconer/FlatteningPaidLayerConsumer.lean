import OAI.MeasureTheory.Falconer.FlatteningMassThreshold

/-! Slow descent consumes Lemma 3.3 with the original input energies. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem OSS_original_energy_slow_layer_volume (kernel : SmoothKernel) {s t η a : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t ≤ 1) (hη : 0 < η) (ha : 0 < a) :
    ∃ ε e M T r₀ : ℝ, 0 < ε ∧ 0 < e ∧ 0 < M ∧ 0 < T ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
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
          let A := flatteningCellDyadicLevel (additiveDensity ρ (kernelProfile kernel r)) r j
          ENNReal.ofReal ((5*r)^e) ≤ ρ (cthickening (4*r) A) ∧
          (Nat.ceil ((5*r)^(-s-t+η)) : ℝ≥0∞) * ENNReal.ofReal r ≤ volume A := by
  obtain ⟨ε,e,r₁,hε,he,hr₁,hr₁1,hlarge⟩ :=
    OSS_original_energy_intermediate_layer_volume kernel hs ht hst hη ha
  obtain ⟨M,T,r₂,hM,hT,hr₂,hr₂1,hselect⟩ :=
    exists_uniform_paid_original_slow_mass kernel he
  refine ⟨ε,e,M,T,min r₁ r₂,hε,he,hM,hT,lt_min hr₁ hr₂,
    (min_le_left _ _).trans hr₁1,?_⟩
  intro r hr hrr
  obtain ⟨L,hL,hchoose⟩ := hselect r hr (hrr.trans (min_le_right _ _))
  refine ⟨L,hL,?_⟩
  intro δ hδ hδr hwindow μ ν _ _ hμU hνU hμE hνE k hk ρ hslow
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  rcases hchoose ρ hslow with hlo | ⟨j,hj,hmass⟩
  · exact Or.inl hlo
  · exact Or.inr ⟨j,hj,hmass,hlarge δ r hδ hr hδr hwindow
      (hrr.trans (min_le_left _ _)) μ ν hμU hνU hμE hνE k hk j hmass⟩

#print axioms OSS_original_energy_slow_layer_volume
end OAI.Falconer
