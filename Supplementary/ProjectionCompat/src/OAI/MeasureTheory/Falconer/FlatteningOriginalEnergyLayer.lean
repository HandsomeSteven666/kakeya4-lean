import OAI.MeasureTheory.Falconer.FlatteningIntermediateEnergyCap

/-! All intermediate layer-volume consumers keep the original delta energy inputs. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal

theorem OSS_original_energy_intermediate_layer_volume (kernel : SmoothKernel) {s t η a : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t ≤ 1) (hη : 0 < η) (ha : 0 < a) :
    ∃ ε e r₀ : ℝ, 0 < ε ∧ 0 < e ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ δ r : ℝ, 0 < δ → 0 < r → δ ≤ r → r ≤ δ^a → r ≤ r₀ →
    ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
      smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
      ∀ k : ℕ, 2 ≤ k → ∀ j : ℕ,
      let ρ := additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k
      let A := flatteningCellDyadicLevel (additiveDensity ρ (kernelProfile kernel r)) r j
      ENNReal.ofReal ((5*r)^e) ≤ ρ (cthickening (4*r) A) →
      (Nat.ceil ((5*r)^(-s-t+η)) : ℝ≥0∞) * ENNReal.ofReal r ≤ volume A := by
  have hs1 : s < 1 := by linarith
  have ht1 : t < 1 := by linarith
  obtain ⟨e,r₁,he,hr₁,hr₁1,hlarge⟩ :=
    OSS_energy_large_image_layer_volume kernel hs hs1.le ht ht1.le hst hη
  obtain ⟨ε,r₂,hε,hr₂,hr₂1,hcap⟩ := exists_uniform_intermediate_energy_cap kernel ha he
  refine ⟨ε,e,min r₁ r₂,hε,he,lt_min hr₁ hr₂,(min_le_left _ _).trans hr₁1,?_⟩
  intro δ r hδ hr hδr hwindow hrr μ ν _ _ hμU hνU hμE hνE k hk j ρ A hmass
  exact hlarge r hr (hrr.trans (min_le_left _ _)) μ ν hμU hνU
    (hcap μ s δ r hs hs1 hδ hr hδr hwindow (hrr.trans (min_le_right _ _)) hμE)
    (hcap ν t δ r ht ht1 hδ hr hδr hwindow (hrr.trans (min_le_right _ _)) hνE)
    k hk j hmass

#print axioms OSS_original_energy_intermediate_layer_volume
end OAI.Falconer
