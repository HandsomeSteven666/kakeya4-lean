






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningCellCover
import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.OSSEnergyLargeImage

/-! Consume proved OSS Lemma 3.3 on the actual selected interval-layer neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal

theorem OSS_energy_large_image_layer_volume (kernel : SmoothKernel) {s t η : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hst : s+t ≤ 1) (hη : 0 < η) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ r : ℝ, 0 < r → r ≤ r₀ →
    ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy kernel.law s (5*r) μ ≤ ENNReal.ofReal ((5*r)^(-ε)) →
      smoothEnergy kernel.law t (5*r) ν ≤ ENNReal.ofReal ((5*r)^(-ε)) →
      ∀ k : ℕ, 2 ≤ k → ∀ j : ℕ,
      let ρ := additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k
      let A := flatteningCellDyadicLevel (additiveDensity ρ (kernelProfile kernel r)) r j
      ENNReal.ofReal ((5*r)^ε) ≤ ρ (cthickening (4*r) A) →
      (Nat.ceil ((5*r)^(-s-t+η)) : ℝ≥0∞) * ENNReal.ofReal r ≤ volume A := by
  obtain ⟨ε,R,hε,hR,hR1,hlarge⟩ := OSS_energy_large_image kernel hs hs1 ht ht1 hst hη
  refine ⟨ε,R/5,hε,by positivity,by linarith,?_⟩
  intro r hr hrr μ ν _ _ hμU hνU hμE hνE k hk j ρ A hmass
  have h5r : 0 < 5*r := by positivity
  have h5R : 5*r ≤ R := by linarith
  have hcard := hlarge (5*r) h5r h5R μ ν hμU hνU hμE hνE k hk (cthickening (4*r) A) hmass
  have hcard' : (Nat.ceil ((5*r)^(-s-t+η)) : ℝ≥0∞) ≤
      (externalCoveringNumber ⟨5*r,h5r.le⟩ (cthickening (4*r) A) : ℝ≥0∞) := by
    exact_mod_cast hcard
  exact (mul_le_mul_left hcard' (ENNReal.ofReal r)).trans
    (actual_cell_layer_neighborhood_cover_bound kernel ρ hr j)

#print axioms OSS_energy_large_image_layer_volume
end OAI.Falconer
