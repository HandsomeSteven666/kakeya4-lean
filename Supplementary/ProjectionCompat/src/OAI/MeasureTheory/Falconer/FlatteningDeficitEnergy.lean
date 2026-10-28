import OAI.MeasureTheory.Falconer.FlatteningUniformInterior

/-! A real subcritical output for critical inputs; this does not assert finite I_1. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem OSS_energy_flattening_with_exponent_deficit_uniform_K (kernel : SmoothKernel) {α κ : ℝ}
    (hα : 0 < α) (hκ : 0 < κ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ s t η : ℝ, α ≤ s → α ≤ t → s+t ≤ 1 → 0 < η → η ≤ α →
      ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        UnitSupported μ → UnitSupported ν →
        smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
        smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
        ∀ k : ℕ, K ≤ k →
        smoothEnergy kernel.law (s+t-η) δ
          (additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k) ≤ ENNReal.ofReal (δ^(-κ)) := by
  obtain ⟨K,hK,hflat⟩ := OSS_original_energy_interior_flattening_uniform_K kernel
    (by positivity : 0 < α/2) hκ
  refine ⟨K,hK,?_⟩
  intro s t η hαs hαt hst hη hηα
  have hs : 0 < s := hα.trans_le hαs
  have ht : 0 < t := hα.trans_le hαt
  obtain ⟨ε,δ₁,hε,hδ₁,hδ₁1,henergy⟩ := hflat (s-η/2) (t-η/2)
    (by linarith) (by linarith) (by linarith)
  obtain ⟨δ₂,hδ₂,hδ₂1,hpay⟩ := exists_uniform_lower_exponent_cap kernel hε
  refine ⟨ε/2,min δ₁ δ₂,by positivity,lt_min hδ₁ hδ₂,
    (min_le_left _ _).trans hδ₁1,?_⟩
  intro δ hδ hδsmall μ ν _ _ hμU hνU hμE hνE k hk
  have hμcap := hpay δ hδ (hδsmall.trans (min_le_right _ _)) μ hμU (s-η/2) s
    (by linarith) (by linarith) (by linarith) hμE
  have hνcap := hpay δ hδ (hδsmall.trans (min_le_right _ _)) ν hνU (t-η/2) t
    (by linarith) (by linarith) (by linarith) hνE
  have hb := henergy δ hδ (hδsmall.trans (min_le_left _ _)) μ ν hμU hνU hμcap hνcap k hk
  simpa only [show (s-η/2)+(t-η/2)=s+t-η by ring] using hb

#print axioms OSS_energy_flattening_with_exponent_deficit_uniform_K
end OAI.Falconer
