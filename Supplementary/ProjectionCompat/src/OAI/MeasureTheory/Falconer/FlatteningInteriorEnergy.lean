import OAI.MeasureTheory.Falconer.FlatteningAllScalePairMass
import OAI.MeasureTheory.Falconer.FlatteningPairEnergyBound

/-! The actual nontruncated energy conclusion in the strict interior. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem exists_absorb_energy_additive_constant {D β κ : ℝ} (hD : 0 ≤ D)
    (hβ : 0 < β) (hκ : 2*β < κ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      1+D*δ^(-2*β) ≤ δ^(-κ) := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hsmall⟩ := exists_small_scale_power_bound
    (C := 1+D) (a := κ-2*β) (τ := 0) (by positivity) (by linarith)
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro δ hδ hδsmall
  have hp : (1:ℝ) ≤ δ^(-2*β) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ
      (hδsmall.trans hδ₀1) (by linarith : -2*β ≤ 0)
  have hs : (1+D)*δ^(κ-2*β) ≤ 1 := by
    simpa only [neg_zero,Real.rpow_zero,mul_one] using hsmall δ hδ hδsmall
  calc
    _ ≤ (1+D)*δ^(-2*β) := by nlinarith
    _ = ((1+D)*δ^(κ-2*β))*δ^(-κ) := by
      rw [mul_assoc,← Real.rpow_add hδ]
      congr 2
      ring
    _ ≤ 1*δ^(-κ) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := one_mul _

theorem OSS_original_energy_interior_flattening (kernel : SmoothKernel) {s t κ : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t < 1) (hκ : 0 < κ) :
    ∃ ε δ₀ : ℝ, ∃ K : ℕ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 2 ≤ K ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
      smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
      ∀ k : ℕ, K ≤ k →
      smoothEnergy kernel.law (s+t) δ
        (additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k) ≤ ENNReal.ofReal (δ^(-κ)) := by
  let β : ℝ := min (κ/8) ((1-s-t)/2)
  have hβ : 0 < β := lt_min (by positivity) (by linarith)
  have hβκ : 2*β < κ := by have h := min_le_left (κ/8) ((1-s-t)/2); dsimp [β]; linarith
  have hv1 : s+t+β ≤ 1 := by have h := min_le_right (κ/8) ((1-s-t)/2); dsimp [β]; linarith
  have hv : 0 < s+t+β := by positivity
  let a : ℝ := min 1 (β/(s+t+β))
  have ha : 0 < a := lt_min (by norm_num) (div_pos hβ hv)
  have ha1 : a ≤ 1 := min_le_left _ _
  have hgap : a*(s+t+β) ≤ 2*β := by
    have ha' : a ≤ β/(s+t+β) := min_le_right _ _
    have h := (le_div_iff₀ hv).mp ha'
    linarith
  obtain ⟨B,ε,δ₁,K,hB,hε,hδ₁,hδ₁1,hK,hpair⟩ :=
    OSS_original_energy_all_scale_pairMass kernel hs ht hst.le hβ ha ha1 hv1 hgap
  obtain ⟨C,hC,henergy⟩ := exists_rieszEnergy_bound_of_pairMass_power
    (show 0 < s+t by positivity) (show s+t < s+t+β by linarith)
  obtain ⟨δ₂,hδ₂,hδ₂1,hpay⟩ := exists_absorb_energy_additive_constant
    (show 0 ≤ C*B by positivity) hβ hβκ
  refine ⟨ε,min δ₁ δ₂,K,hε,lt_min hδ₁ hδ₂,(min_le_left _ _).trans hδ₁1,hK,?_⟩
  intro δ hδ hδsmall μ ν _ _ hμU hνU hμE hνE k hk
  let ρ := additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have : IsProbabilityMeasure (smoothLaw kernel.law δ ρ) := by unfold smoothLaw; infer_instance
  have : NullSingletonClass (smoothLaw kernel.law δ ρ) := by
    rw [smoothLaw_eq_withDensity kernel ρ hδ.ne']
    infer_instance
  have he := henergy (smoothLaw kernel.law δ ρ) (B*δ^(-2*β)) (by positivity)
    (fun r hr ↦ by
      simpa only [mul_assoc] using hpair δ hδ (hδsmall.trans (min_le_left _ _))
        μ ν hμU hνU hμE hνE k hk r hr)
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using hpay δ hδ (hδsmall.trans (min_le_right _ _))

#print axioms exists_absorb_energy_additive_constant
#print axioms OSS_original_energy_interior_flattening
end OAI.Falconer
