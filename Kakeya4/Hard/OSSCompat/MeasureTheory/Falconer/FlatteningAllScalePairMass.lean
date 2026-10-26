






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningThreeRanges

/-! All positive radii, derived from original energies and actual smoothing. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem OSS_original_energy_all_scale_pairMass (kernel : SmoothKernel) {s t β a : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t ≤ 1) (hβ : 0 < β)
    (ha : 0 < a) (ha1 : a ≤ 1) (hv1 : s+t+β ≤ 1) (hgap : a*(s+t+β) ≤ 2*β) :
    ∃ B ε δ₀ : ℝ, ∃ K : ℕ, 0 < B ∧ 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 2 ≤ K ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
      smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
      ∀ k : ℕ, K ≤ k → ∀ r : ℝ, 0 < r →
      pairMass r (smoothLaw kernel.law δ
        (additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k)) ≤
        ENNReal.ofReal (B*δ^(-2*β)*r^(s+t+β)) := by
  obtain ⟨C,hC,hpair⟩ := exists_smooth_pairMass_le_actual_L2 kernel
  obtain ⟨ε,r₀,K,hε,hr₀,hr₀1,hK,hflat⟩ :=
    OSS_original_energy_intermediate_L2_flattening kernel hs ht hst hβ ha
  let B : ℝ := max 2 (max C (4^(s+t+β)))
  let δ₀ : ℝ := min 1 (r₀^(1/a))
  have hδ₀ : 0 < δ₀ := lt_min (by norm_num) (Real.rpow_pos_of_pos hr₀ _)
  refine ⟨B,ε,δ₀,K,lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_left _ _),
    hε,hδ₀,min_le_left _ _,hK,?_⟩
  intro δ hδ hδsmall μ ν _ _ hμU hνU hμE hνE k hk r hr
  have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left _ _)
  have hwindow : δ ≤ δ^a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ha1
  have htop : δ^a ≤ r₀ := by
    calc
      _ ≤ (r₀^(1/a))^a := Real.rpow_le_rpow hδ.le (hδsmall.trans (min_le_right _ _)) ha.le
      _ = r₀ := by rw [← Real.rpow_mul hr₀.le,one_div_mul_cancel ha.ne',Real.rpow_one]
  let ρ := additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have : IsProbabilityMeasure (smoothLaw kernel.law δ ρ) := by unfold smoothLaw; infer_instance
  apply three_range_mass_power_bound (u := s+t) _ hδ hδ1 hr hβ (by positivity) hv1 hgap hC.le
  · have hd := hflat δ δ hδ hδ le_rfl hwindow (hwindow.trans htop) μ ν hμU hνU hμE hνE k hk
    exact (smooth_pairMass_fine_radius_bound kernel ρ hδ.ne' hr.le).trans
      ((mul_le_mul_right hd _).trans_eq (ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)).symm)
  · intro hδr hrr
    have hd := hflat δ (4*r) hδ (by positivity) hδr hrr (hrr.trans htop)
      μ ν hμU hνU hμE hνE k hk
    exact (hpair ρ δ r hr).trans
      ((mul_le_mul_right hd _).trans_eq (ENNReal.ofReal_mul (by positivity : 0 ≤ C*r)).symm)
  · calc
      _ ≤ ∫⁻ _ : ℝ, (1:ℝ≥0∞) ∂smoothLaw kernel.law δ ρ := lintegral_mono (fun _ ↦ prob_le_one)
      _ = 1 := by simp

#print axioms OSS_original_energy_all_scale_pairMass
end OAI.Falconer
