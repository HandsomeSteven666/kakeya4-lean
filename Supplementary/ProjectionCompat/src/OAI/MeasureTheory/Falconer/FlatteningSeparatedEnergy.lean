import OAI.MeasureTheory.Falconer.FlatteningInteriorEnergy

/-! The integrability gap affects the scale threshold, not the L2 iteration budget. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem three_range_mass_power_bound_separated {δ r u b g a C : ℝ} (F : ℝ≥0∞)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hb : 0 < b) (hg : 0 < g)
    (hv : 0 ≤ u+g) (hv1 : u+g ≤ 1) (hgap : a*(u+g) ≤ b+g) (hC : 0 ≤ C)
    (hf : F ≤ ENNReal.ofReal (2*r*δ^(u-1-b)))
    (hi : δ ≤ 4*r → 4*r ≤ δ^a → F ≤ ENNReal.ofReal (C*r*(4*r)^(u-1-b)))
    (hp : F ≤ 1) :
    F ≤ ENNReal.ofReal (max 2 (max C (4^(u+g)))*δ^(-(b+g))*r^(u+g)) := by
  have he1 : u+(g-b)/2-1-(b+g)/2 = u-1-b := by ring
  have he2 : u+(g-b)/2+(b+g)/2 = u+g := by ring
  have he3 : -2*((b+g)/2) = -(b+g) := by ring
  have hv' : 0 ≤ u+(g-b)/2+(b+g)/2 := by linarith
  have hv1' : u+(g-b)/2+(b+g)/2 ≤ 1 := by linarith
  have hgap' : a*(u+(g-b)/2+(b+g)/2) ≤ 2*((b+g)/2) := by
    rw [he2]
    linarith
  have h := three_range_mass_power_bound (u := u+(g-b)/2) (β := (b+g)/2) F
    hδ hδ1 hr (by positivity) hv' hv1' hgap' hC
    (by simpa only [he1] using hf) (by simpa only [he1] using hi) hp
  simpa only [he1,he2,he3] using h

theorem exists_intermediate_L2_energy_consumer (kernel : SmoothKernel) {u b a κ : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hb : 0 < b) (hκ : 2*b < κ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      (∀ R : ℝ, δ ≤ R → R ≤ δ^a → R ≤ r₀ →
        densityL2 ρ (kernelProfile kernel R) ≤ ENNReal.ofReal (R^(u-1-b))) →
      smoothEnergy kernel.law u δ ρ ≤ ENNReal.ofReal (δ^(-κ)) := by
  let g : ℝ := min b ((1-u)/2)
  have hg : 0 < g := lt_min hb (by linarith)
  have hgb : g ≤ b := min_le_left _ _
  have hv1 : u+g ≤ 1 := by have h := min_le_right b ((1-u)/2); dsimp [g]; linarith
  have hv : 0 < u+g := by positivity
  have hgap : a*(u+g) ≤ b+g :=
    (mul_le_mul_of_nonneg_left hv1 ha.le).trans (by linarith)
  obtain ⟨C,hC,hpair⟩ := exists_smooth_pairMass_le_actual_L2 kernel
  let B : ℝ := max 2 (max C (4^(u+g)))
  have hB : 0 < B := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_left _ _)
  obtain ⟨E,hE,henergy⟩ := exists_rieszEnergy_bound_of_pairMass_power hu (by linarith : u<u+g)
  obtain ⟨δ₂,hδ₂,hδ₂1,hpay⟩ := exists_absorb_energy_additive_constant
    (show 0 ≤ E*B by positivity) (show 0 < (b+g)/2 by positivity) (by linarith : 2*((b+g)/2)<κ)
  let δ₀ : ℝ := min δ₂ (min 1 (r₀^(1/a)))
  refine ⟨δ₀,lt_min hδ₂ (lt_min (by norm_num) (by positivity)),
    (min_le_right _ _).trans (min_le_left _ _),?_⟩
  intro δ hδ hδsmall ρ _ hL2
  have hδ1 : δ ≤ 1 := (hδsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hwindow : δ ≤ δ^a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ha1
  have htop : δ^a ≤ r₀ := by
    calc
      _ ≤ (r₀^(1/a))^a := Real.rpow_le_rpow hδ.le
        ((hδsmall.trans (min_le_right _ _)).trans (min_le_right _ _)) ha.le
      _ = r₀ := by rw [← Real.rpow_mul hr₀.le,one_div_mul_cancel ha.ne',Real.rpow_one]
  have : IsProbabilityMeasure (smoothLaw kernel.law δ ρ) := by unfold smoothLaw; infer_instance
  have : NullSingletonClass (smoothLaw kernel.law δ ρ) := by
    rw [smoothLaw_eq_withDensity kernel ρ hδ.ne']
    infer_instance
  have hall (r : ℝ) (hr : 0 < r) : pairMass r (smoothLaw kernel.law δ ρ) ≤
      ENNReal.ofReal (B*δ^(-(b+g))*r^(u+g)) := by
    apply three_range_mass_power_bound_separated _ hδ hδ1 hr hb hg hv.le hv1 hgap hC.le
    · exact (smooth_pairMass_fine_radius_bound kernel ρ hδ.ne' hr.le).trans
        ((mul_le_mul_right (hL2 δ le_rfl hwindow (hwindow.trans htop)) _).trans_eq
          (ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)).symm)
    · intro hδr hrr
      exact (hpair ρ δ r hr).trans
        ((mul_le_mul_right (hL2 (4*r) hδr hrr (hrr.trans htop)) _).trans_eq
          (ENNReal.ofReal_mul (by positivity : 0 ≤ C*r)).symm)
    · calc
        _ ≤ ∫⁻ _ : ℝ, (1:ℝ≥0∞) ∂smoothLaw kernel.law δ ρ := lintegral_mono (fun _ ↦ prob_le_one)
        _ = 1 := by simp
  have he := henergy (smoothLaw kernel.law δ ρ) (B*δ^(-(b+g))) (by positivity)
    (fun r hr ↦ by simpa only [mul_assoc] using hall r hr)
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  have hp := hpay δ hδ (hδsmall.trans (min_le_left _ _))
  have hexp : -2*((b+g)/2) = -(b+g) := by ring
  simpa only [hexp,mul_assoc] using hp

#print axioms three_range_mass_power_bound_separated
#print axioms exists_intermediate_L2_energy_consumer
end OAI.Falconer
