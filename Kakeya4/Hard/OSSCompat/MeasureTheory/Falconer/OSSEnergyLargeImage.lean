






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.EnergyDifferenceConvolutionPowers

/-! OSS Lemma 3.3 with actual original smooth energy and additive convolution powers. -/
set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem OSS_energy_large_image (kernel : SmoothKernel) {s t η : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hst : s+t ≤ 1) (hη : 0 < η) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ r : ℝ, ∀ hr : 0 < r, r ≤ r₀ →
    ∀ μ ν : Measure ℝ, ∀ [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy kernel.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
      smoothEnergy kernel.law t r ν ≤ ENNReal.ofReal (r^(-ε)) →
      ∀ k : ℕ, 2 ≤ k → ∀ E : Set ℝ, ENNReal.ofReal (r^ε) ≤
        additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k E →
        (Nat.ceil (r^(-s-t+η)) : ℕ∞) ≤ externalCoveringNumber ⟨r,hr.le⟩ E := by
  let σ : ℝ := max 0 (s+t-η)
  have hσ : 0 ≤ σ := le_max_left _ _
  have hσmax : σ < min (s+t) 1 := by
    rw [min_eq_left hst]
    exact max_lt (by linarith) (by linarith)
  obtain ⟨ε,r₀,hε,hr₀,hr₀1,hlarge⟩ :=
    energy_difference_mconv_all_powers_large_image kernel hs hs1 ht ht1 hσ hσmax
  refine ⟨ε,r₀,hε,hr₀,hr₀1,?_⟩
  intro r hr hrr μ ν _ _ hμU hνU hμE hνE k hk E hE
  have he : r^(-s-t+η) ≤ r^(-σ) :=
    Real.rpow_le_rpow_of_exponent_ge hr (hrr.trans hr₀1) (by
      have := le_max_right (0:ℝ) (s+t-η)
      dsimp [σ]
      linarith)
  exact (show (Nat.ceil (r^(-s-t+η)) : ℕ∞) ≤ (Nat.ceil (r^(-σ)) : ℕ∞) by
    exact_mod_cast Nat.ceil_mono he).trans
      (hlarge r hr hrr μ ν hμU hνU hμE hνE k hk E hE)

#print axioms OSS_energy_large_image
end OAI.Falconer
