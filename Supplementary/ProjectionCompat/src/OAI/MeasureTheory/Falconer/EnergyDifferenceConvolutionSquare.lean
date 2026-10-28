import OAI.MeasureTheory.Falconer.DifferenceConvolutionEightLaw

/-! Original smooth-energy inputs, with the actual source Π ∗ Π as output law. -/
set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem energy_difference_mconv_square_large_image (κ : SmoothKernel) {s t σ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 ≤ σ) (hσmax : σ < min (s+t) 1) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ r : ℝ, ∀ hr : 0 < r, r ≤ r₀ →
    ∀ μ ν : Measure ℝ, ∀ [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
      smoothEnergy κ.law t r ν ≤ ENNReal.ofReal (r^(-ε)) →
      ∀ E : Set ℝ, ENNReal.ofReal (r^ε) ≤
        ((differenceLaw μ ∗ₘ differenceLaw ν) ∗ (differenceLaw μ ∗ₘ differenceLaw ν)) E →
        (Nat.ceil (r^(-σ)) : ℕ∞) ≤ externalCoveringNumber ⟨r,hr.le⟩ E := by
  obtain ⟨ε,r₀,hε,hr₀,hr₀1,hlarge⟩ :=
    energy_eight_variable_large_image κ hs hs1 ht ht1 hσ hσmax
  refine ⟨ε,r₀,hε,hr₀,hr₀1,?_⟩
  intro r hr hrr μ ν _ _ hμU hνU hμE hνE E hE
  apply hlarge r hr hrr (sourceEightMarginals μ ν)
  · intro i
    fin_cases i <;> dsimp [sourceEightMarginals] <;> assumption
  · intro i
    fin_cases i <;> dsimp [sourceEightMarginals] <;> assumption
  · rw [original_pi_eight_eq_difference_mconv_square]
    exact hE

#print axioms energy_difference_mconv_square_large_image
end OAI.Falconer
