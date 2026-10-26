import Kakeya4.Hard.MultiplicativeConvolution.TwoFactorDecay

/-! # The actual n=2 branch of the full finite-scale target -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The engineering product law at n=2 is exactly the binary multiplicative convolution. -/
theorem productLaw_finTwo (μ : Fin 2 → Measure ℝ) [∀ j, IsFiniteMeasure (μ j)] :
    productLaw μ = (μ 0) ∗ₘ (μ 1) := by
  have hp := (measurePreserving_piFinTwo μ).map_eq
  rw [Measure.mconv, ← hp]
  rw [Measure.map_map (by fun_prop : Measurable (fun p : ℝ × ℝ ↦ p.1*p.2))
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).measurable]
  unfold productLaw
  congr 1
  funext x
  simp only [Function.comp_apply, MeasurableEquiv.piFinTwo_apply, Fin.prod_univ_two]

/-- The complete n=2 branch has exactly the original target's probability-law and frequency quantifiers. -/
theorem finiteScaleDecay_two (κ : SmoothKernel) (s : Fin 2 → ℝ)
    (hs : ∀ j, 0 < s j ∧ s j ≤ 1) (hsum : 1 < ∑ j, s j) :
    ∃ r₀ ε τ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < τ ∧ τ ≤ 1 ∧
      ∀ (μ : Fin 2 → Measure ℝ), (∀ j, IsProbabilityMeasure (μ j)) →
        (∀ j, UnitSupported (μ j)) →
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          (∀ j, smoothEnergy κ.law (s j) r (μ j) ≤ ENNReal.ofReal (r^(-ε))) →
          ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2*r⁻¹ →
            ‖fourier (productLaw μ) ξ‖ ≤ |ξ|^(-τ) := by
  have hst : 1 < s 0+s 1 := by simpa only [Fin.sum_univ_two] using hsum
  obtain ⟨r₀,ε,τ,hr₀,hr₀1,hε,hε1,hτ,hτ1,hdecay⟩ :=
    exists_twoFactor_decay κ (hs 0).1 (hs 0).2 (hs 1).1 (hs 1).2 hst
  refine ⟨r₀,ε,τ,hr₀,hr₀1,hε,hε1,hτ,hτ1,?_⟩
  intro μ hprob hμ r hr hrr he ξ hlo hhi
  letI (j : Fin 2) : IsProbabilityMeasure (μ j) := hprob j
  rw [productLaw_finTwo]
  exact hdecay (μ 0) (μ 1) (hμ 0) (hμ 1) r hr hrr (he 0) (he 1) ξ hlo hhi

end Kakeya4.Hard.MultiplicativeConvolution
