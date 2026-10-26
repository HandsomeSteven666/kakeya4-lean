import Kakeya4.Hard.MultiplicativeConvolution.Complete
import Kakeya4.Hard.MultiplicativeConvolution.GeneratedLaw

/-! A real consumer of the complete OSS theorem for sums of independent products.
Constants precede the number of summands as well as all input laws and scales.
Source: manuscript re:generated-coefficient and the Fourier step of re:flat-coefficients.
The final interval mass estimate and ratio-law energy producer remain separate. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

theorem generatedProductSumLaw_decay (kernel : SmoothKernel) (n : ℕ) (hn : 2 ≤ n)
    (s : Fin n → ℝ) (hs : ∀ j, 0 < s j ∧ s j ≤ 1) (hsum : 1 < ∑ j, s j) :
    ∃ r₀ ε τ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < τ ∧ τ ≤ 1 ∧
      ∀ (k : ℕ) (μ : Fin n → Measure ℝ), (∀ j, IsProbabilityMeasure (μ j)) →
        (∀ j, UnitSupported (μ j)) →
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          (∀ j, smoothEnergy kernel.law (s j) r (μ j) ≤ ENNReal.ofReal (r ^ (-ε))) →
          ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ →
            ‖fourier (generatedProductSumLaw μ k) ξ‖ ≤ (|ξ| ^ (-τ)) ^ k := by
  obtain ⟨r₀, ε, τ, hr₀, hr₀1, hε, hε1, hτ, hτ1, hdecay⟩ :=
    finiteScaleDecay_proof kernel n hn s hs hsum
  refine ⟨r₀, ε, τ, hr₀, hr₀1, hε, hε1, hτ, hτ1, ?_⟩
  intro k μ hμ hsupp r hr hrr henergy ξ hξ hξ'
  let : ∀ j, IsProbabilityMeasure (μ j) := hμ
  rw [norm_fourier_generatedProductSumLaw]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (hdecay μ hμ hsupp r hr hrr henergy ξ hξ hξ') k

#print axioms generatedProductSumLaw_decay
end Kakeya4.Hard.MultiplicativeConvolution
