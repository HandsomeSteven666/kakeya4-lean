import Kakeya4.Hard.MultiplicativeConvolution.RieszEnergy
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The full finite-scale H-004 target, with an explicit fixed smoothing kernel

This is a real statement of the remaining theorem, not a proof. Constants are
chosen after the fixed kernel, n and exponents, before the input measures and
scale. Source: arXiv:2309.03068v2 Theorem 1.5, and manuscript re:oss-input.
The original external opaque is deliberately unchanged until the proof exists.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- An actual smooth compactly supported normalized approximate-identity profile.
Its choice is fixed before all input laws. No decay or flattening is a field. -/
structure SmoothKernel where
  density : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) density
  nonneg : ∀ x, 0 ≤ density x
  outside : ∀ x, 1 < |x| → density x = 0
  positive : ∀ x, |x| ≤ 1 / 2 → 0 < density x
  integrable : Integrable density
  integral_one : ∫ x, density x = 1

/-- The kernel's actual probability law, not an unspecified smoothing operator. -/
def SmoothKernel.law (κ : SmoothKernel) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (κ.density x))

/-- Normalizing the density normalizes the kernel law. -/
instance SmoothKernel.law_isProbabilityMeasure (κ : SmoothKernel) :
    IsProbabilityMeasure κ.law := by
  constructor
  rw [SmoothKernel.law, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal κ.integrable
    (Filter.Eventually.of_forall κ.nonneg), κ.integral_one]
  exact ENNReal.ofReal_one

/-- Full optimal-energy finite-scale target. This proposition is not yet proved. -/
def FiniteScaleDecay (κ : SmoothKernel) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ s : Fin n → ℝ,
    (∀ j, 0 < s j ∧ s j ≤ 1) → 1 < ∑ j, s j →
    ∃ r₀ ε τ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < τ ∧ τ ≤ 1 ∧
      ∀ (μ : Fin n → Measure ℝ), (∀ j, IsProbabilityMeasure (μ j)) →
        (∀ j, UnitSupported (μ j)) →
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          (∀ j, smoothEnergy κ.law (s j) r (μ j) ≤ ENNReal.ofReal (r ^ (-ε))) →
          ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ →
            ‖fourier (productLaw μ) ξ‖ ≤ |ξ| ^ (-τ)

end Kakeya4.Hard.MultiplicativeConvolution
