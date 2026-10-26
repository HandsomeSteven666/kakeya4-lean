import Kakeya4.Hard.MultiplicativeConvolution.FrostmanExtraction
import Kakeya4.Hard.MultiplicativeConvolution.SmallScalePowers

/-!
# Exact scale-power Frostman coefficients from the original energy

The fixed kernel/normalization constant is absorbed before selecting input laws.
This supplies real input laws for the projection step, not the projection theorem.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Original energy yields the precise r^-eta coefficient at every positive radius. -/
theorem exists_exact_Frostman_probability_extraction (κ : SmoothKernel)
    {s η : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], UnitSupported μ →
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
          ∃ A : Set ℝ, MeasurableSet A ∧ μ Aᶜ ≤ ENNReal.ofReal (r^ε) ∧
            IsProbabilityMeasure (unitRescaledSmoothLaw κ r (normalizedRestriction μ A)) ∧
            UnitSupported (unitRescaledSmoothLaw κ r (normalizedRestriction μ A)) ∧
            ∀ (z R : ℝ), 0 < R →
              unitRescaledSmoothLaw κ r (normalizedRestriction μ A) (closedBall z R) ≤
                ENNReal.ofReal (r^(-η)*R^s) := by
  let ε := η/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by dsimp [ε]; linarith
  obtain ⟨C,r₁,hC,hr₁,hr₁1,hextract⟩ := exists_uniform_Frostman_probability_extraction κ hs hs1 hε
  obtain ⟨r₂,hr₂,hr₂1,hsmall⟩ :=
    exists_small_scale_power_bound (C := C) (a := η/2) (τ := 0) hC.le (by positivity)
  refine ⟨ε,min r₁ r₂,hε,hε1,lt_min hr₁ hr₂,(min_le_left _ _).trans hr₁1,?_⟩
  intro μ _ hμ r hr hrr he
  obtain ⟨A,hA,hbad,hprob,hsupp,hball⟩ := hextract μ hμ r hr (hrr.trans (min_le_left _ _)) he
  have hc : C*r^(-2*ε) ≤ r^(-η) := by
    have h := hsmall r hr (hrr.trans (min_le_right _ _))
    simp only [neg_zero, Real.rpow_zero, one_mul] at h
    have hm := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hr.le (-η))
    rw [one_mul, mul_assoc, ← Real.rpow_add hr] at hm
    have heq : η/2+(-η) = -2*ε := by dsimp [ε]; ring
    simpa only [heq] using hm
  refine ⟨A,hA,hbad,hprob,hsupp,?_⟩
  intro z R hR
  exact (hball z R hR).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc (by positivity)))

end Kakeya4.Hard.MultiplicativeConvolution
