import Kakeya4.Hard.MultiplicativeConvolution.RescaledSmoothing
import Kakeya4.Hard.MultiplicativeConvolution.NormalizedRestriction

/-!
# Actual all-radius Frostman probability laws extracted from the original energy

Every law is explicitly a normalized restriction followed by the original
smoothing and the fixed half dilation. All constants precede the input law.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Exact independent-noise integration formula for the actual rescaled smoothed law. -/
theorem lintegral_unitRescaledSmoothLaw (κ : SmoothKernel) (μ : Measure ℝ) [SFinite μ]
    (r : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂unitRescaledSmoothLaw κ r μ) =
      ∫⁻ x, ∫⁻ u, f ((x+r*u)/2) ∂κ.law ∂μ := by
  rw [unitRescaledSmoothLaw, lintegral_map hf (by fun_prop)]
  exact lintegral_smoothLaw κ.law μ r
    (f := fun x ↦ f (x/2)) (hf.comp (by fun_prop))

/-- Original energy produces actual unit-supported all-radius Frostman probability laws. -/
theorem exists_uniform_Frostman_probability_extraction (κ : SmoothKernel)
    {s ε : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 < ε) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], UnitSupported μ →
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
          ∃ A : Set ℝ, MeasurableSet A ∧ μ Aᶜ ≤ ENNReal.ofReal (r^ε) ∧
            IsProbabilityMeasure (unitRescaledSmoothLaw κ r (normalizedRestriction μ A)) ∧
            UnitSupported (unitRescaledSmoothLaw κ r (normalizedRestriction μ A)) ∧
            ∀ (z R : ℝ), 0 < R →
              unitRescaledSmoothLaw κ r (normalizedRestriction μ A) (closedBall z R) ≤
                ENNReal.ofReal (C*r^(-2*ε)*R^s) := by
  obtain ⟨C,hC,hball⟩ := exists_unitRescaledSmoothLaw_all_scale_ball_bound κ hs hs1
  obtain ⟨r₀,hr₀,hr₀1,hextract⟩ := exists_uniform_nonconcentrated_probability_restriction κ hs hε
  refine ⟨C*2*(6:ℝ)^s,r₀,mul_pos (mul_pos hC (by norm_num)) (by positivity),hr₀,hr₀1,?_⟩
  intro μ _ hμ r hr hrr he
  obtain ⟨A,hA,hbad,hprob,hsupp,hcoarse⟩ := hextract μ hμ r hr hrr he
  letI : IsProbabilityMeasure (normalizedRestriction μ A) := hprob
  refine ⟨A,hA,hbad,inferInstance,
    unitRescaledSmoothLaw_unitSupported κ _ hr.le (hrr.trans hr₀1) hsupp,?_⟩
  intro z R hR
  have hb := hball (normalizedRestriction μ A) r (2*(6:ℝ)^s*r^(-2*ε)) hr (by positivity)
    (by intro z R hR; simpa only [mul_assoc] using hcoarse z R hR) z R hR
  have heq : C*(2*(6:ℝ)^s*r^(-2*ε))*R^s = (C*2*(6:ℝ)^s)*r^(-2*ε)*R^s := by ring
  simpa only [heq] using hb

end Kakeya4.Hard.MultiplicativeConvolution
