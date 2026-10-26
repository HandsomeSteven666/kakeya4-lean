






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FourierFineScaleEnergy

/-! Fixed scaling coefficients are paid at the new physical scale, before the input law. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem exists_pay_fixed_energy_coefficient {D R ε : ℝ}
    (hD : 0 ≤ D) (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ENNReal.ofReal D*ENNReal.ofReal (δ^(-(ε/2))) ≤ ENNReal.ofReal ((δ/R)^(-ε)) := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hsmall⟩ := exists_small_scale_power_bound
    (C := D) (a := ε/2) (τ := 0) hD (by positivity)
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro δ hδ hδsmall
  have hs : D*δ^(ε/2) ≤ 1 := by
    simpa only [neg_zero,Real.rpow_zero,mul_one] using hsmall δ hδ hδsmall
  have hp : D*δ^(-(ε/2)) ≤ (δ/R)^(-ε) := by
    calc
      _ = (D*δ^(ε/2))*δ^(-ε) := by rw [mul_assoc,← Real.rpow_add hδ]; congr 2; ring
      _ ≤ 1*δ^(-ε) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ (δ/R)^(-ε) := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_nonpos (div_pos hδ (by linarith))
          (div_le_self hδ.le hR) (by linarith)
  simpa only [ENNReal.ofReal_mul hD] using ENNReal.ofReal_le_ofReal hp

theorem exists_fixed_finer_input_energy_cap (kernel : SmoothKernel) {R ε : ℝ}
    (hR : 2 ≤ R) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (μ : Measure ℝ) [SFinite μ], ∀ s : ℝ,
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-(ε/2))) →
      smoothEnergy kernel.law s (δ/R) μ ≤ ENNReal.ofReal ((δ/R)^(-ε)) := by
  obtain ⟨C,hC,hbound⟩ := exists_fixed_finer_smoothEnergy_bound kernel
  obtain ⟨δ₀,hδ₀,hδ₀1,hpay⟩ := exists_pay_fixed_energy_coefficient
    (D := C*R^2) (by positivity) (by linarith : 1≤R) hε
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro δ hδ hδsmall μ _ s hcap
  exact (hbound μ R δ s hR hδ).trans ((mul_le_mul_right hcap _).trans (hpay δ hδ hδsmall))

theorem exists_normalized_input_energy_cap (kernel : SmoothKernel) {R ε : ℝ}
    (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], ∀ s : ℝ, s ≤ 1 →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-(ε/2))) →
      smoothEnergy kernel.law s (δ/R) (μ.map (fun x : ℝ ↦ x/R)) ≤
        ENNReal.ofReal ((δ/R)^(-ε)) := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hpay⟩ := exists_pay_fixed_energy_coefficient (D := R) (by linarith) hR hε
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro δ hδ hδsmall μ _ s hs1 hcap
  rw [normalized_smoothEnergy_exact kernel μ (by linarith : 0<R)]
  have hc : ENNReal.ofReal (R^s) ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR hs1)
  exact (mul_le_mul' hc hcap).trans (hpay δ hδ hδsmall)

#print axioms exists_pay_fixed_energy_coefficient
#print axioms exists_fixed_finer_input_energy_cap
#print axioms exists_normalized_input_energy_cap
end OAI.Falconer
