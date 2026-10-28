import OAI.MeasureTheory.Falconer.FlatteningEnergyScale

/-! Original energy caps transport to the entire fractional-power scale window. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem exists_uniform_intermediate_energy_cap (kernel : SmoothKernel)
    {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], ∀ s δ r : ℝ,
      0 < s → s < 1 → 0 < δ → 0 < r → δ ≤ r → r ≤ δ^a → r ≤ r₀ →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
      smoothEnergy kernel.law s (5*r) μ ≤ ENNReal.ofReal ((5*r)^(-e)) := by
  obtain ⟨C,hC,hscale⟩ := exists_uniform_larger_smoothEnergy_bound kernel
  let ε : ℝ := a*e/2
  obtain ⟨r₀,hr₀,hr₀1,hsmall⟩ := exists_small_scale_power_bound
    (C := C*5^e) (a := e/2) (τ := 0) (by positivity) (by positivity)
  refine ⟨ε,r₀,by dsimp [ε]; positivity,hr₀,hr₀1,?_⟩
  intro μ _ s δ r hs hs1 hδ hr hδr hwindow hrr henergy
  have hp : r^(e/2) ≤ δ^ε := by
    have h := Real.rpow_le_rpow hr.le hwindow (by positivity : 0 ≤ e/2)
    rw [← Real.rpow_mul hδ.le] at h
    convert h using 1
    congr 1
    dsimp [ε]
    ring
  have hw : δ^(-ε) ≤ r^(-e/2) := by
    rw [Real.rpow_neg hδ.le,show -e/2 = -(e/2) by ring,Real.rpow_neg hr.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hδ ε) (Real.rpow_pos_of_pos hr (e/2))).mpr hp
  have hsmall' : C*5^e*r^(e/2) ≤ 1 := by
    have h := hsmall r hr hrr
    simpa only [neg_zero,Real.rpow_zero,mul_one] using h
  have hc : C*r^(-e/2) ≤ (5*r)^(-e) := by
    have h := mul_le_mul_of_nonneg_right hsmall' (Real.rpow_nonneg (by positivity : 0 ≤ 5*r) (-e))
    have h5 : (5 : ℝ)^e * 5^(-e) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 5)]
      simp
    have hfactor : C*5^e*r^(e/2)*(5*r)^(-e) = C*r^(-e/2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hr.le]
      calc
        _ = C*(5^e*5^(-e))*(r^(e/2)*r^(-e)) := by ring
        _ = C*r^(-e/2) := by
          rw [h5,mul_one,← Real.rpow_add hr]
          congr 2
          ring
    simpa only [hfactor,one_mul] using h
  calc
    _ ≤ ENNReal.ofReal C * smoothEnergy kernel.law s δ μ :=
      hscale μ δ (5*r) s hδ (by linarith) hs hs1
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (δ^(-ε)) := mul_le_mul_right henergy _
    _ = ENNReal.ofReal (C*δ^(-ε)) := (ENNReal.ofReal_mul hC.le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hw hC.le).trans hc)

#print axioms exists_uniform_intermediate_energy_cap
end OAI.Falconer
