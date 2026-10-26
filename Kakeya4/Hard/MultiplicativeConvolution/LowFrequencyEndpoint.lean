import Kakeya4.Hard.MultiplicativeConvolution.LowFrequencyMass

/-!
# The true low-frequency Fourier estimate from the original energy cap

Constants precede all laws and positive scales. This supplies the frequency
mass needed in the two-factor argument; it is not the oscillatory bound itself.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Original energy controls the actual sharp Fourier window, with the exact scale exponent. -/
theorem lowFrequencyMass_le_energy (κ : SmoothKernel) {s K r : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hK : 1 ≤ K) (hr : 0 < r)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    lowFrequencyMass (K/r) μ ≤
      ENNReal.ofReal ((gaussianWindowConstant * K * 3^s) * r^(s-1)) * smoothEnergy κ.law s r μ := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hR : 0 < K/r := div_pos hKpos hr
  have hRr : 1 ≤ (K/r)*r := by simpa only [div_mul_cancel₀ _ hr.ne'] using hK
  have hg := gaussianFourierMass_le_smoothEnergy κ hs hs1 hr hRr μ
  calc
    _ ≤ ENNReal.ofReal (gaussianWindowConstant*(K/r)) *
        ENNReal.ofReal (gaussianFourierMass (K/r) μ) := lowFrequencyMass_le_gaussian hR μ
    _ ≤ ENNReal.ofReal (gaussianWindowConstant*(K/r)) *
        (ENNReal.ofReal ((3*r)^s) * smoothEnergy κ.law s r μ) := mul_le_mul_right hg _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg gaussianWindowConstant_pos.le hR.le)]
      congr 1
      congr 1
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr.le, Real.rpow_sub hr, Real.rpow_one]
      field_simp

/-- Under the original finite-scale energy cap, the exact Fourier exponent is s-1-epsilon. -/
theorem exists_lowFrequencyMass_bound (κ : SmoothKernel) {s K : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (r ε : ℝ), 0 < r →
      smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
      lowFrequencyMass (K/r) μ ≤ ENNReal.ofReal (C * r^(s-1-ε)) := by
  let C := gaussianWindowConstant * K * 3^s
  have hCpos : 0 < C := mul_pos (mul_pos gaussianWindowConstant_pos (zero_lt_one.trans_le hK))
    (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C,hCpos,?_⟩
  intro μ _ r ε hr he
  calc
    _ ≤ ENNReal.ofReal (C*r^(s-1)) * smoothEnergy κ.law s r μ :=
      lowFrequencyMass_le_energy κ hs hs1 hK hr μ
    _ ≤ ENNReal.ofReal (C*r^(s-1)) * ENNReal.ofReal (r^(-ε)) := mul_le_mul_right he _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hCpos.le (Real.rpow_nonneg hr.le _))]
      congr 1
      rw [mul_assoc, ← Real.rpow_add hr]
      simp only [sub_eq_add_neg]

/-- The real squared-amplitude function is integrable on every finite Fourier window. -/
theorem integrableOn_fourier_sq (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ) :
    IntegrableOn (fun t ↦ ‖fourier μ t‖ ^ 2) (Icc (-R) R) := by
  have hm : Measurable (fun t ↦ ‖fourier μ t‖ ^ 2) := by
    unfold fourier
    exact (measurable_charFun.comp (by fun_prop)).norm.pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable (μ.real univ ^ 2)
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

/-- The actual sharp nonnegative Fourier mass agrees with the ordinary real integral. -/
theorem ofReal_integral_fourier_sq (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ) :
    ENNReal.ofReal (∫ t in Icc (-R) R, ‖fourier μ t‖ ^ 2) = lowFrequencyMass R μ :=
  ofReal_integral_eq_lintegral_ofReal (integrableOn_fourier_sq μ R)
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))

/-- Ordinary real Fourier-window estimate, not a proxy or a supplied certificate. -/
theorem exists_integral_fourier_sq_bound (κ : SmoothKernel) {s K : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (r ε : ℝ), 0 < r →
      smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
      (∫ t in Icc (-(K/r)) (K/r), ‖fourier μ t‖ ^ 2) ≤ C*r^(s-1-ε) := by
  obtain ⟨C,hCpos,hC⟩ := exists_lowFrequencyMass_bound κ hs hs1 hK
  refine ⟨C,hCpos,?_⟩
  intro μ _ r ε hr he
  have hb := hC μ r ε hr he
  rw [← ofReal_integral_fourier_sq] at hb
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ sq_nonneg _)),
    ENNReal.toReal_ofReal (mul_nonneg hCpos.le (Real.rpow_nonneg hr.le _))] at h
  exact h

end Kakeya4.Hard.MultiplicativeConvolution
