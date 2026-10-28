import OAI.MeasureTheory.Falconer.FlatteningDeficitEnergy

/-! The real Fourier transfer in OSS Section 4, with actual additive powers. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution

theorem fourier_additiveLawPower (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) (ξ : ℝ) :
    fourier (additiveLawPower μ k) ξ = (fourier μ ξ)^k := by
  induction k with
  | zero => simp [additiveLawPower,Kakeya4.Hard.MultiplicativeConvolution.fourier]
  | succ k ih =>
    change fourier (additiveLawPower μ k ∗ μ) ξ = _
    rw [fourier_additiveConvolution,ih,pow_succ]

theorem fourier_difference_product_im_zero (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ξ : ℝ) :
    (fourier (differenceLaw μ ∗ₘ differenceLaw ν) ξ).im = 0 := by
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  rw [fourier_difference_mconv]
  rfl

theorem fourier_additiveLawPower_im_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hreal : ∀ ξ : ℝ, (fourier μ ξ).im=0) (k : ℕ) (ξ : ℝ) :
    (fourier (additiveLawPower μ k) ξ).im=0 := by
  have hz : fourier μ ξ = ((fourier μ ξ).re : ℂ) := by
    apply Complex.ext <;> simp [hreal ξ]
  rw [fourier_additiveLawPower,hz,← Complex.ofReal_pow]
  rfl

theorem norm_fourier_real_mconv_sq_le_double (ρ lawL : Measure ℝ)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure lawL]
    (hreal : ∀ ξ : ℝ, (fourier ρ ξ).im=0) (ξ : ℝ) :
    ‖fourier (ρ ∗ₘ lawL) ξ‖^2 ≤ ‖fourier ((ρ ∗ ρ) ∗ₘ lawL) ξ‖ := by
  have heq (t : ℝ) : fourier (differenceLaw ρ) t = fourier (ρ ∗ ρ) t := by
    have hz : fourier ρ t = ((fourier ρ t).re : ℂ) := by
      apply Complex.ext <;> simp [hreal t]
    rw [fourier_differenceLaw,fourier_additiveConvolution,hz]
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.ofReal_pow,pow_two]
  have : IsProbabilityMeasure (differenceLaw ρ) := by unfold differenceLaw; infer_instance
  have hconv : fourier (differenceLaw ρ ∗ₘ lawL) ξ = fourier ((ρ ∗ ρ) ∗ₘ lawL) ξ := by
    rw [Measure.mconv_comm (differenceLaw ρ) lawL,Measure.mconv_comm (ρ ∗ ρ) lawL,
      fourier_multiplicativeConvolution,fourier_multiplicativeConvolution]
    simp_rw [heq]
  have hb := norm_fourier_mconv_sq_le_difference ρ lawL ξ
  rw [hconv] at hb
  exact hb.trans (Complex.re_le_norm _)

theorem norm_fourier_three_product_fourth_le_difference_product (μ ν lawL : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure lawL] (ξ : ℝ) :
    ‖fourier ((μ ∗ₘ ν) ∗ₘ lawL) ξ‖^4 ≤
      ‖fourier ((differenceLaw μ ∗ₘ differenceLaw ν) ∗ₘ lawL) ξ‖ := by
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have h₁ := norm_fourier_mconv_sq_le_difference μ (ν ∗ₘ lawL) ξ
  rw [← Measure.mconv_assoc μ ν lawL] at h₁
  have h₂ := norm_fourier_mconv_sq_le_difference ν (differenceLaw μ ∗ₘ lawL) ξ
  have heq₁ : ν ∗ₘ (differenceLaw μ ∗ₘ lawL) = differenceLaw μ ∗ₘ (ν ∗ₘ lawL) := by
    rw [← Measure.mconv_assoc,Measure.mconv_comm ν (differenceLaw μ),Measure.mconv_assoc]
  have heq₂ : differenceLaw ν ∗ₘ (differenceLaw μ ∗ₘ lawL) =
      (differenceLaw μ ∗ₘ differenceLaw ν) ∗ₘ lawL := by
    rw [← Measure.mconv_assoc,Measure.mconv_comm (differenceLaw ν) (differenceLaw μ)]
  rw [heq₁,heq₂] at h₂
  have h₁' := h₁.trans (Complex.re_le_norm _)
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖fourier ((μ ∗ₘ ν) ∗ₘ lawL) ξ‖^2) h₁' 2
  have hp : (‖fourier ((μ ∗ₘ ν) ∗ₘ lawL) ξ‖^2)^2 = ‖fourier ((μ ∗ₘ ν) ∗ₘ lawL) ξ‖^4 := by ring
  rw [hp] at hs
  exact hs.trans (h₂.trans (Complex.re_le_norm _))

theorem norm_fourier_three_product_le_flattened_power (μ ν lawL : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure lawL] (ξ : ℝ) (n : ℕ) :
    ‖fourier ((μ ∗ₘ ν) ∗ₘ lawL) ξ‖^((2:ℕ)^(n+2)) ≤
      ‖fourier ((additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) (2^n)) ∗ₘ lawL) ξ‖ := by
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  induction n with
  | zero =>
    simpa [additiveLawPower] using norm_fourier_three_product_fourth_le_difference_product μ ν lawL ξ
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,pow_succ,pow_mul]
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖fourier ((μ ∗ₘ ν) ∗ₘ lawL) ξ‖^(2^(n+2))) ih 2
    have hd := norm_fourier_real_mconv_sq_le_double
      (additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) (2^n)) lawL
      (fourier_additiveLawPower_im_zero _ (fourier_difference_product_im_zero μ ν) _) ξ
    exact hs.trans (by simpa only [pow_succ',additiveLawPower_double] using hd)

#print axioms fourier_additiveLawPower
#print axioms fourier_difference_product_im_zero
#print axioms fourier_additiveLawPower_im_zero
#print axioms norm_fourier_real_mconv_sq_le_double
#print axioms norm_fourier_three_product_fourth_le_difference_product
#print axioms norm_fourier_three_product_le_flattened_power
end OAI.Falconer

