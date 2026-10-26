import Kakeya4.Hard.MultiplicativeConvolution.DensityL2

/-!
# Actual smooth energy bounds the squared L2 density

The bound is obtained in physical space from independent noise and pair mass,
without assuming a Fourier-Riesz identity. Constants depend on the fixed smooth
profile and s, and are fixed before the original law and scale. The density is
the one already proved to represent smoothLaw, also for singular original laws.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual scaled profile converts pair mass into a density L2 bound. -/
theorem densityL2_kernelProfile_le_pairMass (κ : SmoothKernel) {M : ℝ}
    (hM : ∀ z, κ.density z ≤ M) (μ : Measure ℝ) [SFinite μ]
    {r : ℝ} (hr : 0 < r) :
    densityL2 μ (kernelProfile κ r) ≤
      (ENNReal.ofReal |r⁻¹| * ENNReal.ofReal M) * pairMass (2*r) μ := by
  apply densityL2_le_pairMass μ _ (measurable_kernelProfile κ r)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (kernelProfile_le κ hM r) (kernelProfile_integral κ hr.ne') r
  exact fun z hz ↦ kernelProfile_zero_of_radius κ hr hz

/-- Intermediate energy estimate, keeping the exact physical scale factors. -/
theorem densityL2_kernelProfile_mul_le_energy (κ : SmoothKernel) {M : ℝ}
    (hM : ∀ z, κ.density z ≤ M) (μ : Measure ℝ) [SFinite μ]
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) :
    ENNReal.ofReal (6*r) ^ (-s) * densityL2 μ (kernelProfile κ r) ≤
      (ENNReal.ofReal |r⁻¹| * ENNReal.ofReal M) * smoothEnergy κ.law s r μ := by
  have hb := densityL2_kernelProfile_le_pairMass κ hM μ hr
  have he : ENNReal.ofReal (6*r) ^ (-s) * pairMass (2*r) μ ≤ smoothEnergy κ.law s r μ := by
    simpa only [show 3*(2*r) = 6*r by ring] using
      pairMass_le_smoothEnergy κ.law κ.law_unitSupported μ hs hr.le
        (by positivity : 0 < 2*r) (by linarith : r ≤ 2*r)
  calc
    _ ≤ ENNReal.ofReal (6*r) ^ (-s) *
        ((ENNReal.ofReal |r⁻¹| * ENNReal.ofReal M) * pairMass (2*r) μ) := mul_le_mul_right hb _
    _ = (ENNReal.ofReal |r⁻¹| * ENNReal.ofReal M) *
        (ENNReal.ofReal (6*r) ^ (-s) * pairMass (2*r) μ) := by ac_rfl
    _ ≤ _ := mul_le_mul_right he _

/-- The physical scale factor has the manuscript's exact r^(s-1) exponent. -/
theorem densityL2_kernelProfile_le_energy (κ : SmoothKernel) {M : ℝ}
    (hM : ∀ z, κ.density z ≤ M) (μ : Measure ℝ) [SFinite μ]
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) :
    densityL2 μ (kernelProfile κ r) ≤
      ENNReal.ofReal ((M * 6 ^ s) * r ^ (s-1)) * smoothEnergy κ.law s r μ := by
  have he := densityL2_kernelProfile_mul_le_energy κ hM μ hs hr
  have hpos : (0 : ℝ) < 6*r := by positivity
  have hcancel : ENNReal.ofReal (6*r) ^ s * ENNReal.ofReal (6*r) ^ (-s) = 1 := by
    rw [← ENNReal.rpow_add s (-s) (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) ENNReal.ofReal_ne_top]
    simp
  have hbound : densityL2 μ (kernelProfile κ r) ≤
      (ENNReal.ofReal (6*r) ^ s * (ENNReal.ofReal |r⁻¹| * ENNReal.ofReal M)) *
        smoothEnergy κ.law s r μ := by
    have h := mul_le_mul_right he (ENNReal.ofReal (6*r) ^ s)
    simpa only [← mul_assoc, hcancel, one_mul] using h
  have hfactor : ENNReal.ofReal (6*r) ^ s * (ENNReal.ofReal |r⁻¹| * ENNReal.ofReal M) =
      ENNReal.ofReal ((M * 6 ^ s) * r ^ (s-1)) := by
    rw [ENNReal.ofReal_rpow_of_pos hpos, abs_of_pos (inv_pos.mpr hr),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)]
    congr 1
    calc
      _ = M * 6 ^ s * (r ^ s * r ^ (-1 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) hr.le, Real.rpow_neg_one]
        ring
      _ = _ := by rw [← Real.rpow_add hr]; simp only [sub_eq_add_neg]
  simpa only [hfactor] using hbound

/-- A fixed, positive, finite constant is chosen before every original law and scale. -/
theorem exists_smooth_density_L2_bound (κ : SmoothKernel) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ] (r : ℝ), 0 < r →
      densityL2 μ (kernelProfile κ r) ≤
        ENNReal.ofReal (C * r ^ (s-1)) * smoothEnergy κ.law s r μ := by
  obtain ⟨M,hMpos,hM⟩ := κ.exists_height
  refine ⟨M * 6 ^ s, mul_pos hMpos (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro μ _ r hr
  exact densityL2_kernelProfile_le_energy κ hM μ hs hr

/-- Finite original smoothed energy implies finite actual squared density mass. -/
theorem densityL2_ne_top_of_energy (κ : SmoothKernel) (μ : Measure ℝ) [SFinite μ]
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (hE : smoothEnergy κ.law s r μ ≠ ⊤) :
    densityL2 μ (kernelProfile κ r) ≠ ⊤ := by
  obtain ⟨C,_,hC⟩ := exists_smooth_density_L2_bound κ hs
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE) (hC μ r hr)

/-- The exact energy cap yields the L2 exponent needed in the two-factor base case.
The constant precedes μ, r and ε; no extra L2 hypothesis is introduced. -/
theorem exists_smooth_density_L2_bound_of_energy_cap (κ : SmoothKernel) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ] (r ε : ℝ), 0 < r →
      smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r ^ (-ε)) →
      densityL2 μ (kernelProfile κ r) ≤ ENNReal.ofReal (C * r ^ (s-1-ε)) := by
  obtain ⟨C,hCpos,hC⟩ := exists_smooth_density_L2_bound κ hs
  refine ⟨C,hCpos,?_⟩
  intro μ _ r ε hr hE
  calc
    _ ≤ ENNReal.ofReal (C * r ^ (s-1)) * smoothEnergy κ.law s r μ := hC μ r hr
    _ ≤ ENNReal.ofReal (C * r ^ (s-1)) * ENNReal.ofReal (r ^ (-ε)) := mul_le_mul_right hE _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hCpos.le (Real.rpow_nonneg hr.le _))]
      congr 1
      rw [mul_assoc, ← Real.rpow_add hr]
      simp only [sub_eq_add_neg]

end Kakeya4.Hard.MultiplicativeConvolution
