import Kakeya4.Hard.MultiplicativeConvolution.SmoothEnergyL2

/-!
# Fine-scale density controlled by the original-scale energy

The factor r/rho is explicit; no comparison between two unproved smoothed
energies is assumed. This pays fixed refinements such as rho=r/10.
-/

noncomputable section
open MeasureTheory Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Actual pair mass increases with the physical encounter radius. -/
theorem pairMass_mono (μ : Measure ℝ) {a b : ℝ} (hab : a ≤ b) :
    pairMass a μ ≤ pairMass b μ := by
  exact lintegral_mono (fun x ↦ measure_mono (closedBall_subset_closedBall hab))

/-- Fine-scale density needs only pair mass at the coarser scale. -/
theorem fine_densityL2_le_pairMass (κ : SmoothKernel) {M : ℝ}
    (hM : ∀ z, κ.density z ≤ M) (μ : Measure ℝ) [SFinite μ]
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    densityL2 μ (kernelProfile κ ρ) ≤
      (ENNReal.ofReal |ρ⁻¹| * ENNReal.ofReal M) * pairMass (2*r) μ := by
  exact (densityL2_kernelProfile_le_pairMass κ hM μ hρ).trans
    (mul_le_mul_right (pairMass_mono μ (by linarith : 2*ρ ≤ 2*r)) _)

/-- Fine-scale L2 bound with a constant chosen before both scales and the law. -/
theorem exists_twoScale_density_L2_bound (κ : SmoothKernel) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ] (ρ r : ℝ),
      0 < ρ → ρ ≤ r → densityL2 μ (kernelProfile κ ρ) ≤
        ENNReal.ofReal (C * (r/ρ) * r ^ (s-1)) * smoothEnergy κ.law s r μ := by
  obtain ⟨M,hMpos,hM⟩ := κ.exists_height
  refine ⟨M * 6 ^ s, mul_pos hMpos (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro μ _ ρ r hρ hρr
  have hr : 0 < r := hρ.trans_le hρr
  have hpos : (0 : ℝ) < 6*r := by positivity
  have hb := fine_densityL2_le_pairMass κ hM μ hρ hρr
  have he : ENNReal.ofReal (6*r) ^ (-s) * pairMass (2*r) μ ≤ smoothEnergy κ.law s r μ := by
    simpa only [show 3*(2*r) = 6*r by ring] using
      pairMass_le_smoothEnergy κ.law κ.law_unitSupported μ hs hr.le
        (by positivity : 0 < 2*r) (by linarith : r ≤ 2*r)
  have hmul : ENNReal.ofReal (6*r) ^ (-s) * densityL2 μ (kernelProfile κ ρ) ≤
      (ENNReal.ofReal |ρ⁻¹| * ENNReal.ofReal M) * smoothEnergy κ.law s r μ := by
    calc
      _ ≤ ENNReal.ofReal (6*r) ^ (-s) *
          ((ENNReal.ofReal |ρ⁻¹| * ENNReal.ofReal M) * pairMass (2*r) μ) := mul_le_mul_right hb _
      _ = (ENNReal.ofReal |ρ⁻¹| * ENNReal.ofReal M) *
          (ENNReal.ofReal (6*r) ^ (-s) * pairMass (2*r) μ) := by ac_rfl
      _ ≤ _ := mul_le_mul_right he _
  have hcancel : ENNReal.ofReal (6*r) ^ s * ENNReal.ofReal (6*r) ^ (-s) = 1 := by
    rw [← ENNReal.rpow_add s (-s) (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) ENNReal.ofReal_ne_top]
    simp
  have h := mul_le_mul_right hmul (ENNReal.ofReal (6*r) ^ s)
  rw [← mul_assoc, hcancel, one_mul] at h
  have hfactor : ENNReal.ofReal (6*r) ^ s * (ENNReal.ofReal |ρ⁻¹| * ENNReal.ofReal M) =
      ENNReal.ofReal (M * 6 ^ s * (r/ρ) * r ^ (s-1)) := by
    rw [ENNReal.ofReal_rpow_of_pos hpos, abs_of_pos (inv_pos.mpr hρ),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)]
    congr 1
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) hr.le, Real.rpow_sub hr, Real.rpow_one]
    field_simp
  rw [← mul_assoc, hfactor] at h
  exact h

end Kakeya4.Hard.MultiplicativeConvolution
