import Kakeya4.Hard.MultiplicativeConvolution.PotentialRestriction
import Kakeya4.Hard.MultiplicativeConvolution.EndpointStatement
import Kakeya4.Hard.MultiplicativeConvolution.FixedKernel

/-!
# Large-mass nonconcentrated restrictions from the original smooth energy

The threshold is explicit, and the same actual Borel restriction works for
every center and radius. No dyadic union or supplied Frostman certificate.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Explicit threshold whose Markov loss is r^epsilon. -/
def energyPotentialThreshold (s r ε : ℝ) : ℝ := (3:ℝ)^s*r^(-2*ε)

/-- The threshold is positive for every positive original scale. -/
theorem energyPotentialThreshold_pos (s ε : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < energyPotentialThreshold s r ε := mul_pos (by positivity) (Real.rpow_pos_of_pos hr _)

/-- Capped energy inherits the actual original smooth-energy cap. -/
theorem cappedEnergy_le_of_smoothEnergy_cap (κ : SmoothKernel) (μ : Measure ℝ) [SFinite μ]
    {s r ε : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (he : smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε))) :
    cappedEnergy s r μ ≤ ENNReal.ofReal ((3:ℝ)^s*r^(-ε)) := by
  have he' := (smoothEnergy_ge_capped κ.law κ.law_unitSupported μ hs hr.le).trans he
  have hcancel : ENNReal.ofReal 3 ^ s * ENNReal.ofReal 3 ^ (-s) = 1 := by
    rw [← ENNReal.rpow_add s (-s) (by norm_num) ENNReal.ofReal_ne_top]
    simp
  have h := mul_le_mul_right he' (ENNReal.ofReal 3 ^ s)
  rw [← mul_assoc, hcancel, one_mul] at h
  rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 3),
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 3^s)] at h
  exact h

/-- The explicit potential restriction removes at most r^epsilon of the original mass. -/
theorem potentialGoodSet_compl_le_energy_cap (κ : SmoothKernel)
    (μ : Measure ℝ) [SFinite μ] {s r ε : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (he : smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε))) :
    μ (potentialGoodSet μ s r (ENNReal.ofReal (energyPotentialThreshold s r ε)))ᶜ ≤
      ENNReal.ofReal (r^ε) := by
  let L := ENNReal.ofReal (energyPotentialThreshold s r ε)
  have hLp := energyPotentialThreshold_pos s ε hr
  have hL0 : L ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hLp
  have hLtop : L ≠ ⊤ := ENNReal.ofReal_ne_top
  have hb := (potentialGoodSet_compl_mass μ s r L).trans
    (cappedEnergy_le_of_smoothEnergy_cap κ μ hs hr he)
  have heq : ENNReal.ofReal ((3:ℝ)^s*r^(-ε)) = L * ENNReal.ofReal (r^ε) := by
    rw [← ENNReal.ofReal_mul hLp.le]
    congr 1
    dsimp [energyPotentialThreshold]
    rw [mul_assoc, ← Real.rpow_add hr]
    congr 1
    ring
  rw [heq] at hb
  have hc := mul_le_mul_right hb L⁻¹
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hL0 hLtop, one_mul] using hc

/-- Every center and every radius R>=r has a uniform actual restricted-ball bound. -/
theorem potentialGoodSet_ball_le_energy_cap (μ : Measure ℝ) [SFinite μ]
    {s r ε R : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (hrR : r ≤ R) (z : ℝ) :
    (μ.restrict (potentialGoodSet μ s r (ENNReal.ofReal (energyPotentialThreshold s r ε))))
      (closedBall z R) ≤ ENNReal.ofReal ((6:ℝ)^s*r^(-2*ε)*R^s) := by
  have hR : 0 < R := hr.trans_le hrR
  have h := restricted_ball_mass_le_potential μ hs hR (by linarith : r ≤ 2*R)
    (ENNReal.ofReal (energyPotentialThreshold s r ε)) z
  have heq : ENNReal.ofReal ((2*R)^s) * ENNReal.ofReal (energyPotentialThreshold s r ε) =
      ENNReal.ofReal ((6:ℝ)^s*r^(-2*ε)*R^s) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2*R)^s)]
    congr 1
    dsimp [energyPotentialThreshold]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hR.le,
      show (6:ℝ) = 2*3 by norm_num,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 3)]
    ring
  exact h.trans_eq heq

/-- One genuine Borel set gives both the small mass loss and all-scale nonconcentration. -/
theorem exists_large_mass_nonconcentrated_restriction (κ : SmoothKernel)
    (μ : Measure ℝ) [SFinite μ] {s r ε : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (he : smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε))) :
    ∃ A : Set ℝ, MeasurableSet A ∧ μ Aᶜ ≤ ENNReal.ofReal (r^ε) ∧
      ∀ (z R : ℝ), r ≤ R →
        (μ.restrict A) (closedBall z R) ≤ ENNReal.ofReal ((6:ℝ)^s*r^(-2*ε)*R^s) := by
  refine ⟨potentialGoodSet μ s r (ENNReal.ofReal (energyPotentialThreshold s r ε)),
    measurableSet_potentialGoodSet μ _ _ _, potentialGoodSet_compl_le_energy_cap κ μ hs hr he,?_⟩
  intro z R hR
  exact potentialGoodSet_ball_le_energy_cap μ hs hr hR z

end Kakeya4.Hard.MultiplicativeConvolution
