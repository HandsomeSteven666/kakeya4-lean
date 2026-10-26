import Kakeya4.Hard.MultilinearKakeya.VisibilityAmplification
import Kakeya4.Hard.MultilinearKakeya.DirectionalLowerBound

/-! Construction of the actual final polynomial with every unit-direction
energy strictly above one on all prescribed unit balls. One amplification scale
is chosen before the polynomial and the common smoothing parameter. -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

def unitDegreeCoefficient (n : ℕ) : ℝ := (transverseUnitVolume n).toReal * Real.pi

theorem unitDegreeCoefficient_pos (n : ℕ) : 0 < unitDegreeCoefficient n :=
  mul_pos (ENNReal.toReal_pos (transverseUnitVolume_pos n).ne' (transverseUnitVolume_ne_top n)) Real.pi_pos

theorem unit_localDegreeBudget_toReal (n d : ℕ) :
    (localDegreeBudget n 1 d).toReal = unitDegreeCoefficient n * (d : ℝ) := by
  simp only [localDegreeBudget,ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ d*Real.pi),unitDegreeCoefficient]
  ring

theorem one_lt_directional_of_small_real_body {n : ℕ} (hn : 2 ≤ n)
    (p : Seminorm ℝ (E n)) (hp : Continuous p) {D : ℝ} (hD : 1 ≤ D)
    (hup : ∀ x, p x ≤ D*‖x‖)
    (hsmall : (volume (visibilityBody p)).toReal < (2*D)⁻¹^(n-1)*(transverseUnitVolume n).toReal) :
    ∀ v : E n, ‖v‖ = 1 → 1 < p v := by
  intro v hv
  by_contra! hle
  have h := ENNReal.toReal_mono (volume_visibilityBody_lt_top p hp).ne
    (volume_visibilityBody_lower_of_direction_le_one hn p hD hup v hv hle)
  have hi : 0 ≤ (2*D)⁻¹ := inv_nonneg.mpr (by linarith)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hi] at h
  exact (not_lt_of_ge h) hsmall

theorem exists_directional_normalization_scale {n : ℕ} (hn : 0 < n)
    {A B C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ t : ℝ, 1 ≤ t ∧ B/t^n < (2*(t*A))⁻¹^(n-1)*C := by
  let t := max 1 (B*(2*A)^(n-1)/C+1)
  have ht : 1 ≤ t := le_max_left _ _
  have hlarge : B*(2*A)^(n-1)/C < t := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have hpay : B*(2*A)^(n-1) < C*t := by
    simpa only [mul_comm] using (div_lt_iff₀ hC).mp hlarge
  exact ⟨t,ht,div_pow_lt_inverse_power_of_payment hn (by linarith) hA hpay⟩

theorem exists_direction_normalized_weighted_polynomial {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (w : κ → ℝ) (hw : ∀ q, 1 ≤ w q) :
    ∃ t : ℝ, 1 ≤ t ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      (P.totalDegree : ℝ) ≤ t*weightedVisibilityDegreeBound n w ∧
      (∀ q, (volume (visibilityBody (smoothDirectionalSeminorm P ε (Metric.closedBall (b q) 1)
        (isCompact_closedBall (b q) 1)))).toReal < (2*Real.sqrt n)^n/(t^n*w q)) ∧
      (∀ q, ∀ v : E n, ‖v‖ = 1 →
        1 < directionalEnergy P ε (Metric.closedBall (b q) 1) v) := by
  let A := max 1 (unitDegreeCoefficient n * weightedVisibilityDegreeBound n w)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 < (transverseUnitVolume n).toReal :=
    ENNReal.toReal_pos (transverseUnitVolume_pos n).ne' (transverseUnitVolume_ne_top n)
  obtain ⟨t,ht,hscale⟩ := exists_directional_normalization_scale (by omega : 0 < n) hA hC
    (B := (2*Real.sqrt n)^n)
  obtain ⟨ε,hε,P,hP,hD,hV⟩ := exists_amplified_weighted_small_visibilityBody hn b w hw ht
  refine ⟨t,ht,ε,hε,P,hP,hD,hV,?_⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have htp : 0 ≤ t := htpos.le
  have hAD : (localDegreeBudget n 1 P.totalDegree).toReal ≤ t*A := by
    rw [unit_localDegreeBudget_toReal]
    calc
      _ ≤ unitDegreeCoefficient n * (t*weightedVisibilityDegreeBound n w) :=
        mul_le_mul_of_nonneg_left hD (unitDegreeCoefficient_pos n).le
      _ = t*(unitDegreeCoefficient n*weightedVisibilityDegreeBound n w) := by ring
      _ ≤ t*A := mul_le_mul_of_nonneg_left (le_max_right _ _) htp
  have htA : 1 ≤ t*A := le_trans ht (le_mul_of_one_le_right htp (le_max_left _ _))
  intro q
  apply one_lt_directional_of_small_real_body hn
    (smoothDirectionalSeminorm P ε (Metric.closedBall (b q) 1) (isCompact_closedBall (b q) 1))
    (continuous_smoothDirectionalSeminorm P ε (isCompact_closedBall (b q) 1)) htA
  · intro x
    exact (directionalEnergy_le_degree_mul_norm hn P hε.ne' (isCompact_closedBall (b q) 1)
      (Subset.refl _) x).trans (mul_le_mul_of_nonneg_right hAD (norm_nonneg x))
  · calc
      _ < (2*Real.sqrt n)^n/(t^n*w q) := hV q
      _ ≤ (2*Real.sqrt n)^n/t^n := div_le_div_of_nonneg_left (by positivity) (pow_pos htpos _)
        (le_mul_of_one_le_right (pow_nonneg htp _) (hw q))
      _ < _ := hscale

end Kakeya4.Hard.MultilinearKakeya
