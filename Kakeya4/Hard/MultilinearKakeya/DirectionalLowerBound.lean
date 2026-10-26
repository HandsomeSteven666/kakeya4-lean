import Kakeya4.Hard.MultilinearKakeya.LocalEnergyBound
import Kakeya4.Hard.MultilinearKakeya.VisibilityBody

/-! A quantitative normalization lemma for the actual truncated unit body.
If one unit direction has p(v) <= 1, a transverse cylinder forces body volume
at least c_n D^(-(n-1)). Thus a smaller body forces every directional value > 1. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace Kakeya4.Hard.MultilinearKakeya

theorem axialCylinder_subset_visibilityBody_of_direction_le_one {n : ℕ}
    (p : Seminorm ℝ (E n)) {D : ℝ} (hD : 1 ≤ D) (hup : ∀ x, p x ≤ D * ‖x‖)
    (v : E n) (hv : ‖v‖ = 1) (hpv : p v ≤ 1) :
    Construction.axialCylinder v hv (-(1/2 : ℝ)) (1/2) ((2*D)⁻¹) ⊆ visibilityBody p := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hr : (2*D)⁻¹ ≤ (1/2 : ℝ) := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2*D)
  have hDr : D * (2*D)⁻¹ = (1/2 : ℝ) := by field_simp
  intro x hx
  let z := axialMeasurableEquiv v hv x
  change z.1 ∈ Icc (-(1/2 : ℝ)) (1/2) ∧ z.2 ∈ Metric.closedBall 0 ((2*D)⁻¹) at hx
  have ht : |z.1| ≤ (1/2 : ℝ) := abs_le.mpr hx.1
  have hw : ‖(z.2 : E n)‖ ≤ (2*D)⁻¹ := by
    change ‖z.2‖ ≤ (2*D)⁻¹
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2
  have hxrep : x = z.1 • v + (z.2 : E n) := by
    rw [← axialMeasurableEquiv_symm_apply v hv z]
    exact ((axialMeasurableEquiv v hv).symm_apply_apply x).symm
  rw [mem_visibilityBody, hxrep]
  constructor
  · calc
      _ ≤ ‖z.1 • v‖ + ‖(z.2 : E n)‖ := norm_add_le _ _
      _ = |z.1| + ‖(z.2 : E n)‖ := by rw [norm_smul, Real.norm_eq_abs, hv, mul_one]
      _ ≤ 1 := by linarith
  · calc
      _ ≤ p (z.1 • v) + p (z.2 : E n) := map_add_le_add p _ _
      _ = |z.1| * p v + p (z.2 : E n) := by rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ ≤ |z.1| * 1 + D * ‖(z.2 : E n)‖ := add_le_add
        (mul_le_mul_of_nonneg_left hpv (abs_nonneg _)) (hup _)
      _ ≤ (1/2 : ℝ) + D * (2*D)⁻¹ := add_le_add (by simpa using ht)
        (mul_le_mul_of_nonneg_left hw hDp.le)
      _ = 1 := by rw [hDr]; norm_num

theorem volume_visibilityBody_lower_of_direction_le_one {n : ℕ} (hn : 2 ≤ n)
    (p : Seminorm ℝ (E n)) {D : ℝ} (hD : 1 ≤ D) (hup : ∀ x, p x ≤ D * ‖x‖)
    (v : E n) (hv : ‖v‖ = 1) (hpv : p v ≤ 1) :
    ENNReal.ofReal ((2*D)⁻¹) ^ (n-1) * transverseUnitVolume n ≤ volume (visibilityBody p) := by
  have h : volume (Construction.axialCylinder v hv (-(1/2 : ℝ)) (1/2) ((2*D)⁻¹)) ≤
      volume (visibilityBody p) :=
    measure_mono (axialCylinder_subset_visibilityBody_of_direction_le_one p hD hup v hv hpv)
  rw [Construction.volume_axialCylinder] at h
  have hlen : (1/2 : ℝ) - -(1/2 : ℝ) = 1 := by ring
  rw [hlen, ENNReal.ofReal_one, one_mul] at h
  have heq := volume_transverse_closedBall hn (Line.mk 0 v hv) ((2*D)⁻¹)
  exact heq ▸ h

theorem one_lt_directional_of_small_visibilityBody {n : ℕ} (hn : 2 ≤ n)
    (p : Seminorm ℝ (E n)) {D : ℝ} (hD : 1 ≤ D) (hup : ∀ x, p x ≤ D * ‖x‖)
    (hsmall : volume (visibilityBody p) <
      ENNReal.ofReal ((2*D)⁻¹) ^ (n-1) * transverseUnitVolume n) :
    ∀ v : E n, ‖v‖ = 1 → 1 < p v := by
  intro v hv
  by_contra! hpv
  exact (not_le_of_gt hsmall) (volume_visibilityBody_lower_of_direction_le_one hn p hD hup v hv hpv)

theorem one_lt_smoothDirectionalEnergy_of_small_body {n : ℕ} (hn : 2 ≤ n)
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0)
    {Q : Set (E n)} (hQ : IsCompact Q) {c : E n} {R : ℝ} (hQR : Q ⊆ Metric.closedBall c R)
    (hsmall : volume (visibilityBody (smoothDirectionalSeminorm P ε Q hQ)) <
      ENNReal.ofReal ((2 * max 1 (localDegreeBudget n R P.totalDegree).toReal)⁻¹) ^ (n-1) *
        transverseUnitVolume n) :
    ∀ v : E n, ‖v‖ = 1 → 1 < directionalEnergy P ε Q v := by
  apply one_lt_directional_of_small_visibilityBody hn (smoothDirectionalSeminorm P ε Q hQ)
    (le_max_left _ _) ?_ hsmall
  intro x
  exact (directionalEnergy_le_degree_mul_norm hn P hε hQ hQR x).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))

end Kakeya4.Hard.MultilinearKakeya
