import Kakeya4.Hard.MultilinearKakeya.CylinderBudget

/-! Uniform local directional bounds from the actual whole-tube budget.
The constant depends on degree and the spatial radius, not coefficients or epsilon. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

def localDegreeBudget (n : ℕ) (R : ℝ) (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal R ^ (n-1) * transverseUnitVolume n * ENNReal.ofReal (d * Real.pi)

theorem localDegreeBudget_ne_top (n : ℕ) (R : ℝ) (d : ℕ) :
    localDegreeBudget n R d ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (transverseUnitVolume_ne_top n)
  · exact ENNReal.ofReal_ne_top

theorem closedBall_subset_origin_tube {n : ℕ} (v : E n) (hv : ‖v‖ = 1) (R : ℝ) :
    Metric.closedBall 0 R ⊆ (Line.mk 0 v hv).tube R := by
  intro x hx
  have hzero : (0 : E n) ∈ (Line.mk 0 v hv).carrier := ⟨0, by simp⟩
  exact (Metric.infDist_le_dist_of_mem hzero).trans hx

theorem closedBall_subset_centered_tube {n : ℕ} (c v : E n) (hv : ‖v‖ = 1) (R : ℝ) :
    Metric.closedBall c R ⊆ (Line.mk c v hv).tube R := by
  intro x hx
  have hc : c ∈ (Line.mk c v hv).carrier := ⟨0, by simp⟩
  exact (Metric.infDist_le_dist_of_mem hc).trans hx

theorem directionalEnergy_unit_le_degree {n : ℕ} (hn : 2 ≤ n)
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0)
    {Q : Set (E n)} (hQ : IsCompact Q) {c : E n} {R : ℝ} (hQR : Q ⊆ Metric.closedBall c R)
    (v : E n) (hv : ‖v‖ = 1) :
    directionalEnergy P ε Q v ≤ (localDegreeBudget n R P.totalDegree).toReal := by
  have heq : ENNReal.ofReal (directionalEnergy P ε Q v) =
      ∫⁻ x in Q, ENNReal.ofReal ‖fderiv ℝ (smoothPolynomial P ε) x v‖ :=
    ofReal_integral_eq_lintegral_ofReal (integrableOn_smoothPolynomial_direction P ε hQ v)
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  have hle : ENNReal.ofReal (directionalEnergy P ε Q v) ≤
      localDegreeBudget n R P.totalDegree := by
    rw [heq]
    apply (lintegral_mono_set (hQR.trans (closedBall_subset_centered_tube c v hv R))).trans
    exact lintegral_smoothPolynomial_tube_le_degree hn (Line.mk c v hv) P hε R
  have h := ENNReal.toReal_mono (localDegreeBudget_ne_top n R P.totalDegree) hle
  simpa only [ENNReal.toReal_ofReal (directionalEnergy_nonneg P ε Q v)] using h

theorem directionalEnergy_le_degree_mul_norm {n : ℕ} (hn : 2 ≤ n)
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0)
    {Q : Set (E n)} (hQ : IsCompact Q) {c : E n} {R : ℝ} (hQR : Q ⊆ Metric.closedBall c R)
    (v : E n) :
    directionalEnergy P ε Q v ≤ (localDegreeBudget n R P.totalDegree).toReal * ‖v‖ := by
  by_cases hz : v = 0
  · subst v
    simp [directionalEnergy]
  · let u := ‖v‖⁻¹ • v
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hz
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le),
        inv_mul_cancel₀ hvpos.ne']
    have hv : v = ‖v‖ • u := by simp [u, smul_smul, hvpos.ne']
    calc
      _ = ‖v‖ * directionalEnergy P ε Q u := by
        conv_lhs => rw [hv, directionalEnergy_smul]
        rw [Real.norm_of_nonneg hvpos.le]
      _ ≤ ‖v‖ * (localDegreeBudget n R P.totalDegree).toReal :=
        mul_le_mul_of_nonneg_left (directionalEnergy_unit_le_degree hn P hε hQ hQR u hu) hvpos.le
      _ = _ := mul_comm _ _

end Kakeya4.Hard.MultilinearKakeya
