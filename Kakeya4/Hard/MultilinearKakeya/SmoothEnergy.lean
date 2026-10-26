import Kakeya4.Hard.MultilinearKakeya.Basic

/-! Actual smooth polynomial directional energy on a compact spatial region.
No cylinder-budget or polynomial-visibility theorem is assumed here. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology NNReal

namespace Kakeya4.Hard.MultilinearKakeya

def smoothPolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) (x : E n) : ℝ :=
  Real.arctan (MvPolynomial.eval (WithLp.ofLp x) P / ε)

theorem contDiff_smoothPolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPolynomial P ε) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun x : E n => MvPolynomial.eval (WithLp.ofLp x) P) :=
    (AnalyticOnNhd.eval_continuousLinearMap
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap P).contDiff
  exact (hp.div_const ε).arctan

theorem continuous_fderiv_smoothPolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) :
    Continuous (fderiv ℝ (smoothPolynomial P ε)) :=
  (contDiff_smoothPolynomial P ε).continuous_fderiv (by simp)

def directionalEnergy {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ)
    (Q : Set (E n)) (v : E n) : ℝ := ∫ x in Q, ‖fderiv ℝ (smoothPolynomial P ε) x v‖

theorem integrableOn_smoothPolynomial_direction {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q) (v : E n) :
    IntegrableOn (fun x => ‖fderiv ℝ (smoothPolynomial P ε) x v‖) Q :=
  ContinuousOn.integrableOn_compact hQ
    (((continuous_fderiv_smoothPolynomial P ε).clm_apply continuous_const).norm.continuousOn)

theorem directionalEnergy_nonneg {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ)
    (Q : Set (E n)) (v : E n) : 0 ≤ directionalEnergy P ε Q v :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem directionalEnergy_smul {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ)
    (Q : Set (E n)) (a : ℝ) (v : E n) :
    directionalEnergy P ε Q (a • v) = ‖a‖ * directionalEnergy P ε Q v := by
  simp only [directionalEnergy, map_smul, norm_smul]
  exact integral_const_mul _ _

theorem directionalEnergy_add_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ)
    {Q : Set (E n)} (hQ : IsCompact Q) (v w : E n) :
    directionalEnergy P ε Q (v+w) ≤ directionalEnergy P ε Q v + directionalEnergy P ε Q w := by
  unfold directionalEnergy
  rw [← integral_add (integrableOn_smoothPolynomial_direction P ε hQ v)
    (integrableOn_smoothPolynomial_direction P ε hQ w)]
  apply integral_mono (integrableOn_smoothPolynomial_direction P ε hQ (v+w))
    ((integrableOn_smoothPolynomial_direction P ε hQ v).add
      (integrableOn_smoothPolynomial_direction P ε hQ w))
  intro x
  change ‖fderiv ℝ (smoothPolynomial P ε) x (v+w)‖ ≤
    ‖fderiv ℝ (smoothPolynomial P ε) x v‖ + ‖fderiv ℝ (smoothPolynomial P ε) x w‖
  rw [map_add]
  exact norm_add_le _ _

def smoothDirectionalSeminorm {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ)
    (Q : Set (E n)) (hQ : IsCompact Q) : Seminorm ℝ (E n) :=
  Seminorm.of (directionalEnergy P ε Q) (directionalEnergy_add_le P ε hQ)
    (directionalEnergy_smul P ε Q)

theorem smoothDirectionalSeminorm_apply {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ)
    (Q : Set (E n)) (hQ : IsCompact Q) (v : E n) :
    smoothDirectionalSeminorm P ε Q hQ v = directionalEnergy P ε Q v := rfl

theorem directionalEnergy_le_gradient_integral {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q) (v : E n) :
    directionalEnergy P ε Q v ≤ (∫ x in Q, ‖fderiv ℝ (smoothPolynomial P ε) x‖) * ‖v‖ := by
  unfold directionalEnergy
  rw [← integral_mul_const]
  apply integral_mono (integrableOn_smoothPolynomial_direction P ε hQ v)
    ((ContinuousOn.integrableOn_compact hQ
      (continuous_fderiv_smoothPolynomial P ε).norm.continuousOn).mul_const ‖v‖)
  intro x
  exact (fderiv ℝ (smoothPolynomial P ε) x).le_opNorm v

theorem continuous_smoothDirectionalSeminorm {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q) :
    Continuous (smoothDirectionalSeminorm P ε Q hQ) := by
  let C : ℝ≥0 := ⟨∫ x in Q, ‖fderiv ℝ (smoothPolynomial P ε) x‖,
    integral_nonneg (fun _ => norm_nonneg _)⟩
  apply Seminorm.continuous_of_le (q := C • normSeminorm ℝ (E n))
  · change Continuous (fun v : E n => (C : ℝ) * ‖v‖)
    exact continuous_const.mul continuous_norm
  · intro v
    exact directionalEnergy_le_gradient_integral P ε hQ v

theorem hasDerivAt_smoothPolynomial_line {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε : ℝ) (a v : E n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => smoothPolynomial P ε (a + s • v))
      (fderiv ℝ (smoothPolynomial P ε) (a + t • v) v) t := by
  have hp := (contDiff_smoothPolynomial P ε).differentiable (by simp)
  have hl : HasDerivAt (fun s : ℝ => a + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add a
  exact (hp (a + t • v)).hasFDerivAt.comp_hasDerivAt t hl

end Kakeya4.Hard.MultilinearKakeya
