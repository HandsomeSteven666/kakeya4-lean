import Kakeya4.Hard.MultilinearKakeya.AffineBisectionEnergy

/-! Joint continuity of the actual spatial derivative and directional energy in
polynomial coefficients, and invariance of that energy under antipodal coefficients. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology

namespace Kakeya4.Hard.MultilinearKakeya

theorem contDiff_coefficientSmoothPolynomial {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : E k × E n => smoothPolynomial (coefficientPolynomial B z.1) ε z.2) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun z : E k × E n =>
      MvPolynomial.eval (WithLp.ofLp z.2) (coefficientPolynomial B z.1)) := by
    simp only [eval_coefficientPolynomial]
    apply ContDiff.sum
    intro i _
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : E k × E n => z.1 i) :=
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin k => ℝ) i).contDiff.comp contDiff_fst
    have hb : ContDiff ℝ (⊤ : ℕ∞) (fun x : E n => MvPolynomial.eval (WithLp.ofLp x) (B i)) :=
      (AnalyticOnNhd.eval_continuousLinearMap
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap (B i)).contDiff
    exact hc.mul (hb.comp contDiff_snd)
  exact (hp.div_const ε).arctan

set_option maxHeartbeats 800000 in
theorem continuous_coefficient_spatial_fderiv {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ) :
    Continuous (fun z : E k × E n => fderiv ℝ (smoothPolynomial (coefficientPolynomial B z.1) ε) z.2) := by
  let F : E k × E n → ℝ := fun z => smoothPolynomial (coefficientPolynomial B z.1) ε z.2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_coefficientSmoothPolynomial B ε
  have he (u : E k) (x : E n) :
      fderiv ℝ (smoothPolynomial (coefficientPolynomial B u) ε) x =
        (fderiv ℝ F (u,x)).comp (ContinuousLinearMap.inr ℝ (E k) (E n)) := by
    have hg : HasFDerivAt (fun y : E n => (u,y))
        (ContinuousLinearMap.inr ℝ (E k) (E n)) x :=
      (hasFDerivAt_const u x).prodMk (hasFDerivAt_id x)
    exact (((hF.differentiable (by simp)) (u,x)).hasFDerivAt.comp x hg).fderiv
  have hd : Continuous (fun z : E k × E n =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inr ℝ (E k) (E n))) :=
    (hF.continuous_fderiv (by simp)).clm_comp continuous_const
  simpa only [he] using hd

theorem continuous_coefficient_spatial_direction {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ) :
    Continuous (fun z : (E k × E n) × E n =>
      fderiv ℝ (smoothPolynomial (coefficientPolynomial B z.1.1) ε) z.1.2 z.2) :=
  ((continuous_coefficient_spatial_fderiv B ε).comp continuous_fst).clm_apply continuous_snd

theorem continuous_coefficient_directionalEnergy {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ)
    {Q : Set (E n)} (hQ : IsCompact Q) :
    Continuous (fun z : E k × E n => directionalEnergy (coefficientPolynomial B z.1) ε Q z.2) := by
  apply continuous_parametric_integral_of_continuous (s := Q) _ hQ
  exact ((continuous_coefficient_spatial_direction B ε).comp
    ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd)).norm

theorem continuous_directionalEnergy_coefficients {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ)
    {Q : Set (E n)} (hQ : IsCompact Q) (v : E n) :
    Continuous (fun u : E k => directionalEnergy (coefficientPolynomial B u) ε Q v) := by
  apply continuous_parametric_integral_of_continuous (s := Q) _ hQ
  exact ((continuous_coefficient_spatial_fderiv B ε).clm_apply continuous_const).norm

theorem isOpen_coefficient_directionalEnergy_lt {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ)
    {Q : Set (E n)} (hQ : IsCompact Q) (v : E n) (a : ℝ) :
    IsOpen {u : E k | directionalEnergy (coefficientPolynomial B u) ε Q v < a} :=
  isOpen_lt (continuous_directionalEnergy_coefficients B ε hQ v) continuous_const

theorem isClosed_coefficient_directionalEnergy_le {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ)
    {Q : Set (E n)} (hQ : IsCompact Q) (v : E n) (a : ℝ) :
    IsClosed {u : E k | directionalEnergy (coefficientPolynomial B u) ε Q v ≤ a} :=
  isClosed_le (continuous_directionalEnergy_coefficients B ε hQ v) continuous_const

theorem smoothPolynomial_neg {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) :
    smoothPolynomial (-P) ε = -smoothPolynomial P ε := by
  funext x
  simp only [smoothPolynomial, MvPolynomial.eval_neg, neg_div, Real.arctan_neg, Pi.neg_apply]

theorem directionalEnergy_neg_polynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε : ℝ) (Q : Set (E n)) (v : E n) :
    directionalEnergy (-P) ε Q v = directionalEnergy P ε Q v := by
  simp only [directionalEnergy, smoothPolynomial_neg, fderiv_neg,
    neg_apply, norm_neg]

theorem directionalEnergy_neg_coefficients {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ) (Q : Set (E n)) (u : E k) (v : E n) :
    directionalEnergy (coefficientPolynomial B (-u)) ε Q v =
      directionalEnergy (coefficientPolynomial B u) ε Q v := by
  rw [coefficientPolynomial_neg, directionalEnergy_neg_polynomial]

end Kakeya4.Hard.MultilinearKakeya
