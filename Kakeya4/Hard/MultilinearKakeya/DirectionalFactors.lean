import Kakeya4.Hard.MultilinearKakeya.FinalNormalization

/-! Actual normalized directional-energy factors. The same amplification t^n
in the volume bound cancels exactly against the n directional factors p(v)/t. -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

def directionalFactor {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε t : ℝ) (Q : Set (E n)) (v : E n) : ℝ :=
  directionalEnergy P ε Q v/t

theorem directionalFactor_nonneg {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (Q : Set (E n)) (v : E n) : 0 ≤ directionalFactor P ε t Q v :=
  div_nonneg (directionalEnergy_nonneg P ε Q v) ht

def directionalDeterminantConstant (n : ℕ) : ℝ := ((2 : ℝ)/(n : ℝ))^n/(2*Real.sqrt n)^n

theorem directionalDeterminantConstant_pos {n : ℕ} (hn : 0 < n) : 0 < directionalDeterminantConstant n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (pow_pos (div_pos (by norm_num) hnR) n) (pow_pos (by positivity) n)

theorem weighted_determinant_le_normalized_directional_product {n : ℕ} (hn : 0 < n)
    (p : Seminorm ℝ (E n)) (hp : Continuous p) (v : Fin n → E n)
    (hv : ∀ i, ‖v i‖ = 1) (hlower : ∀ i, 1 ≤ p (v i))
    {t w : ℝ} (ht : 0 < t) (hw : 0 < w)
    (hsmall : (volume (visibilityBody p)).toReal ≤ (2*Real.sqrt n)^n/(t^n*w)) :
    directionalDeterminantConstant n*w*|Matrix.det (fun i j => v j i)| ≤ ∏ i, p (v i)/t := by
  have hprod : 0 ≤ ∏ i, p (v i) := Finset.prod_nonneg (fun i _ => apply_nonneg p _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : 0 < (2*Real.sqrt n)^n := pow_pos (by positivity) n
  have hfinite := (volume_visibilityBody_lt_top p hp).ne
  have hd := ENNReal.toReal_mono (ENNReal.mul_ne_top hfinite ENNReal.ofReal_ne_top)
    (determinant_visibilityBody_le_of_lower_bound hn p hp v hv hlower)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hprod,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ((2 : ℝ)/(n : ℝ))^n*|Matrix.det (fun i j => v j i)|)] at hd
  have hK := (le_div_iff₀ (mul_pos (pow_pos ht _) hw)).mp hsmall
  have h1 := mul_le_mul_of_nonneg_right hd (mul_pos (pow_pos ht n) hw).le
  have h2 := mul_le_mul_of_nonneg_right hK hprod
  rw [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply (le_div_iff₀ (pow_pos ht n)).mpr
  unfold directionalDeterminantConstant
  have hf : ((2 : ℝ)/(n : ℝ))^n*|Matrix.det (fun i j => v j i)| *(t^n*w) ≤
      (2*Real.sqrt n)^n * ∏ i, p (v i) := h1.trans (by nlinarith [h2])
  calc
    _ = (((2 : ℝ)/(n : ℝ))^n*|Matrix.det (fun i j => v j i)| *(t^n*w))/(2*Real.sqrt n)^n := by ring
    _ ≤ _ := (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hf)

theorem exists_weighted_directional_factor_polynomial {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (w : κ → ℝ) (hw : ∀ q, 1 ≤ w q) :
    ∃ t : ℝ, 1 ≤ t ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      (P.totalDegree : ℝ) ≤ t*weightedVisibilityDegreeBound n w ∧
      (∀ q, ∀ v : E n, ‖v‖ = 1 → 1 < directionalEnergy P ε (Metric.closedBall (b q) 1) v) ∧
      (∀ q, ∀ v : Fin n → E n, (∀ i, ‖v i‖ = 1) →
        directionalDeterminantConstant n*w q*|Matrix.det (fun i j => v j i)| ≤
          ∏ i, directionalFactor P ε t (Metric.closedBall (b q) 1) (v i)) := by
  obtain ⟨t,ht,ε,hε,P,hP,hD,hV,hdir⟩ := exists_direction_normalized_weighted_polynomial hn b w hw
  refine ⟨t,ht,ε,hε,P,hP,hD,hdir,fun q v hv => ?_⟩
  have he := weighted_determinant_le_normalized_directional_product (by omega : 0 < n)
    (smoothDirectionalSeminorm P ε (Metric.closedBall (b q) 1) (isCompact_closedBall (b q) 1))
    (continuous_smoothDirectionalSeminorm P ε (isCompact_closedBall (b q) 1)) v hv
    (fun i => (hdir q (v i) (hv i)).le) (by linarith : 0 < t)
    (lt_of_lt_of_le zero_lt_one (hw q)) (hV q).le
  exact he

end Kakeya4.Hard.MultilinearKakeya
