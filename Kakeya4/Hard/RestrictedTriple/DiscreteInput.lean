import Kakeya4.Hard.RestrictedTriple.IntervalTransport

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- Constants are paid before the arbitrary sets or the base scale are chosen. -/
theorem exists_constant_power_payment (C : ℝ) (hC : 0 ≤ C) {θ : ℝ} (hθ : 0 < θ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → C ≤ p^(-θ) := by
  let q := (C+1)^((-θ)⁻¹)
  have hq : 0 < q := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨min (1/2) q, lt_min (by norm_num) hq, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro p hp hpp
  have hpq : p ≤ q := hpp.trans (min_le_right _ _)
  have hpow : q^(-θ) = C+1 := Real.rpow_inv_rpow (by linarith) (by linarith)
  have hh := Real.rpow_le_rpow_of_nonpos hp hpq (show -θ ≤ 0 by linarith)
  rw [hpow] at hh
  linarith

/-- A fixed multiplicative cardinality loss is absorbed in an explicit exponent slack. -/
theorem absorb_cardinality_constant {p η θ C : ℝ} {q : ℝ≥0∞}
    (hp : 0 < p) (hC : C ≤ p^(-θ))
    (hlarge : ENNReal.ofReal (p^(η-3)) ≤ ENNReal.ofReal C*q) :
    ENNReal.ofReal (p^(η+θ-3)) ≤ q := by
  have hbound : ENNReal.ofReal (p^(η-3)) ≤ ENNReal.ofReal (p^(-θ))*q := by
    refine hlarge.trans ?_
    gcongr
  have heq : ENNReal.ofReal (p^(-θ))*ENNReal.ofReal (p^(η+θ-3)) =
      ENNReal.ofReal (p^(η-3)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hp _).le, ← Real.rpow_add hp]
    congr 2
    ring
  have hzero : ENNReal.ofReal (p^(-θ)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hp _))
  have hfinite : ENNReal.ofReal (p^(-θ)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hh : ENNReal.ofReal (p^(-θ))*ENNReal.ofReal (p^(η+θ-3)) ≤
      ENNReal.ofReal (p^(-θ))*q := by rwa [heq]
  exact (ENNReal.mul_le_mul_iff_right hzero hfinite).mp hh

/-- Actual separated finite marginals at the original p scale. All entropy losses
and the local interval enlargement are exposed to the eventual dichotomy adapter. -/
theorem exists_discrete_restricted_input {A B : Set Plane}
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare) {H : Set Triple}
    (hH : H ⊆ tripleCarrier A B) {p : ℝ} (hp : 0 < p) :
    ∃ PA PB : Set Plane, ∃ Q : Set Triple,
      PA ⊆ A ∧ PB ⊆ B ∧ PA.Finite ∧ PB.Finite ∧ Q.Finite ∧
      IsSeparated (Real.toNNReal p) (planeCoordinates '' PA) ∧
      IsSeparated (Real.toNNReal p) (planeCoordinates '' PB) ∧
      Q ⊆ tripleCarrier PA PB ∧ tripleCover p H ≤ 4096*(Q.encard : ℝ≥0∞) ∧
      (∀ C : ℝ, ADUpperBound p C A → ∀ z w, p ≤ w →
        ((PA ∩ ball z w).encard : ℝ≥0∞) ≤ ENNReal.ofReal (C*w/p)) ∧
      (∀ C : ℝ, ADUpperBound p C B → ∀ z w, p ≤ w →
        ((PB ∩ ball z w).encard : ℝ≥0∞) ≤ ENNReal.ofReal (C*w/p)) ∧
      (∀ s a b : ℝ, p ≤ s →
        intervalCover s (Icc a b ∩ dotDifferenceImage Q) ≤
          16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H)) := by
  obtain ⟨PA, PB, Q, hPA, hPB, hPAfin, hPBfin, hQfin, hPAsep, hPBsep,
    hQ, hlarge, _hforward, hbackward, _hglobal⟩ := exists_separated_marginal_dot_model hA hB hH hp
  have horig : tripleCover p H ≤ 4096*(Q.encard : ℝ≥0∞) := by
    refine (tripleCover_le_4096_mul_four_scale p hp.le H).trans ?_
    gcongr
  refine ⟨PA, PB, Q, hPA, hPB, hPAfin, hPBfin, hQfin, hPAsep, hPBsep,
    hQ, horig, ?_, ?_, ?_⟩
  · intro C hAD z w hw
    exact separated_local_count_of_ADUpperBound hp hAD hPA hPAsep z hw
  · intro C hAD z w hw
    exact separated_local_count_of_ADUpperBound hp hAD hPB hPBsep z hw
  · intro s a b hs
    exact intervalCover_local_le_sixteen_mul_of_approximation (hp.trans_le hs).le
      (by positivity) (by linarith) hbackward

end Kakeya4.Hard.RestrictedTriple
