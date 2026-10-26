import Kakeya4.Hard.MultiplicativeConvolution.PlanarProductLaw

/-!
# The genuine initial tube exponent for a planar product probability

Fubini in a coordinate with a large unit-normal coefficient gives the exponent
min(s,t), uniformly in the center, the normal and every positive width. This is
the initial bound for the later thin-tube bootstrap, not a bootstrap step.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- A closed slab described by its two real normal coordinates. -/
def planarSlab (a b c R : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | |a*z 0+b*z 1-c| ≤ R}

/-- The actual closed slab is Borel, so both orders of product integration apply. -/
theorem measurableSet_planarSlab (a b c R : ℝ) : MeasurableSet (planarSlab a b c R) :=
  measurableSet_le (by fun_prop) measurable_const

/-- A real affine slab section is contained in its literal coordinate ball. -/
theorem affine_slab_subset_closedBall (a d R : ℝ) (ha : a ≠ 0) :
    {x : ℝ | |a*x-d| ≤ R} ⊆ closedBall (d/a) (R/|a|) := by
  intro x hx
  have he : x-d/a = (a*x-d)/a := by field_simp
  rw [mem_closedBall, Real.dist_eq, he, abs_div]
  exact div_le_div_of_nonneg_right hx (abs_nonneg a)

/-- The first marginal controls all slab sections when the first normal coordinate is nonzero. -/
theorem planarProductLaw_slab_le_first (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C s a b c R : ℝ}
    (ha : a ≠ 0) (hR : 0 < R)
    (hμ : ∀ z W : ℝ, 0 < W → μ (closedBall z W) ≤ ENNReal.ofReal (C*W^s)) :
    planarProductLaw μ ν (planarSlab a b c R) ≤ ENNReal.ofReal (C*(R/|a|)^s) := by
  rw [planarProductLaw, Measure.map_apply continuous_pairToPlane.measurable
    (measurableSet_planarSlab a b c R),
    Measure.prod_apply_symm ((measurableSet_planarSlab a b c R).preimage continuous_pairToPlane.measurable)]
  calc
    _ ≤ ∫⁻ _ : ℝ, ENNReal.ofReal (C*(R/|a|)^s) ∂ν := by
      apply lintegral_mono
      intro y
      apply (measure_mono (show {x : ℝ | |a*x+b*y-c| ≤ R} ⊆
        closedBall ((c-b*y)/a) (R/|a|) from ?_)).trans
        (hμ _ _ (div_pos hR (abs_pos.mpr ha)))
      intro x hx
      apply affine_slab_subset_closedBall a (c-b*y) R ha
      simpa only [sub_sub_eq_add_sub] using hx
    _ = _ := by simp

/-- The second marginal controls all slab sections when the second normal coordinate is nonzero. -/
theorem planarProductLaw_slab_le_second (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C t a b c R : ℝ}
    (hb : b ≠ 0) (hR : 0 < R)
    (hν : ∀ z W : ℝ, 0 < W → ν (closedBall z W) ≤ ENNReal.ofReal (C*W^t)) :
    planarProductLaw μ ν (planarSlab a b c R) ≤ ENNReal.ofReal (C*(R/|b|)^t) := by
  rw [planarProductLaw, Measure.map_apply continuous_pairToPlane.measurable
    (measurableSet_planarSlab a b c R),
    Measure.prod_apply ((measurableSet_planarSlab a b c R).preimage continuous_pairToPlane.measurable)]
  calc
    _ ≤ ∫⁻ _ : ℝ, ENNReal.ofReal (C*(R/|b|)^t) ∂μ := by
      apply lintegral_mono
      intro x
      apply (measure_mono (show {y : ℝ | |a*x+b*y-c| ≤ R} ⊆
        closedBall ((c-a*x)/b) (R/|b|) from ?_)).trans
        (hν _ _ (div_pos hR (abs_pos.mpr hb)))
      intro y hy
      apply affine_slab_subset_closedBall b (c-a*x) R hb
      have he : b*y-(c-a*x) = a*x+b*y-c := by ring
      change |b*y-(c-a*x)| ≤ R
      rw [he]
      exact hy
    _ = _ := by simp

/-- A large normal coordinate pays at most two in the small-width power estimate. -/
theorem slab_width_power_le {a R q T : ℝ} (ha : (1/2 : ℝ) ≤ |a|)
    (hR : 0 < R) (hR1 : R ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hT : T ≤ q) :
    (R/|a|)^q ≤ 2*R^T := by
  have ha0 : 0 < |a| := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) ha
  have hw : R/|a| ≤ 2*R := (div_le_iff₀ ha0).2 (by nlinarith)
  have htwo : (2:ℝ)^q ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hq1
  calc
    _ ≤ (2*R)^q := Real.rpow_le_rpow (by positivity) hw hq
    _ = (2:ℝ)^q*R^q := Real.mul_rpow (by norm_num) hR.le
    _ ≤ 2*R^T := mul_le_mul htwo (Real.rpow_le_rpow_of_exponent_ge hR hR1 hT)
      (Real.rpow_nonneg hR.le _) (by norm_num)

/-- The product of actual Frostman probabilities has initial exponent min(s,t) in every unit-normal slab. -/
theorem planarProductLaw_unit_normal_slab_bound (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C s t : ℝ}
    (hC : 1 ≤ C) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hμ : ∀ z W : ℝ, 0 < W → μ (closedBall z W) ≤ ENNReal.ofReal (C*W^s))
    (hν : ∀ z W : ℝ, 0 < W → ν (closedBall z W) ≤ ENNReal.ofReal (C*W^t))
    (a b c : ℝ) (hnormal : a^2+b^2 = 1) {R : ℝ} (hR : 0 < R) :
    planarProductLaw μ ν (planarSlab a b c R) ≤ ENNReal.ofReal (2*C*R^(min s t)) := by
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  by_cases hR1 : R ≤ 1
  · have hlarge : (1/2 : ℝ) ≤ |a| ∨ (1/2 : ℝ) ≤ |b| := by
      by_contra hn
      push Not at hn
      have ha2 := (sq_lt_sq₀ (abs_nonneg a) (by norm_num : (0:ℝ) ≤ 1/2)).2 hn.1
      have hb2 := (sq_lt_sq₀ (abs_nonneg b) (by norm_num : (0:ℝ) ≤ 1/2)).2 hn.2
      simp only [sq_abs] at ha2 hb2
      nlinarith
    rcases hlarge with ha | hb
    · have ha0 : a ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) ha)
      apply (planarProductLaw_slab_le_first μ ν ha0 hR hμ).trans
      apply ENNReal.ofReal_le_ofReal
      have hp := mul_le_mul_of_nonneg_left
        (slab_width_power_le ha hR hR1 hs hs1 (min_le_left s t)) hC0
      nlinarith
    · have hb0 : b ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) hb)
      apply (planarProductLaw_slab_le_second μ ν hb0 hR hν).trans
      apply ENNReal.ofReal_le_ofReal
      have hp := mul_le_mul_of_nonneg_left
        (slab_width_power_le hb hR hR1 ht ht1 (min_le_right s t)) hC0
      nlinarith
  · have hpow : 1 ≤ R^(min s t) := Real.one_le_rpow (le_of_not_ge hR1) (le_min hs ht)
    apply prob_le_one.trans
    have hc' := one_le_mul_of_one_le_of_one_le hC hpow
    have hc : 1 ≤ 2*C*R^(min s t) := by nlinarith
    exact_mod_cast (ENNReal.ofReal_le_ofReal hc)

end Kakeya4.Hard.MultiplicativeConvolution
