import OAI.MeasureTheory.Falconer.CrossedParameterLaw

/-! The original four-coordinate, nonunit, two-plus-sign OSS projection
for dyadic scales, with open-ball Frostman assumptions and arbitrary G. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem real_closed_ball_bound_of_open {μ : Measure ℝ} {a C : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ z r : ℝ, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (C*r^a)) :
    ∀ z r : ℝ, 0 < r → μ (closedBall z r) ≤ ENNReal.ofReal ((2*C)*r^a) := by
  intro z r hr
  apply (measure_mono (closedBall_subset_ball (by linarith : r < 2*r))).trans
  apply (hb z (2*r) (by positivity)).trans
  apply ENNReal.ofReal_le_ofReal
  rw [Real.mul_rpow (by norm_num) hr.le]
  have hh : (2:ℝ)^a ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ha1
  nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg hC (Real.rpow_nonneg hr.le a))]

theorem unit_cube_product_diameter (ρ : Measure (Space 2)) [SFinite ρ]
    (hcube : ∀ᵐ x ∂ρ, ∀ i : Fin 2, |x i| ≤ 1) :
    ∀ᵐ z : Space 2 × Space 2 ∂(ρ.prod ρ), ‖z.1-z.2‖ ≤ 4 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [hcube] with x hx
  filter_upwards [hcube] with y hy
  have h0 := (abs_sub (x 0) (y 0)).trans (add_le_add (hx 0) (hy 0))
  have h1 := (abs_sub (x 1) (y 1)).trans (add_le_add (hx 1) (hy 1))
  have hd := planar_dist_le_coordinate_sum x y
  rw [dist_eq_norm] at hd
  linarith

theorem dyadic_OSS_Frostman_projection {s t σ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 ≤ σ) (hσmax : σ < min (s+t) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ C : ℝ, 1 ≤ C → C ≤ ((2:ℝ)^N)^ε →
    ∀ μ : Fin 4 → Measure ℝ, ∀ [∀ i, IsProbabilityMeasure (μ i)],
      (∀ i, UnitSupported (μ i)) →
      (∀ (i : Fin 4) (z r : ℝ), 0 < r →
        μ i (ball z r) ≤ ENNReal.ofReal (C*r^(if i.val < 2 then s else t))) →
    ∀ ρ : Measure (Space 2), ∀ [IsProbabilityMeasure ρ], FrostmanBallBound ρ (s+t) C →
      (∀ᵐ x ∂ρ, ∀ i : Fin 2, |x i| ≤ 1) →
      ∃ Bad : Set (Fin 4 → ℝ), MeasurableSet Bad ∧
        Measure.pi μ Bad ≤ ENNReal.ofReal (((2:ℝ)^N)^(-ε)) ∧
        ∀ w ∉ Bad, ∀ G : Set (Space 2), ENNReal.ofReal (((2:ℝ)^N)^(-ε)) ≤ ρ G →
          (Nat.ceil (((2:ℝ)^N)^σ) : ℕ∞) ≤ externalCoveringNumber
            ⟨((2:ℝ)^N)⁻¹,by positivity⟩
            ((fun x ↦ (w 2-w 3)*x 0+(w 0-w 1)*x 1) '' G) := by
  classical
  let σ' := (σ+min (s+t) 1)/2
  have hσσ' : σ < σ' := by dsimp [σ']; linarith
  have hσ' : 0 < σ' := hσ.trans_lt hσσ'
  have hσ'max : σ' < min (s+t) 1 := by dsimp [σ']; linarith
  obtain ⟨ep,τ,θ,hep,hτ,hθ,Np,hNp⟩ := Regularization.uniform_product_parameter_nonunit_projection hs hs1 ht ht1 hσ' hσ'max
  let d := min ep τ
  let ε := d/2
  have hd : 0 < d := lt_min hep hτ
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεp : 2*ε ≤ ep := by dsimp [ε,d]; linarith [min_le_left ep τ]
  have hετ : ε ≤ τ := by dsimp [ε,d]; linarith [min_le_right ep τ]
  have hεep : ε ≤ ep := by linarith
  obtain ⟨Nc,hNc⟩ := Regularization.fixed_constant_absorbed hε 2
  refine ⟨ε,hε,max Np Nc,?_⟩
  intro N hN C hC hCb μ _ hμ hb ρ _ hρ hcube
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hbudget : 2*C ≤ R^ep := calc
    _ ≤ R^ε*R^ε := mul_le_mul (hNc N ((le_max_right _ _).trans hN)) hCb hC0 (by positivity)
    _ = R^(2*ε) := by rw [← Real.rpow_add hR0]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR hεp
  have hclosed (i : Fin 4) : ∀ z r : ℝ, 0 < r → μ i (closedBall z r) ≤
      ENNReal.ofReal ((2*C)*r^(if i.val < 2 then s else t)) := by
    apply real_closed_ball_bound_of_open (hC := hC0) (hb := hb i)
    · split_ifs <;> linarith
    · split_ifs <;> assumption
  have hρ' : FrostmanBallBound ρ (s+t) (2*C) := by
    intro x r hr
    exact (hρ x r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ 2*C) (Real.rpow_nonneg hr.le _)))
  obtain ⟨B,hB,hBad,hgood⟩ := hNp N ((le_max_left _ _).trans hN) (2*C) (by linarith) hbudget
    (μ 0) (μ 1) (μ 3) (μ 2) (hμ 0) (hμ 1) (hμ 3) (hμ 2)
    (by simpa using hclosed 0) (by simpa using hclosed 1)
    (by simpa using hclosed 3) (by simpa using hclosed 2) ρ hρ' (unit_cube_product_diameter ρ hcube)
  let Bad := crossedParameterMap ⁻¹' B
  refine ⟨Bad,hB.preimage crossed_parameter_map_measurable,?_,?_⟩
  · have hm : Measure.pi μ Bad ≤ ENNReal.ofReal (R^(-τ)) := by
      change ((planarProductLaw (μ 0) (μ 3)).prod (planarProductLaw (μ 1) (μ 2))) B ≤ _ at hBad
      rw [← original_pi_four_parameter_law μ,Measure.map_apply crossed_parameter_map_measurable hB] at hBad
      exact hBad
    exact hm.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg hετ)))
  · intro w hw G hG
    have hm : R^(-ep) ≤ (ρ G).toReal := by
      have hh := ENNReal.toReal_mono (measure_ne_top ρ G) hG
      rw [ENNReal.toReal_ofReal (by positivity)] at hh
      exact (Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg hεep)).trans hh
    have hproj := (hgood (crossedParameterMap w) hw).2 G hm
    have hn : Nat.ceil (R^σ) ≤ Nat.ceil (R^σ') :=
      Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hR hσσ'.le)
    apply (show (Nat.ceil (R^σ) : ℕ∞) ≤ Nat.ceil (R^σ') by exact_mod_cast hn).trans
    simpa only [crossed_OSS_projection_identity] using hproj

#print axioms real_closed_ball_bound_of_open
#print axioms unit_cube_product_diameter
#print axioms dyadic_OSS_Frostman_projection
end OAI.Falconer
