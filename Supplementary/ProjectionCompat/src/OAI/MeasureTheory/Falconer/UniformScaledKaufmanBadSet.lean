import OAI.MeasureTheory.Falconer.ScaledKaufmanBudget

/-! One uniform Borel collision bad set at a controlled enlarged scale. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem uniform_scaled_kaufman_collision_bad_set {σ p S : ℝ}
    (hσ : 0 < σ) (hσp : σ < p) (hpS : p < S) :
    ∃ e τ : ℝ, 0 < e ∧ 0 < τ ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ κ : ℝ, 0 ≤ κ → κ*p ≤ e →
    ∀ K C : ℝ, 1 ≤ K → K ≤ ((2:ℝ)^N)^e → 1 ≤ C → C ≤ ((2:ℝ)^N)^e →
    ∀ ρ θ : Measure (Space 2), ∀ [IsProbabilityMeasure ρ] [SFinite θ],
      θ {w | ‖w‖ = 1}ᶜ = 0 → θ univ ≤ 1 →
      (∀ w : Space 2, ‖w‖ = 1 → ∀ a : ℝ, ((2:ℝ)^N)⁻¹ ≤ a → a ≤ 1 →
        θ (ball w a) ≤ ENNReal.ofReal (K*a^p)) →
      FrostmanBallBound ρ S C →
      (∀ᵐ z : Space 2 × Space 2 ∂(ρ.prod ρ), ‖z.1-z.2‖ ≤ 4) →
      ∃ B : Set (Space 2), MeasurableSet B ∧ θ B ≤ ENNReal.ofReal (((2:ℝ)^N)^(-τ)) ∧
        ∀ u ∉ B, directionProjectionCollision ρ u (3*((2:ℝ)^N)^(κ-1)) <
          ENNReal.ofReal (((2:ℝ)^N)^(-(σ+2*e))) := by
  let e := (p-σ)/16
  have he : 0 < e := by dsimp [e]; positivity
  have hp : 0 < p := hσ.trans hσp
  obtain ⟨Nr,hNr⟩ := uniform_riesz_dyadic_coefficient_budget hpS he
  obtain ⟨Nc,hNc⟩ := Regularization.fixed_constant_absorbed he (2*(6:ℝ)^p)
  refine ⟨e,8*e,he,by positivity,max Nr Nc,?_⟩
  intro N hN κ hκ hκp K C hK hKb hC hCb ρ θ _ _ hsphere hmass hcap hfrost hdiam
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have ha : 0 < R^(κ-1) := by positivity
  have hδa : R⁻¹ ≤ R^(κ-1) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hδr : R⁻¹ ≤ (3*R^(κ-1))/2 := by linarith
  obtain ⟨B,hB,hBad,hgood⟩ := finite_scale_kaufman_Borel_bad_set ρ θ hsphere hmass
    hK hp hpS hcap hfrost hdiam (by positivity : 0 < 3*R^(κ-1)) hδr
    (ENNReal.ofReal (R^(-(σ+2*e))))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) ENNReal.ofReal_ne_top
  refine ⟨B,hB,?_,hgood⟩
  have hRiesz : rieszSmallBallBound S C p ≤ ENNReal.ofReal (R^(2*e)) := by
    simpa only [two_mul] using hNr N ((le_max_left _ _).trans hN) e C hC hCb
  calc
    _ ≤ (ENNReal.ofReal (2*K*(2*(3*R^(κ-1)))^p)*rieszSmallBallBound S C p)/ENNReal.ofReal (R^(-(σ+2*e))) := hBad
    _ ≤ (ENNReal.ofReal (2*K*(2*(3*R^(κ-1)))^p)*ENNReal.ofReal (R^(2*e)))/ENNReal.ofReal (R^(-(σ+2*e))) := by gcongr
    _ = ENNReal.ofReal ((2*K*(2*(3*R^(κ-1)))^p*R^(2*e))/(R^(-(σ+2*e)))) := by
      rw [← ENNReal.ofReal_mul (by have := zero_lt_one.trans_le hK; positivity),
        ← ENNReal.ofReal_div_of_pos (by positivity)]
    _ ≤ ENNReal.ofReal (R^(-8*e)) := ENNReal.ofReal_le_ofReal (kaufman_real_scaled_budget hR he.le
      (by dsimp [e]; ring) hκp (zero_le_one.trans hK) hKb (hNc N ((le_max_right _ _).trans hN)))
    _ = _ := by congr 1; congr 1; ring

#print axioms uniform_scaled_kaufman_collision_bad_set
end OAI.Falconer
