import OAI.MeasureTheory.Falconer.KaufmanPowerBudget

/-! All constants precede both actual laws and growing Frostman/cap coefficients.
The Borel bad set controls every arbitrary large outer-mass set simultaneously. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem uniform_kaufman_robust_cover {σ p S : ℝ}
    (hσ : 0 < σ) (hσp : σ < p) (hpS : p < S) :
    ∃ e τ : ℝ, 0 < e ∧ 0 < τ ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ K C : ℝ, 1 ≤ K → K ≤ ((2:ℝ)^N)^e →
      1 ≤ C → C ≤ ((2:ℝ)^N)^e →
    ∀ ρ θ : Measure (Space 2), ∀ [IsProbabilityMeasure ρ] [SFinite θ],
      θ {w | ‖w‖ = 1}ᶜ = 0 → θ univ ≤ 1 →
      (∀ w : Space 2, ‖w‖ = 1 → ∀ a : ℝ, ((2:ℝ)^N)⁻¹ ≤ a → a ≤ 1 →
        θ (ball w a) ≤ ENNReal.ofReal (K*a^p)) →
      FrostmanBallBound ρ S C →
      (∀ᵐ z : Space 2 × Space 2 ∂(ρ.prod ρ), ‖z.1-z.2‖ ≤ 4) →
      ∃ B : Set (Space 2), MeasurableSet B ∧ θ B ≤ ENNReal.ofReal (((2:ℝ)^N)^(-τ)) ∧
        ∀ u ∉ B, ∀ G : Set (Space 2), ((2:ℝ)^N)^(-e) ≤ (ρ G).toReal →
          (Nat.ceil (((2:ℝ)^N)^σ) : ℕ∞) ≤
            externalCoveringNumber ⟨((2:ℝ)^N)⁻¹,by positivity⟩ ((fun x ↦ u 0*x 1-u 1*x 0) '' G) := by
  let e := (p-σ)/16
  have he : 0 < e := by dsimp [e]; positivity
  have hp : 0 < p := hσ.trans hσp
  obtain ⟨Nr,hNr⟩ := uniform_riesz_dyadic_coefficient_budget hpS he
  obtain ⟨Nc,hNc⟩ := Regularization.fixed_constant_absorbed he (2*(6:ℝ)^p)
  refine ⟨e,8*e,he,by positivity,max Nr Nc,?_⟩
  intro N hN K C hK hKb hC hCb ρ θ _ _ hsphere hmass hcap hfrost hdiam
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hr : 0 < 3/R := by positivity
  have hδr : R⁻¹ ≤ (3/R)/2 := by simp only [div_eq_mul_inv]; norm_num; linarith [inv_pos.mpr hR0]
  have har : 2*(R⁻¹) < 3/R := by rw [div_eq_mul_inv]; linarith [inv_pos.mpr hR0]
  obtain ⟨B,hB,hBad,hgood⟩ := finite_scale_kaufman_robust_outer_projection ρ θ hsphere hmass
    hK hp hpS hcap hfrost hdiam hr hδr (by positivity : 0 ≤ R^(-e))
    (by positivity : 0 < R^(-(σ+2*e))) ⟨R⁻¹,by positivity⟩ har
  refine ⟨B,hB,?_,?_⟩
  · have hRiesz : rieszSmallBallBound S C p ≤ ENNReal.ofReal (R^(2*e)) := by
      simpa only [two_mul] using hNr N ((le_max_left _ _).trans hN) e C hC hCb
    calc
      _ ≤ (ENNReal.ofReal (2*K*(2*(3/R))^p)*rieszSmallBallBound S C p)/ENNReal.ofReal (R^(-(σ+2*e))) := hBad
      _ ≤ (ENNReal.ofReal (2*K*(2*(3/R))^p)*ENNReal.ofReal (R^(2*e)))/ENNReal.ofReal (R^(-(σ+2*e))) := by gcongr
      _ = ENNReal.ofReal ((2*K*(2*(3/R))^p*R^(2*e))/(R^(-(σ+2*e)))) := by
        rw [← ENNReal.ofReal_mul (by have := zero_lt_one.trans_le hK; positivity),
          ← ENNReal.ofReal_div_of_pos (by positivity)]
      _ ≤ ENNReal.ofReal (R^(-8*e)) := ENNReal.ofReal_le_ofReal (kaufman_real_dyadic_budget hR he.le
        (by dsimp [e]; ring) (zero_le_one.trans hK) hKb (hNc N ((le_max_right _ _).trans hN)))
      _ = _ := by congr 1; congr 1; ring
  · intro u hu G hG
    simpa only [kaufman_cover_exponent_identity hR0] using hgood u hu G hG

#print axioms uniform_kaufman_robust_cover
end OAI.Falconer
