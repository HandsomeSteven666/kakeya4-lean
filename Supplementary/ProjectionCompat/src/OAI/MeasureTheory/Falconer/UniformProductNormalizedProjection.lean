import OAI.MeasureTheory.Falconer.UniformRetainedProjectionConsumer

/-! Genuine four-marginal parameter products, all losses paid, arbitrary rho.
The projection is still by the normalized difference direction; its original
length and OSS sign convention must be restored in a later consumer. -/

set_option autoImplicit false
namespace OAI.Falconer.Regularization
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem uniform_product_parameter_normalized_projection
    {s t σ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 < σ) (hσmax : σ < min (s+t) 1) :
    ∃ ε τ θ : ℝ, 0 < ε ∧ 0 < τ ∧ 0 < θ ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ C : ℝ, 1 ≤ C → C ≤ ((2:ℝ)^N)^ε →
    ∀ μ₁ μ₂ ν₁ ν₂ : Measure ℝ,
      ∀ [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂],
      UnitSupported μ₁ → UnitSupported μ₂ → UnitSupported ν₁ → UnitSupported ν₂ →
      (∀ z r : ℝ, 0 < r → μ₁ (closedBall z r) ≤ ENNReal.ofReal (C*r^s)) →
      (∀ z r : ℝ, 0 < r → μ₂ (closedBall z r) ≤ ENNReal.ofReal (C*r^s)) →
      (∀ z r : ℝ, 0 < r → ν₁ (closedBall z r) ≤ ENNReal.ofReal (C*r^t)) →
      (∀ z r : ℝ, 0 < r → ν₂ (closedBall z r) ≤ ENNReal.ofReal (C*r^t)) →
    ∀ ρ : Measure (Space 2), ∀ [IsProbabilityMeasure ρ], FrostmanBallBound ρ (s+t) C →
      (∀ᵐ z : Space 2 × Space 2 ∂(ρ.prod ρ), ‖z.1-z.2‖ ≤ 4) →
      ∃ Bad : Set (Space 2 × Space 2), MeasurableSet Bad ∧
        ((parameterProductProbability μ₁ ν₁ : Measure (Space 2)).prod
          (parameterProductProbability μ₂ ν₂)) Bad ≤ ENNReal.ofReal (((2:ℝ)^N)^(-τ)) ∧
        ∀ z ∉ Bad, ((2:ℝ)^N)^(-θ) ≤ dist z.1 z.2 ∧
          ∀ G : Set (Space 2), ((2:ℝ)^N)^(-ε) ≤ (ρ G).toReal →
            (Nat.ceil (((2:ℝ)^N)^σ) : ℕ∞) ≤ externalCoveringNumber
              ⟨((2:ℝ)^N)⁻¹,by positivity⟩
              ((fun x ↦ (radialDirection z.1 z.2) 0*x 1-(radialDirection z.1 z.2) 1*x 0) '' G) := by
  classical
  let p := (σ+min (s+t) 1)/2
  have hσp : σ < p := by dsimp [p]; linarith
  have hpmax : p < min (s+t) 1 := by dsimp [p]; linarith
  have hp : 0 < p := hσ.trans hσp
  have hpS : p < s+t := hpmax.trans_le (min_le_left _ _)
  obtain ⟨e,τr,he,hτr,Nr,hNr⟩ := uniform_retained_pair_robust_projection hσ hσp hpS
  obtain ⟨ep,τp,hep,hτp,Np,hNp⟩ := uniform_parameter_product_bootstrap hs hs1 ht ht1 hp hpmax e he
  let θ := e/(s+t)
  have hS : 0 < s+t := add_pos hs ht
  have hθ : 0 < θ := div_pos he hS
  have hθS : θ*(s+t) = e := by dsimp [θ]; field_simp
  let ε := min ep (e/4)
  have hε : 0 < ε := lt_min hep (by positivity)
  have hεp : ε ≤ ep := min_le_left _ _
  have hεq : ε ≤ e/4 := min_le_right _ _
  have hεe : ε ≤ e := by linarith
  let d := min τp (min (e/2) τr)
  have hd : 0 < d := lt_min hτp (lt_min (by positivity) hτr)
  obtain ⟨Nc,hNc⟩ := fixed_constant_absorbed (by positivity : 0 < d/2) 3
  refine ⟨ε,d/2,θ,hε,by positivity,hθ,max (max Nr Np) Nc,?_⟩
  intro N hN C hC hCb μ₁ μ₂ ν₁ ν₂ _ _ _ _ hμ₁ hμ₂ hν₁ hν₂ hbμ₁ hbμ₂ hbν₁ hbν₂ ρ _ hfrost hdiam
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hNrp : max Nr Np ≤ N := (le_max_left _ _).trans hN
  have hbudgetp : C ≤ R^ep := hCb.trans (Real.rpow_le_rpow_of_exponent_le hR hεp)
  have hbudgete : C ≤ R^e := hCb.trans (Real.rpow_le_rpow_of_exponent_le hR hεe)
  obtain ⟨H,hH,hroot,hdel,hcap⟩ := hNp N ((le_max_right _ _).trans hNrp) C hC hbudgetp
    μ₁ μ₂ ν₁ ν₂ hμ₁ hμ₂ hν₁ hν₂ hbμ₁ hbμ₂ hbν₁ hbν₂
  let law₁ := parameterProductProbability μ₁ ν₁
  let law₂ := parameterProductProbability μ₂ ν₂
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  obtain ⟨F,hF,hFH,hsep,hdelF,hcapF,hsphere,hcaps⟩ := short_pair_direction_consumer law₁ law₂ H hH
    (by positivity : 0 < R^(-θ)) (parameter_product_full_frostman μ₂ ν₂ hC0 hbμ₂ hbν₂) hcap
  have hnear : C*C*(R^(-θ))^(s+t) ≤ R^(-e/2) := calc
    _ ≤ (R^ε*R^ε)*(R^(-θ))^(s+t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hCb hCb hC0 (by positivity)) (by positivity)
    _ = R^(2*ε-θ*(s+t)) := by
      rw [← Real.rpow_mul hR0.le,← Real.rpow_add hR0,← Real.rpow_add hR0]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by rw [hθS]; linarith)
  have hneq : ∀ z ∈ F, z.1 ≠ z.2 := by
    intro z hz heq
    have hh := hsep z hz
    rw [heq,dist_self] at hh
    exact (not_le_of_gt (by positivity : 0 < R^(-θ))) hh
  obtain ⟨Bad,hBad,hdelBad,hgood⟩ := hNr N ((le_max_left _ _).trans hNrp) C hC hbudgete
    law₁ law₂ F hF hneq hcapF ρ hfrost hdiam
  refine ⟨Bad,hBad,?_,?_⟩
  · have hcost : ((law₁ : Measure (Space 2)).prod law₂) Bad ≤
        ENNReal.ofReal (R^(-τp))+ENNReal.ofReal (R^(-e/2))+ENNReal.ofReal (R^(-τr)) :=
      hdelBad.trans (add_le_add (hdelF.trans (add_le_add hdel (ENNReal.ofReal_le_ofReal hnear))) le_rfl)
    have h₁ := Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_left τp (min (e/2) τr)))
    have h₂ := Real.rpow_le_rpow_of_exponent_le hR (show -e/2 ≤ -d by dsimp [d]; linarith [min_le_right τp (min (e/2) τr),min_le_left (e/2) τr])
    have h₃ := Real.rpow_le_rpow_of_exponent_le hR (show -τr ≤ -d by dsimp [d]; linarith [min_le_right τp (min (e/2) τr),min_le_right (e/2) τr])
    calc
      _ ≤ ENNReal.ofReal (R^(-τp))+ENNReal.ofReal (R^(-e/2))+ENNReal.ofReal (R^(-τr)) := hcost
      _ ≤ ENNReal.ofReal (R^(-d))+ENNReal.ofReal (R^(-d))+ENNReal.ofReal (R^(-d)) :=
        add_le_add (add_le_add (ENNReal.ofReal_le_ofReal h₁) (ENNReal.ofReal_le_ofReal h₂)) (ENNReal.ofReal_le_ofReal h₃)
      _ = ENNReal.ofReal (3*R^(-d)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
      _ ≤ ENNReal.ofReal (R^(d/2)*R^(-d)) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hNc N ((le_max_right _ _).trans hN)) (by positivity))
      _ = _ := by rw [← Real.rpow_add hR0]; congr 1; congr 1; ring
  · intro z hz
    obtain ⟨hzF,hproj⟩ := hgood z hz
    refine ⟨hsep z hzF,?_⟩
    intro G hG
    exact hproj G ((Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg hεe)).trans hG)

#print axioms uniform_product_parameter_normalized_projection
end OAI.Falconer.Regularization
